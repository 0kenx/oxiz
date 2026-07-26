//! Differential harness: run one generated script through both z3 and oxiz
//! as isolated subprocesses (each killed on timeout), classify the outcome,
//! and — when oxiz claims `sat` over a scalar-valued logic — validate oxiz's
//! reported model by grounding it and re-checking the conjunction with z3.
//!
//! Both solvers run as subprocesses (rather than calling oxiz in-process the
//! way `bench/z3_parity` does) on purpose: it is robust to any oxiz internal
//! API change, cannot leak `panic = "abort"` into the harness, and lets a
//! runaway quantifier solve be `SIGKILL`ed cleanly.

use crate::grammar::{Logic, Script};
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The classification of one solver's raw output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Verdict {
    Sat,
    Unsat,
    /// Honest "I don't know" (inconclusive; never a discrepancy on its own).
    Unknown,
    /// The solver printed an `(error ...)` or otherwise failed to produce a
    /// check-sat answer (parse error, internal error, nonzero exit, crash).
    Error,
    /// The solver exceeded the per-case wall-clock budget and was killed.
    Timeout,
}

impl std::fmt::Display for Verdict {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Verdict::Sat => "sat",
            Verdict::Unsat => "unsat",
            Verdict::Unknown => "unknown",
            Verdict::Error => "error",
            Verdict::Timeout => "timeout",
        })
    }
}

/// Parse a solver's stdout into a [`Verdict`]. Both z3 (`-in`) and oxiz
/// (`--quiet`, reading stdin) emit exactly one line for `(check-sat)`: `sat`,
/// `unsat`, `unknown`, or `(error "...")`. Anything unrecognised is `Error`.
pub fn classify_stdout(raw: &str) -> Verdict {
    for line in raw.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        return match line {
            "sat" => Verdict::Sat,
            "unsat" => Verdict::Unsat,
            "unknown" => Verdict::Unknown,
            other if other.starts_with("(error") => Verdict::Error,
            _ => Verdict::Error,
        };
    }
    Verdict::Error
}

/// Outcome of running one script through one solver.
#[derive(Debug, Clone)]
pub struct SolverOutput {
    pub verdict: Verdict,
    /// Raw first non-empty line of stdout (for error reporting).
    pub first_line: String,
    pub elapsed: Duration,
}

/// Result of validating a solver's `sat` model by grounding it and re-checking
/// with the *other* (trusted) solver.
#[derive(Debug, Clone)]
pub enum ModelCheck {
    /// The logic does not produce scalar models (arrays / uninterpreted), or
    /// the solver did not report `sat`.
    NotApplicable,
    /// The grounded model was confirmed consistent with the assertions.
    Valid,
    /// The grounded model contradicts the assertions (or is not even a
    /// well-formed term) — a soundness bug in the solver that produced it.
    Invalid(String),
    /// The checker could not decide (unknown/timeout) or the model could not
    /// be parsed/exctracted.
    Inconclusive,
}

/// The high-level classification of a single differential case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// Both solvers gave the same definite sat/unsat answer (and any sat model
    /// checked out, when applicable).
    Agree,
    /// z3 says sat and oxiz says unsat (or vice-versa) — a soundness bug in
    /// one of the solvers. **The headline discrepancy.**
    SoundnessDisagree,
    /// oxiz reported `sat` but its model, when grounded and re-checked with
    /// z3, contradicts the assertions (or is malformed) — a model-soundness
    /// bug in oxiz.
    InvalidModel,
    /// One solver produced a definite answer; the other errored (parse error
    /// or internal failure). Could be a real parser bug or a feature gap.
    OneError,
    /// At least one side returned `unknown` (and neither disagrees on
    /// sat/unsat) — inconclusive, not counted as a discrepancy.
    Inconclusive,
    /// At least one side timed out (and neither disagrees / errored).
    Timeout,
    /// Both errored — the script is probably malformed (shouldn't happen with
    /// the grammar generator, but harmless if it does).
    BothError,
}

impl std::fmt::Display for Outcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Outcome::Agree => "Agree",
            Outcome::SoundnessDisagree => "SoundnessDisagree",
            Outcome::InvalidModel => "InvalidModel",
            Outcome::OneError => "OneError",
            Outcome::Inconclusive => "Inconclusive",
            Outcome::Timeout => "Timeout",
            Outcome::BothError => "BothError",
        })
    }
}

/// Run `cmd[0] cmd[1..]`, feed `script` on stdin, return `(stdout, killed)`.
fn run_collect(cmd: &[&str], script: &str, timeout: Duration) -> std::io::Result<(String, bool)> {
    let start = Instant::now();
    let mut child = Command::new(cmd[0])
        .args(&cmd[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(script.as_bytes());
    }

    let mut killed = false;
    loop {
        match child.try_wait()? {
            Some(_status) => break,
            None => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    killed = true;
                    break;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }

    let output = child.wait_with_output()?;
    Ok((String::from_utf8_lossy(&output.stdout).to_string(), killed))
}

/// Run a solver, classify stdout, record timing.
fn run_solver(cmd: &[&str], script: &str, timeout: Duration) -> std::io::Result<SolverOutput> {
    let start = Instant::now();
    let (stdout, killed) = run_collect(cmd, script, timeout)?;
    let elapsed = start.elapsed();

    if killed {
        return Ok(SolverOutput {
            verdict: Verdict::Timeout,
            first_line: "<timeout>".to_string(),
            elapsed,
        });
    }

    let verdict = classify_stdout(&stdout);
    let first_line = stdout
        .lines()
        .map(str::trim)
        .find(|l| !l.is_empty())
        .unwrap_or("")
        .to_string();
    Ok(SolverOutput {
        verdict,
        first_line,
        elapsed,
    })
}

/// Run `script` through z3 (`z3 -in`).
pub fn run_z3(z3: &str, script: &str, timeout: Duration) -> std::io::Result<SolverOutput> {
    run_solver(&[z3, "-in"], script, timeout)
}

/// Run `script` through oxiz (`oxiz --quiet`, reading stdin).
pub fn run_oxiz(oxiz: &str, script: &str, timeout: Duration) -> std::io::Result<SolverOutput> {
    run_solver(&[oxiz, "--quiet"], script, timeout)
}

// ---------------------------------------------------------------------
// Model-validity oracle
// ---------------------------------------------------------------------

/// Build a copy of `source` with a `(get-value (vars...))` query inserted
/// after the existing `(check-sat)` (and before `(exit)`).
fn with_get_value(source: &str, vars: &[String]) -> String {
    let trimmed = source.trim_end();
    let body = trimmed
        .strip_suffix("(exit)")
        .map(str::trim_end)
        .unwrap_or(trimmed);
    format!("{body}\n(get-value ({}))\n(exit)\n", vars.join(" "))
}

/// Parse a `((x v0) (y v1) ...)` get-value line into `(var, value)` pairs.
/// Tolerates values containing spaces (e.g. `(- 5)`). Returns `None` if no
/// recognisable model line is present.
fn parse_get_value(stdout: &str) -> Option<Vec<(String, String)>> {
    let line = stdout
        .lines()
        .map(str::trim)
        .find(|l| l.starts_with("((") && l.ends_with(')'))?;
    // Strip exactly one outer paren pair to get the list of binding groups.
    let inner = line.strip_prefix('(')?.strip_suffix(')')?;
    let mut out = Vec::new();
    for group in split_top_sexprs(inner) {
        if let Some(p) = parse_binding(&group) {
            out.push(p);
        }
    }
    Some(out)
}

/// Split `s` into its top-level s-expressions (balanced-paren groups),
/// ignoring whitespace that separates them.
fn split_top_sexprs(s: &str) -> Vec<String> {
    let mut groups = Vec::new();
    let mut depth = 0i32;
    let mut cur = String::new();
    for ch in s.chars() {
        match ch {
            '(' => {
                depth += 1;
                cur.push(ch);
            }
            ')' => {
                depth -= 1;
                cur.push(ch);
            }
            ws if depth == 0 && ws.is_whitespace() => {
                let g = std::mem::take(&mut cur);
                let g = g.trim().to_string();
                if !g.is_empty() {
                    groups.push(g);
                }
            }
            c => cur.push(c),
        }
    }
    let g = cur.trim().to_string();
    if !g.is_empty() {
        groups.push(g);
    }
    groups
}

fn parse_binding(group: &str) -> Option<(String, String)> {
    // Each group is `(name value...)`; strip exactly one outer paren pair.
    let body = group.trim().strip_prefix('(')?.strip_suffix(')')?;
    let mut it = body.splitn(2, char::is_whitespace);
    let name = it.next()?.trim().to_string();
    let val = it.collect::<Vec<_>>().join(" ").trim().to_string();
    if name.is_empty() || val.is_empty() {
        return None;
    }
    Some((name, val))
}

/// Build a check script: original declarations + original assertions + the
/// model pinned down as extra equalities, then `(check-sat)`. A solver that
/// agrees the model satisfies the formula returns `sat`; `unsat` means the
/// model contradicts an assertion.
fn grounding_script(source: &str, assignment: &[(String, String)]) -> String {
    let preamble: Vec<&str> = source
        .lines()
        .filter(|l| {
            let t = l.trim();
            !t.starts_with("(check-sat)") && !t.starts_with("(exit)")
        })
        .collect();
    let conj: Vec<String> = assignment
        .iter()
        .map(|(v, c)| format!("(= {v} {c})"))
        .collect();
    let model_assert = if conj.len() == 1 {
        format!("(assert {})", conj[0])
    } else {
        format!("(assert (and {}))", conj.join(" "))
    };
    format!(
        "{}\n{model_assert}\n(check-sat)\n(exit)\n",
        preamble.join("\n")
    )
}

/// Validate oxiz's `sat` model using z3 as the trusted checker. Runs oxiz
/// again with a `get-value` query, grounds the returned assignment against the
/// original assertions, and asks z3 whether that conjunction is satisfiable.
pub fn validate_model(z3: &str, oxiz: &str, script: &Script, timeout: Duration) -> ModelCheck {
    let gv = with_get_value(&script.source, &script.vars);
    let (oxiz_stdout, killed) = match run_collect(&[oxiz, "--quiet"], &gv, timeout) {
        Ok(x) => x,
        Err(_) => return ModelCheck::Inconclusive,
    };
    if killed {
        return ModelCheck::Inconclusive;
    }
    let assignment = match parse_get_value(&oxiz_stdout) {
        Some(a) if !a.is_empty() => a,
        _ => return ModelCheck::Inconclusive,
    };

    let ground = grounding_script(&script.source, &assignment);
    let (z3_stdout, killed) = match run_collect(&[z3, "-in"], &ground, timeout) {
        Ok(x) => x,
        Err(_) => return ModelCheck::Inconclusive,
    };
    if killed {
        return ModelCheck::Inconclusive;
    }
    match classify_stdout(&z3_stdout) {
        Verdict::Sat => ModelCheck::Valid,
        Verdict::Unsat => ModelCheck::Invalid(format!(
            "oxiz sat-model contradicts assertions; z3 says the grounded model is unsat. model={assignment:?}"
        )),
        // z3 rejecting the model tokens (e.g. oxiz's malformed `#x-1`) parses
        // as an error -> the model is not even well-formed.
        Verdict::Error => ModelCheck::Invalid(format!(
            "oxiz sat-model is not a well-formed value z3 can parse. model={assignment:?}"
        )),
        _ => ModelCheck::Inconclusive,
    }
}

// ---------------------------------------------------------------------
// Case + outcome
// ---------------------------------------------------------------------

/// A full recorded case for reporting.
#[derive(Debug, Clone)]
pub struct Case {
    pub script: Script,
    pub z3: SolverOutput,
    pub oxiz: SolverOutput,
    pub model: ModelCheck,
}

impl Case {
    pub fn logic(&self) -> Logic {
        self.script.logic
    }
    pub fn seed(&self) -> u64 {
        self.script.seed
    }

    /// Classify this case into a high-level [`Outcome`].
    pub fn outcome(&self) -> Outcome {
        let (z, o) = (self.z3.verdict, self.oxiz.verdict);
        use Verdict::*;
        match (z, o) {
            (Sat, Unsat) | (Unsat, Sat) => Outcome::SoundnessDisagree,
            (Error, Error) => Outcome::BothError,
            (Error, Sat) | (Error, Unsat) | (Sat, Error) | (Unsat, Error) => Outcome::OneError,
            (Timeout, _) | (_, Timeout) => Outcome::Timeout,
            // From here neither disagrees on sat/unsat nor errored.
            _ => {
                if matches!(self.model, ModelCheck::Invalid(_)) {
                    Outcome::InvalidModel
                } else if (z == Sat && o == Sat) || (z == Unsat && o == Unsat) {
                    Outcome::Agree
                } else {
                    Outcome::Inconclusive
                }
            }
        }
    }

    /// `true` if this case is an actionable discrepancy.
    pub fn is_discrepancy(&self) -> bool {
        matches!(
            self.outcome(),
            Outcome::SoundnessDisagree | Outcome::OneError | Outcome::InvalidModel
        )
    }
}

/// Run one differential case end-to-end (parity +, where applicable,
/// model-validation).
pub fn run_case(z3: &str, oxiz: &str, script: &Script, timeout: Duration) -> std::io::Result<Case> {
    let z3_out = run_z3(z3, &script.source, timeout)?;
    let oxiz_out = run_oxiz(oxiz, &script.source, timeout)?;

    // Only validate oxiz's model when it claimed `sat` over a logic whose
    // models are concrete scalar values, and we actually know the var names.
    let model = if oxiz_out.verdict == Verdict::Sat
        && script.logic.has_scalar_models()
        && !script.vars.is_empty()
    {
        validate_model(z3, oxiz, script, timeout)
    } else {
        ModelCheck::NotApplicable
    };

    Ok(Case {
        script: script.clone(),
        z3: z3_out,
        oxiz: oxiz_out,
        model,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mk(z: Verdict, o: Verdict) -> Case {
        Case {
            script: Script {
                logic: Logic::QfLia,
                seed: 0,
                source: String::new(),
                vars: vec!["x0".into()],
            },
            z3: SolverOutput {
                verdict: z,
                first_line: String::new(),
                elapsed: Duration::ZERO,
            },
            oxiz: SolverOutput {
                verdict: o,
                first_line: String::new(),
                elapsed: Duration::ZERO,
            },
            model: ModelCheck::NotApplicable,
        }
    }

    #[test]
    fn classify_basic() {
        assert_eq!(classify_stdout("sat\n"), Verdict::Sat);
        assert_eq!(classify_stdout("unsat\n"), Verdict::Unsat);
        assert_eq!(classify_stdout("unknown\n"), Verdict::Unknown);
        assert_eq!(classify_stdout("(error \"nope\")\n"), Verdict::Error);
        assert_eq!(classify_stdout("\n  \n"), Verdict::Error);
        assert_eq!(classify_stdout("sat"), Verdict::Sat);
    }

    #[test]
    fn classify_ignores_leading_blank_lines() {
        assert_eq!(classify_stdout("\n\nunsat\n"), Verdict::Unsat);
    }

    #[test]
    fn outcome_table() {
        assert_eq!(mk(Verdict::Sat, Verdict::Sat).outcome(), Outcome::Agree);
        assert_eq!(
            mk(Verdict::Unsat, Verdict::Sat).outcome(),
            Outcome::SoundnessDisagree
        );
        assert_eq!(
            mk(Verdict::Sat, Verdict::Error).outcome(),
            Outcome::OneError
        );
        assert_eq!(
            mk(Verdict::Unknown, Verdict::Sat).outcome(),
            Outcome::Inconclusive
        );
        assert!(mk(Verdict::Sat, Verdict::Unsat).is_discrepancy());
        assert!(!mk(Verdict::Unknown, Verdict::Sat).is_discrepancy());
    }

    #[test]
    fn invalid_model_is_a_discrepancy() {
        let mut c = mk(Verdict::Sat, Verdict::Sat);
        c.model = ModelCheck::Invalid("bogus".into());
        assert_eq!(c.outcome(), Outcome::InvalidModel);
        assert!(c.is_discrepancy());
    }

    #[test]
    fn parse_get_value_simple() {
        let s = "sat\n((x #b01) (y 5))\n";
        let v = parse_get_value(s).unwrap();
        assert_eq!(
            v,
            vec![("x".into(), "#b01".into()), ("y".into(), "5".into())]
        );
    }

    #[test]
    fn parse_get_value_negative_and_single() {
        assert_eq!(
            parse_get_value("((x (- 5)))").unwrap(),
            vec![("x".into(), "(- 5)".into())]
        );
        assert_eq!(
            parse_get_value("((p \"ab\"))").unwrap(),
            vec![("p".into(), "\"ab\"".into())]
        );
    }

    #[test]
    fn grounding_pins_assignment() {
        let src =
            "(set-logic QF_LIA)\n(declare-const x Int)\n(assert (> x 0))\n(check-sat)\n(exit)\n";
        let g = grounding_script(src, &[("x".into(), "5".into())]);
        assert!(g.contains("(declare-const x Int)"));
        assert!(g.contains("(assert (> x 0))"));
        assert!(g.contains("(assert (= x 5))"));
        assert!(g.contains("(check-sat)"));
        assert!(!g.contains("(get-value"));
    }
}
