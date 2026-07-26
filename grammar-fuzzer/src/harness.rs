//! Differential harness: run one generated script through both z3 and oxiz
//! as isolated subprocesses (each killed on timeout) and classify the
//! outcome.
//!
//! We run **both** solvers as subprocesses (rather than calling oxiz
//! in-process the way `bench/z3_parity` does) on purpose: it is robust to any
//! oxiz internal API change, cannot leak panic = "abort" into the harness, and
//! lets a runaway quantifier solve be `SIGKILL`ed cleanly. The trade-off is a
//! couple of process-spawn milliseconds per case, which is negligible next to
//! solve time.

use crate::grammar::{Logic, Script};
use std::io::Write;
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

/// The classification of one solver's raw output.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Verdict {
    Sat,
    Unsat,
    /// Honest "I don't know" (inconclusive; never a discrepancy).
    Unknown,
    /// The solver printed an `(error ...)` or otherwise failed to produce a
    /// check-sat answer (parse error, internal error, nonzero exit).
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
/// `unsat`, `unknown`, or `(error "...")`. We classify conservatively —
/// anything we do not recognise becomes `Error`.
pub fn classify_stdout(raw: &str) -> Verdict {
    // The result line is the first non-empty trimmed line; ignore any
    // leading banner/warnings (both solvers put real output first on stdout,
    // diagnostics on stderr).
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
    /// Raw first-line of stdout (for error reporting).
    pub first_line: String,
    pub elapsed: Duration,
}

/// Run `script` through a solver invoked as `cmd`, feeding the script on
/// stdin, with a hard `timeout`. The child is killed if it exceeds the budget.
fn run_solver(cmd: &[&str], script: &str, timeout: Duration) -> std::io::Result<SolverOutput> {
    let start = Instant::now();
    let mut child = Command::new(cmd[0])
        .args(&cmd[1..])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()?;

    // Feed stdin then drop the handle so the child sees EOF.
    if let Some(mut stdin) = child.stdin.take() {
        let _ = stdin.write_all(script.as_bytes());
    }

    // Poll for completion, killing on timeout. Polling (rather than
    // wait_timeout) keeps this dependency-free and portable.
    let mut killed_for_timeout = false;
    loop {
        match child.try_wait()? {
            Some(_status) => break,
            None => {
                if start.elapsed() >= timeout {
                    let _ = child.kill();
                    let _ = child.wait();
                    killed_for_timeout = true;
                    break;
                }
                std::thread::sleep(Duration::from_millis(10));
            }
        }
    }

    let output = child.wait_with_output()?;
    let elapsed = start.elapsed();

    if killed_for_timeout {
        return Ok(SolverOutput {
            verdict: Verdict::Timeout,
            first_line: "<timeout>".to_string(),
            elapsed,
        });
    }

    let stdout = String::from_utf8_lossy(&output.stdout);
    // A non-zero exit *and* no recognisable output is treated as an error
    // (oxiz exits 1 on parse error but still prints `(error ...)`; z3 exits
    // nonzero on internal failure). Don't downgrade a genuine `sat`/`unsat`
    // that happened to set a nonzero status.
    let verdict = classify_stdout(&stdout);
    let verdict = if verdict == Verdict::Error && !output.stderr.is_empty() {
        // Keep Error, but prefer to surface the stderr-flavoured message.
        verdict
    } else {
        verdict
    };

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

/// The high-level classification of a single differential case.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Outcome {
    /// Both solvers gave the same definite sat/unsat answer.
    Agree,
    /// z3 says sat and oxiz says unsat (or vice-versa) — a soundness bug in
    /// one of the solvers. **The headline discrepancy.**
    SoundnessDisagree,

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
            Outcome::OneError => "OneError",
            Outcome::Inconclusive => "Inconclusive",
            Outcome::Timeout => "Timeout",
            Outcome::BothError => "BothError",
        })
    }
}

/// A full recorded case for reporting.
#[derive(Debug, Clone)]
pub struct Case {
    pub script: Script,
    pub z3: SolverOutput,
    pub oxiz: SolverOutput,
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
            (Sat, Sat) | (Unsat, Unsat) => Outcome::Agree,
            (Sat, Unsat) | (Unsat, Sat) => Outcome::SoundnessDisagree,
            (Error, Error) => Outcome::BothError,
            (Error, Sat) | (Error, Unsat) | (Sat, Error) | (Unsat, Error) => Outcome::OneError,
            (Timeout, _) | (_, Timeout) => Outcome::Timeout,
            // From here at least one side is Unknown, and neither disagrees
            // on sat/unsat nor errored.
            _ => Outcome::Inconclusive,
        }
    }

    /// `true` if this case represents a discrepancy worth investigating
    /// (soundness disagreement, or a one-sided error against a definite
    /// answer). `BothError`, `Timeout`, `Inconclusive`, and plain `Agree` are
    /// not actionable discrepancies.
    pub fn is_discrepancy(&self) -> bool {
        matches!(
            self.outcome(),
            Outcome::SoundnessDisagree | Outcome::OneError
        )
    }
}

/// Run one differential case end-to-end. Returns `None` if either solver
/// binary could not be spawned at all (treated as a harness setup error by the
/// caller rather than a per-case failure).
pub fn run_case(z3: &str, oxiz: &str, script: &Script, timeout: Duration) -> std::io::Result<Case> {
    let z3_out = run_z3(z3, &script.source, timeout)?;
    let oxiz_out = run_oxiz(oxiz, &script.source, timeout)?;
    Ok(Case {
        script: script.clone(),
        z3: z3_out,
        oxiz: oxiz_out,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

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
    fn outcome_soundness_disagree() {
        let mk = |z: Verdict, o: Verdict| Case {
            script: Script {
                logic: Logic::QfLia,
                seed: 0,
                source: String::new(),
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
        };
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
}
