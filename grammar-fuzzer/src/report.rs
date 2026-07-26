//! Markdown + console reporting for a fuzz run.

use crate::Args;
use crate::grammar::Logic;
use crate::harness::{Case, Outcome};
use std::collections::HashMap;
use std::fmt::Write as _;

/// Per-logic tally of every outcome bucket. `total` is the sum of the buckets
/// actually observed (so a skipped/harness-errored case is reflected honestly
/// rather than padded out to `iterations`).
struct LogicStats {
    logic: String,
    total: u64,
    agree: u64,
    soundness: u64,
    invalid_model: u64,
    one_error: u64,
    inconclusive: u64,
    timeout: u64,
    both_error: u64,
}

fn aggregate(counts: &HashMap<String, u64>, logics: &[Logic]) -> Vec<LogicStats> {
    logics
        .iter()
        .map(|logic| {
            let key = |o: &str| format!("{logic}/{o}");
            let get = |o: &str| *counts.get(&key(o)).unwrap_or(&0);
            let mut s = LogicStats {
                logic: logic.name().to_string(),
                total: 0,
                agree: get("Agree"),
                soundness: get("SoundnessDisagree"),
                invalid_model: get("InvalidModel"),
                one_error: get("OneError"),
                inconclusive: get("Inconclusive"),
                timeout: get("Timeout"),
                both_error: get("BothError"),
            };
            s.total = s.agree
                + s.soundness
                + s.invalid_model
                + s.one_error
                + s.inconclusive
                + s.timeout
                + s.both_error;
            s
        })
        .collect()
}

/// Build the full markdown report.
pub fn build_report(args: &Args, counts: &HashMap<String, u64>, discrepancies: &[Case]) -> String {
    let stats = aggregate(counts, &args.logics);

    let mut w = String::new();
    let _ = writeln!(w, "# oxiz-grammar-fuzzer report");
    let _ = writeln!(w);
    let _ = writeln!(w, "- **oxiz:** `{}`", args.oxiz);
    let _ = writeln!(w, "- **z3:** `{}`", args.z3);
    let _ = writeln!(
        w,
        "- **config:** iterations={}/logic, base_seed={}, timeout={}s, max_depth={}, max_vars={}, max_asserts={}",
        args.iterations,
        args.base_seed,
        args.timeout_secs,
        args.config.max_term_depth,
        args.config.max_vars,
        args.config.max_asserts
    );
    let _ = writeln!(w, "- **date:** {}", rfc3339_local());
    let _ = writeln!(w);

    let _ = writeln!(w, "## Per-logic outcome summary");
    let _ = writeln!(w);
    let _ = writeln!(
        w,
        "| logic | total | agree | soundness | invalid-model | one-error | inconclusive | timeout | both-error |"
    );
    let _ = writeln!(
        w,
        "|-------|-------|-------|-----------|---------------|-----------|--------------|---------|------------|"
    );
    for s in &stats {
        let _ = writeln!(
            w,
            "| {} | {} | {} | **{}** | **{}** | {} | {} | {} | {} |",
            s.logic,
            s.total,
            s.agree,
            s.soundness,
            s.invalid_model,
            s.one_error,
            s.inconclusive,
            s.timeout,
            s.both_error
        );
    }
    let _ = writeln!(w);

    let total_soundness: u64 = stats.iter().map(|s| s.soundness).sum();
    let total_invalid: u64 = stats.iter().map(|s| s.invalid_model).sum();
    let total_one_error: u64 = stats.iter().map(|s| s.one_error).sum();
    let total: u64 = stats.iter().map(|s| s.total).sum();

    let _ = writeln!(w, "## Headline");
    let _ = writeln!(w);
    if total_soundness == 0 {
        let _ = writeln!(
            w,
            "**No sat/unsat soundness discrepancies** were found across {total} cases."
        );
    } else {
        let _ = writeln!(
            w,
            "**{total_soundness} soundness (sat/unsat) discrepancy(ies)** found — z3 and oxiz \
             disagree on satisfiability (a bug in one of the two solvers)."
        );
    }
    if total_invalid > 0 {
        let _ = writeln!(
            w,
            "**{total_invalid} invalid-model discrepancy(ies)** found — oxiz reported `sat` but \
             its model, when grounded and re-checked by z3, contradicts the assertions (or is \
             not even a well-formed value). Distinct from a sat/unsat disagreement: oxiz got the \
             verdict right but cannot back it with a real model."
        );
    }
    if total_one_error > 0 {
        let _ = writeln!(
            w,
            "{total_one_error} one-sided error(s) (one solver answered sat/unsat, the other \
             errored) — potential parser/crash bugs, listed last."
        );
    }
    let _ = writeln!(w);

    let mut soundness_cases: Vec<&Case> = discrepancies
        .iter()
        .filter(|c| matches!(c.outcome(), Outcome::SoundnessDisagree))
        .collect();
    let mut invalid_cases: Vec<&Case> = discrepancies
        .iter()
        .filter(|c| matches!(c.outcome(), Outcome::InvalidModel))
        .collect();
    let mut error_cases: Vec<&Case> = discrepancies
        .iter()
        .filter(|c| matches!(c.outcome(), Outcome::OneError))
        .collect();
    soundness_cases.sort_by_key(|c| (c.logic().name(), c.seed()));
    invalid_cases.sort_by_key(|c| (c.logic().name(), c.seed()));
    error_cases.sort_by_key(|c| (c.logic().name(), c.seed()));

    if !soundness_cases.is_empty() {
        let _ = writeln!(w, "## Soundness discrepancies (sat/unsat disagreement)");
        let _ = writeln!(w);
        for (i, c) in soundness_cases.iter().enumerate() {
            write_case(&mut w, i + 1, c);
        }
    }
    if !invalid_cases.is_empty() {
        let _ = writeln!(
            w,
            "## Invalid-model discrepancies (oxiz `sat`, bogus model)"
        );
        let _ = writeln!(w);
        for (i, c) in invalid_cases.iter().enumerate() {
            write_case(&mut w, i + 1, c);
        }
    }
    if !error_cases.is_empty() {
        let _ = writeln!(w, "## One-sided errors (potential parser/feature gaps)");
        let _ = writeln!(w);
        for (i, c) in error_cases.iter().enumerate() {
            write_case(&mut w, i + 1, c);
        }
    }

    let _ = writeln!(w);
    let _ = writeln!(
        w,
        "## Reproducing\n\nEvery case above is a pure function of `(logic, seed)`. The reproducer \
         is saved next to this report at `discrepancies/seed-<LOGIC>-<SEED>.smt2` and can be run \
         directly:\n\n```bash\nz3 -in < discrepancies/seed-<LOGIC>-<SEED>.smt2\n<path-to-oxiz> \
         --quiet < discrepancies/seed-<LOGIC>-<SEED>.smt2\n```"
    );
    w
}

fn write_case(w: &mut String, idx: usize, c: &Case) {
    let why = match c.outcome() {
        Outcome::InvalidModel => match &c.model {
            crate::harness::ModelCheck::Invalid(msg) => format!("invalid model: {msg}"),
            _ => "invalid model".to_string(),
        },
        _ => format!(
            "z3={}/{:?}  oxiz={}/{:?}",
            c.z3.verdict, c.z3.first_line, c.oxiz.verdict, c.oxiz.first_line
        ),
    };
    let _ = writeln!(
        w,
        "### {idx}. `{}` seed `{}` [{:?}] — {}",
        c.logic().name(),
        c.seed(),
        c.outcome(),
        why
    );
    let _ = writeln!(
        w,
        "reproducer: `discrepancies/seed-{}-{}.smt2` ({} z3, {} oxiz)",
        c.logic().name(),
        c.seed(),
        fmt_dur(c.z3.elapsed),
        fmt_dur(c.oxiz.elapsed)
    );
    let _ = writeln!(w, "```smt2");
    let _ = w.write_str(&c.script.source);
    if !c.script.source.ends_with('\n') {
        w.push('\n');
    }
    let _ = writeln!(w, "```");
    let _ = writeln!(w);
}

/// Compact one-screen console summary.
pub fn summary_table(args: &Args, counts: &HashMap<String, u64>, discrepancies: &[Case]) -> String {
    let stats = aggregate(counts, &args.logics);
    let total: u64 = stats.iter().map(|s| s.total).sum();
    let total_soundness: u64 = stats.iter().map(|s| s.soundness).sum();
    let total_invalid: u64 = stats.iter().map(|s| s.invalid_model).sum();
    let total_one_error: u64 = stats.iter().map(|s| s.one_error).sum();
    let total_agree: u64 = stats.iter().map(|s| s.agree).sum();

    let mut w = String::new();
    let _ = writeln!(w, "=== summary ({total} cases) ===");
    for s in &stats {
        let flag = if s.soundness > 0 {
            "  <-- SOUNDNESS"
        } else if s.invalid_model > 0 {
            "  <-- INVALID-MODEL"
        } else {
            ""
        };
        let _ = writeln!(
            w,
            "  {:8} total={:<5} agree={:<5} sound={:<3} invmodel={:<3} one-err={:<3} inconcl={:<4} timeout={:<3} both-err={:<3}{}",
            s.logic,
            s.total,
            s.agree,
            s.soundness,
            s.invalid_model,
            s.one_error,
            s.inconclusive,
            s.timeout,
            s.both_error,
            flag
        );
    }
    let _ = writeln!(
        w,
        "  -------------------------------------------------------------------------------------------"
    );
    let _ = writeln!(
        w,
        "  {:8} total={:<5} agree={:<5} sound={:<3} invmodel={:<3} one-err={:<3}",
        "TOTAL", total, total_agree, total_soundness, total_invalid, total_one_error
    );
    if !discrepancies.is_empty() {
        let _ = writeln!(w);
        let _ = writeln!(w, "discrepancies (first {}):", discrepancies.len().min(15));
        for c in discrepancies.iter().take(15) {
            let extra = match &c.model {
                crate::harness::ModelCheck::Invalid(_) => " [invalid model]",
                _ => "",
            };
            let _ = writeln!(
                w,
                "  {:8} seed={:<6} {:<18} z3={} oxiz={}{}",
                c.logic().name(),
                c.seed(),
                format!("{:?}", c.outcome()),
                c.z3.verdict,
                c.oxiz.verdict,
                extra
            );
        }
        if discrepancies.len() > 15 {
            let _ = writeln!(
                w,
                "  ... and {} more (see report.md)",
                discrepancies.len() - 15
            );
        }
    }
    w
}

fn fmt_dur(d: std::time::Duration) -> String {
    let ms = d.as_millis();
    if ms < 1000 {
        format!("{ms}ms")
    } else {
        format!("{:.2}s", d.as_secs_f64())
    }
}

/// Best-effort local timestamp (no chrono dep): shell out to `date`.
fn rfc3339_local() -> String {
    match std::process::Command::new("date")
        .arg("+%Y-%m-%dT%H:%M:%S%:z")
        .output()
    {
        Ok(o) if o.status.success() => String::from_utf8_lossy(&o.stdout).trim().to_string(),
        _ => "unknown".to_string(),
    }
}
