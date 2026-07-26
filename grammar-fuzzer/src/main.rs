//! `oxiz-grammar-fuzzer` — grammar-driven differential fuzzer for z3 vs oxiz.
//!
//! Generates well-typed SMT-LIB2 scripts from a fixed grammar, runs each
//! through both `z3` and the `oxiz` CLI as subprocesses (killed on timeout),
//! and reports every discrepancy. The headline discrepancy class is a
//! **sat/unsat disagreement** (a genuine soundness bug in one of the solvers);
//! one-sided errors (one solver answers, the other errors) are reported
//! separately as potential parser/feature gaps.
//!
//! See [`grammar`] for the supported logics and [`harness`] for the oracle.
//!
//! # Quick start
//!
//! ```text
//! # build oxiz first (the harness shells out to it)
//! cargo build --release -p oxiz-cli
//! # then run the fuzzer (it is not in default-members, so name it explicitly)
//! cargo run --release -p oxiz-grammar-fuzzer -- --iterations 5000
//! ```
//!
//! Every generated case is a pure function of `(logic, seed)`, so any reported
//! discrepancy is reproducible from its seed.

mod grammar;
mod harness;
mod report;
mod rng;

use grammar::{Config, Logic, Script, generate};
use harness::{Case, run_case};
use std::collections::HashMap;
use std::path::PathBuf;
use std::process::ExitCode;
use std::time::Duration;

/// Parsed command-line arguments.
struct Args {
    iterations: usize,
    logics: Vec<Logic>,
    base_seed: u64,
    timeout_secs: u64,
    oxiz: String,
    z3: String,
    outdir: PathBuf,
    save_all: bool,
    config: Config,
}

const HELP: &str = "\
oxiz-grammar-fuzzer — grammar-driven differential fuzzer (z3 vs oxiz)

USAGE:
    oxiz-grammar-fuzzer [OPTIONS]

OPTIONS:
        --iterations N        Cases to generate per logic [default: 1000]
        --logics LIST         Comma-separated logics [default: all]
                              (QF_LIA,QF_LRA,QF_BV,QF_UF,LIA)
        --base-seed N         Starting seed [default: 0]
        --timeout SECS        Per-case wall-clock budget [default: 10]
        --oxiz PATH           oxiz binary [default: target/release/oxiz, then PATH]
        --z3 PATH             z3 binary [default: z3]
        --outdir DIR          Report output directory [default: grammar-fuzz-report]
        --save-all            Dump every generated script to <outdir>/corpus/
        --max-depth N         Formula/term recursion depth [default: 3]
        --max-vars N          Max declared vars per script [default: 5]
        --max-asserts N       Max assertions per script [default: 6]
    -h, --help                Show this help

A discrepancy report is written to <outdir>/report.md and each discrepancy's
reproducing script to <outdir>/discrepancies/seed-<logic>-<seed>.smt2.
Exit code is 1 if any soundness (sat/unsat) discrepancy is found, else 0.
";

fn parse_args(argv: &[String]) -> Result<Args, String> {
    let mut iterations: usize = 1000;
    let mut logics: Vec<Logic> = Logic::ALL.to_vec();
    let mut base_seed: u64 = 0;
    let mut timeout_secs: u64 = 10;
    let mut oxiz: Option<String> = None;
    let mut z3 = "z3".to_string();
    let mut outdir = PathBuf::from("grammar-fuzz-report");
    let mut save_all = false;
    let mut max_depth: u32 = 3;
    let mut max_vars: usize = 5;
    let mut max_asserts: usize = 6;

    let mut i = 0;
    while i < argv.len() {
        let a = &argv[i];
        let take_val = |i: &mut usize| -> Result<String, String> {
            *i += 1;
            argv.get(*i)
                .cloned()
                .ok_or_else(|| format!("missing value for {a}"))
        };
        match a.as_str() {
            "-h" | "--help" => {
                println!("{HELP}");
                std::process::exit(0);
            }
            "--iterations" => iterations = parse_usize(&take_val(&mut i)?)?,
            "--logics" => {
                logics = Logic::parse_list(&take_val(&mut i)?)
                    .ok_or_else(|| "invalid --logics value".to_string())?;
            }
            "--base-seed" => base_seed = parse_u64(&take_val(&mut i)?)?,
            "--timeout" => timeout_secs = parse_u64(&take_val(&mut i)?)?,
            "--oxiz" => oxiz = Some(take_val(&mut i)?),
            "--z3" => z3 = take_val(&mut i)?,
            "--outdir" => outdir = PathBuf::from(take_val(&mut i)?),
            "--save-all" => save_all = true,
            "--max-depth" => max_depth = parse_u32(&take_val(&mut i)?)?,
            "--max-vars" => max_vars = parse_usize(&take_val(&mut i)?)?,
            "--max-asserts" => max_asserts = parse_usize(&take_val(&mut i)?)?,
            other => return Err(format!("unknown argument: {other} (try --help)")),
        }
        i += 1;
    }

    Ok(Args {
        iterations,
        logics,
        base_seed,
        timeout_secs,
        oxiz: oxiz.unwrap_or_else(default_oxiz_path),
        z3,
        outdir,
        save_all,
        config: Config {
            max_term_depth: max_depth,
            max_formula_depth: max_depth,
            min_vars: 2,
            max_vars: max_vars.max(1),
            min_asserts: 2,
            max_asserts: max_asserts.max(1),
        },
    })
}

fn parse_usize(s: &str) -> Result<usize, String> {
    s.parse()
        .map_err(|_| format!("not a non-negative integer: {s:?}"))
}
fn parse_u64(s: &str) -> Result<u64, String> {
    s.parse().map_err(|_| format!("not a u64: {s:?}"))
}
fn parse_u32(s: &str) -> Result<u32, String> {
    s.parse().map_err(|_| format!("not a u32: {s:?}"))
}

/// Locate the oxiz binary: prefer a freshly built `target/release/oxiz` in the
/// current workspace, then fall back to whatever is on `PATH`.
fn default_oxiz_path() -> String {
    for cand in ["target/release/oxiz", "../target/release/oxiz"] {
        if std::path::Path::new(cand).exists() {
            return cand.to_string();
        }
    }
    "oxiz".to_string()
}

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let args = match parse_args(&argv) {
        Ok(a) => a,
        Err(e) => {
            eprintln!("error: {e}");
            eprintln!("\n{HELP}");
            return ExitCode::from(2);
        }
    };

    eprintln!("oxiz-grammar-fuzzer");
    eprintln!("  logics:     {}", fmt_logics(&args.logics));
    eprintln!(
        "  iterations: {} per logic ({} total)",
        args.iterations,
        args.iterations * args.logics.len()
    );
    eprintln!("  oxiz:       {}", args.oxiz);
    eprintln!("  z3:         {}", args.z3);
    eprintln!("  timeout:    {}s/case", args.timeout_secs);
    eprintln!("  outdir:     {}", args.outdir.display());

    // Sanity-check both solver binaries are spawnable up front so we fail
    // fast with a clear message instead of 1000 "Error" verdicts.
    if let Err(e) = check_binary(&args.oxiz, &["--help"]) {
        eprintln!("error: cannot run oxiz binary {:?}: {e}", args.oxiz);
        eprintln!("       build it with: cargo build --release -p oxiz-cli");
        return ExitCode::from(2);
    }
    if let Err(e) = check_binary(&args.z3, &["--version"]) {
        eprintln!("error: cannot run z3 binary {:?}: {e}", args.z3);
        return ExitCode::from(2);
    }

    // Prepare output dirs.
    let _ = std::fs::create_dir_all(&args.outdir);
    let disc_dir = args.outdir.join("discrepancies");
    let corpus_dir = args.outdir.join("corpus");
    let _ = std::fs::create_dir_all(&disc_dir);
    if args.save_all {
        let _ = std::fs::create_dir_all(&corpus_dir);
    }

    let timeout = Duration::from_secs(args.timeout_secs);
    let mut cases: Vec<Case> = Vec::with_capacity(args.iterations * args.logics.len());
    let mut counts: HashMap<String, u64> = HashMap::new();

    let total = args.iterations * args.logics.len();
    let mut done = 0usize;

    // Derive a per-logic seed stream so independent logics don't replay
    // correlated sequences.
    for (li, logic) in args.logics.iter().enumerate() {
        for j in 0..args.iterations {
            let seed = args
                .base_seed
                .wrapping_add((li as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15))
                .wrapping_add(j as u64);
            let script: Script = generate(*logic, seed, &args.config);

            if args.save_all {
                let p = corpus_dir.join(format!("seed-{}-{seed}.smt2", logic.name()));
                let _ = std::fs::write(&p, &script.source);
            }

            let case = match run_case(&args.z3, &args.oxiz, &script, timeout) {
                Ok(c) => c,
                Err(e) => {
                    eprintln!("warning: harness error on {logic}/{seed}: {e}");
                    continue;
                }
            };

            *counts.entry(format!("{}", case.outcome())).or_insert(0) += 1;
            // Also tally per-logic agrees/discrepancies for the report.
            *counts
                .entry(format!("{logic}/{}", case.outcome()))
                .or_insert(0) += 1;

            if case.is_discrepancy() {
                // Persist the reproducer immediately so a crash mid-run never
                // loses it.
                let p = disc_dir.join(format!("seed-{}-{seed}.smt2", logic.name()));
                let header = format!(
                    "; DISCREPANCY  logic={logic}  seed={seed}\n\
                     ; z3={}  oxiz={}\n\
                     ; z3-out={:?}  oxiz-out={:?}\n",
                    case.z3.verdict, case.oxiz.verdict, case.z3.first_line, case.oxiz.first_line
                );
                let _ = std::fs::write(&p, format!("{header}{}", script.source));
                cases.push(case);
            }

            done += 1;
            if done.is_multiple_of(25) || done == total {
                eprint!("\r  progress: {done}/{total} cases ");
                let _ = std::io::Write::flush(&mut std::io::stderr());
            }
        }
    }
    eprintln!();

    // Build the report.
    let report = report::build_report(&args, &counts, &cases);
    let report_path = args.outdir.join("report.md");
    if let Err(e) = std::fs::write(&report_path, &report) {
        eprintln!("warning: could not write {}: {e}", report_path.display());
    }

    // Echo a concise summary to stderr.
    eprintln!();
    eprintln!("{}", report::summary_table(&args, &counts, &cases));

    let soundness = cases
        .iter()
        .filter(|c| matches!(c.outcome(), harness::Outcome::SoundnessDisagree))
        .count();

    eprintln!("report written to {}", report_path.display());
    if !cases.is_empty() {
        eprintln!(
            "{} discrepancy reproducers in {}",
            cases.len(),
            disc_dir.display()
        );
    }

    if soundness > 0 {
        eprintln!("FAIL: {soundness} soundness (sat/unsat) discrepancies found");
        ExitCode::from(1)
    } else {
        ExitCode::from(0)
    }
}

fn fmt_logics(logics: &[Logic]) -> String {
    logics
        .iter()
        .map(|l| l.name())
        .collect::<Vec<_>>()
        .join(",")
}

/// Spawn `bin args`, wait for it to exit; only errors (binary not found, etc.)
/// are propagated — a nonzero exit is fine.
fn check_binary(bin: &str, args: &[&str]) -> std::io::Result<()> {
    std::process::Command::new(bin)
        .args(args)
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .stdin(Stdio::null())
        .status()?;
    Ok(())
}

// re-export for the closure above
use std::process::Stdio;
