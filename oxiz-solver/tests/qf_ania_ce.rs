//! QF_ANIA fixtures: nonlinear products over array `select` terms.
use oxiz_solver::{Context, SolverResult};
use std::path::{Path, PathBuf};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../bench/qf_ania_ce")
}

fn run_smt2(path: &Path) -> SolverResult {
    let source = std::fs::read_to_string(path).unwrap();
    let mut ctx = Context::new();
    match ctx.execute_script(&source) {
        Ok(outputs) => {
            for line in outputs.iter().rev() {
                match line.trim() {
                    "sat" => return SolverResult::Sat,
                    "unsat" => return SolverResult::Unsat,
                    "unknown" => return SolverResult::Unknown,
                    _ => {}
                }
            }
            SolverResult::Unknown
        }
        Err(e) => panic!("{}: {e}", path.display()),
    }
}

fn expected(path: &Path) -> SolverResult {
    let source = std::fs::read_to_string(path).unwrap();
    for line in source.lines().take(8) {
        let l = line.to_lowercase();
        if l.contains("expected:") {
            if l.contains("unsat") {
                return SolverResult::Unsat;
            }
            if l.contains("sat") {
                return SolverResult::Sat;
            }
        }
    }
    panic!("{}: missing expected", path.display());
}

#[test]
fn qf_ania_ce_all_fixtures() {
    let dir = fixture_dir();
    assert!(dir.is_dir(), "missing {}", dir.display());
    let mut paths: Vec<_> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| e.ok())
        .map(|e| e.path())
        .filter(|p| p.extension().is_some_and(|x| x == "smt2"))
        .collect();
    paths.sort();
    let mut failures = Vec::new();
    let mut exact = 0usize;
    for path in &paths {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let exp = expected(path);
        let actual = run_smt2(path);
        eprintln!("  {name}: expected={exp:?} got={actual:?}");
        if actual == exp {
            exact += 1;
        } else {
            failures.push(format!("{name}: expected {exp:?}, got {actual:?}"));
        }
    }
    eprintln!("qf_ania_ce: {exact}/{} exact", paths.len());
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}
