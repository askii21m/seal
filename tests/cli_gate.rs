//! The fail-closed funding gate (driver-level). `--address`, `--lock`, and
//! `--verify` re-derive a real Bitcoin address, so `seal` certifies every leaf
//! first and REFUSES to emit unless each is proven over its full witness
//! domain. An unproven leaf is overridable with `--allow-unproven` (and then
//! warns); a divergence is never overridable. These tests pin that contract at
//! the CLI boundary -- the only place that actually hands a fundable address to
//! a user.
//!
//! Proven fixture: `multisig` is exhaustively CERTIFIED. Unproven fixture: a
//! synthetic contract with two `relaxed`, unbounded Int witnesses (`a < b`) --
//! the domain cannot be exhausted and is not single-Int affine, so it stays
//! Unbounded. `relaxed` passes the malleability gate. (The corpus timelock
//! leaves are now Certified, so they are no longer unproven; this synthetic
//! contract is a stable stand-in until multi-variable SMT lands, if ever.)

use std::path::PathBuf;
use std::process::{Command, Output};

fn seal() -> &'static str {
    env!("CARGO_BIN_EXE_seal")
}

fn examples() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/corpus")
}

fn stdout(o: &Output) -> String {
    String::from_utf8_lossy(&o.stdout).into_owned()
}
fn stderr(o: &Output) -> String {
    String::from_utf8_lossy(&o.stderr).into_owned()
}

/// Run `seal <bs> --args <args> <extra...>`.
fn run(bs: &PathBuf, args: &PathBuf, extra: &[&str]) -> Output {
    let mut cmd = Command::new(seal());
    cmd.arg(bs).arg("--args").arg(args).args(extra);
    cmd.output().expect("spawn seal")
}

/// A committed proven example: `seal tests/corpus/<name>.sl --args ...`.
fn run_example(name: &str, extra: &[&str]) -> Output {
    let dir = examples();
    run(
        &dir.join(format!("{name}.sl")),
        &dir.join(format!("{name}.args.json")),
        extra,
    )
}

/// Materialize a contract that compiles but cannot be certified: two unbounded
/// `relaxed` Int witnesses, so the witness domain can't be exhausted. Returns
/// `(dir, bs, args)`; the caller removes `dir`. `tag` keeps concurrent tests'
/// temp dirs distinct.
fn unprovable_fixture(tag: &str) -> (PathBuf, PathBuf, PathBuf) {
    let dir = std::env::temp_dir().join(format!("seal_gate_{tag}"));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();
    let bs = dir.join("u.sl");
    let args = dir.join("u.args.json");
    std::fs::write(
        &bs,
        "contract U {\n  extern const k: PublicKey;\n  \
         spend f(relaxed a: Int, relaxed b: Int, s: Signature) {\n    \
         require { a < b, k.check(s) }\n  }\n  keypath None;\n}\n",
    )
    .unwrap();
    // Any valid x-only key; certification fails before the address math cares.
    std::fs::write(
        &args,
        "{ \"k\": \"0x2b4ea0a797a443d293ef5cff444f4979f06acfebd7e86d277475656138385b6c\" }\n",
    )
    .unwrap();
    (dir, bs, args)
}

/// A fully-proven contract emits its address and exits 0.
#[test]
fn proven_contract_emits_address() {
    let o = run_example("multisig", &["--address"]);
    assert!(
        o.status.success(),
        "proven --address should exit 0: {}",
        stderr(&o)
    );
    assert!(
        stdout(&o).contains("address:"),
        "expected an address on stdout: {}",
        stdout(&o)
    );
}

/// An unproven contract REFUSES `--address` with no override: non-zero exit,
/// and -- critically -- NO address is printed to stdout.
#[test]
fn unproven_address_is_refused_without_override() {
    let (dir, bs, args) = unprovable_fixture("refuse");
    let o = run(&bs, &args, &["--address"]);
    assert!(!o.status.success(), "unproven --address must NOT exit 0");
    assert!(
        !stdout(&o).contains("address:"),
        "an unproven address must never reach stdout: {}",
        stdout(&o)
    );
    assert!(
        stderr(&o).contains("refusing to emit"),
        "expected a refusal note: {}",
        stderr(&o)
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--allow-unproven` lets the same contract through, but loudly warns and
/// still emits the address.
#[test]
fn unproven_address_proceeds_with_override() {
    let (dir, bs, args) = unprovable_fixture("override");
    let o = run(&bs, &args, &["--address", "--allow-unproven"]);
    assert!(o.status.success(), "override should exit 0: {}", stderr(&o));
    assert!(
        stdout(&o).contains("address:"),
        "override should still emit the address"
    );
    assert!(
        stderr(&o).contains("warning[certify/unproven]"),
        "override must still warn: {}",
        stderr(&o)
    );
    let _ = std::fs::remove_dir_all(&dir);
}

/// `--certify` exits non-zero on an unproven leaf (previously it exited 0 on
/// anything short of a divergence -- the gap this change closes), and 0 on a
/// proven contract or under the override.
#[test]
fn certify_is_strict_on_unproven() {
    let (dir, bs, args) = unprovable_fixture("certify");
    let unproven = run(&bs, &args, &["--certify"]);
    assert!(
        !unproven.status.success(),
        "--certify on an unproven leaf must fail"
    );

    let overridden = run(&bs, &args, &["--certify", "--allow-unproven"]);
    assert!(
        overridden.status.success(),
        "--certify --allow-unproven must pass: {}",
        stderr(&overridden)
    );
    let _ = std::fs::remove_dir_all(&dir);

    let proven = run_example("multisig", &["--certify"]);
    assert!(
        proven.status.success(),
        "--certify on a proven contract must pass: {}",
        stderr(&proven)
    );
}

/// The money-critical invariant: a refused `--lock` writes NOTHING to disk.
#[test]
fn refused_lock_writes_no_file() {
    let (dir, bs, args) = unprovable_fixture("lock");
    let lock = dir.join("u.lock");

    let o = run(&bs, &args, &["--lock"]);
    assert!(!o.status.success(), "unproven --lock must be refused");
    assert!(!lock.exists(), "a refused --lock must not write a lockfile");

    // With the override, the lock is written.
    let o2 = run(&bs, &args, &["--lock", "--allow-unproven"]);
    assert!(
        o2.status.success(),
        "override --lock should succeed: {}",
        stderr(&o2)
    );
    assert!(lock.exists(), "override --lock should write the file");

    let _ = std::fs::remove_dir_all(&dir);
}
