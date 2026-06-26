//! `seal`, the Seal compiler driver.
//!
//! A thin I/O + rendering shell over [`seal::compile::compile`]: it parses
//! arguments, reads files, calls the one shared pipeline, and renders the result
//! to stdout/stderr with the right exit code. All compilation logic (and the
//! fail-closed funding gate DECISION) lives in the library, so this driver and
//! any other embedder (e.g. a WASM web IDE) cannot derive a different address
//! from the same input.
//!
//! Usage:
//!   seal <file.sl>                  check syntax + semantics (template level)
//!   seal <file.sl> --args <json>    also bind externs and instantiate
//!   seal <file.sl> --tokens         dump the token stream
//!   seal <file.sl> --ast            dump the parsed AST
//!   seal <file.sl> --args <json> --report   print proven facts (bounds, paths)
//!   seal <file.sl> --args <json> --script   print lowered tapscript per leaf
//!   seal <file.sl> --args <json> --address  assemble the taproot output
//!   seal <file.sl> --args <json> --lock     write <file>.lock
//!   seal <file.sl> --args <json> --verify <lock>   exact-match re-derivation (determinism)
//!   seal <file.sl> --args <json> --certify  prove optimized == naive == predicate
//!                                          over each finite witness domain (T1+T2)
//!
//! Fail-closed funding: `--address`, `--lock`, and `--verify` re-derive a real
//! Bitcoin address, so the driver certifies every leaf first and REFUSES to emit
//! the address unless each leaf is proven correct over its complete witness
//! domain. A leaf that is only differentially checked / windowed / unbounded is
//! "unproven" and blocks emission unless `--allow-unproven` is passed (which
//! emits with a loud per-leaf warning). A leaf that actively diverges blocks
//! emission unconditionally -- the override cannot fund a known-wrong compile.

use std::process::ExitCode;

use seal::compile::{CompileOptions, DiagFile, GateOutcome, Target, compile};
use seal::syntax::span::LineIndex;

fn hex(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap_or('?'));
        s.push(char::from_digit((b & 0xf) as u32, 16).unwrap_or('?'));
    }
    s
}

/// Print the assembled taproot output: address + the satisfier-facing
/// artifacts (control blocks, NUMS disclosure).
fn print_output(
    out: &seal::output::taproot::ContractOutput,
    address: &str,
    leaves: &[seal::codegen::lower::LoweredLeaf],
) {
    let asm = &out.assembled;
    println!("address:      {address}");
    println!(
        "output key:   {} (parity {})",
        hex(&asm.output_key),
        u8::from(asm.parity)
    );
    match &out.nums_r {
        Some(r) => {
            println!("internal key: {} (NUMS: H + r*G)", hex(&asm.internal_key));
            println!("  r:          {}", hex(r));
        }
        None => println!("internal key: {}", hex(&asm.internal_key)),
    }
    if let Some(root) = &asm.merkle_root {
        println!("merkle root:  {}", hex(root));
    }
    for (leaf, a) in leaves.iter().zip(&asm.leaves) {
        println!(
            "leaf {} (depth {}): control block {}",
            leaf.name,
            a.path.len(),
            hex(&a.control_block)
        );
    }
}

/// Loud reminder, printed to stderr whenever the CLI emits or re-derives a real
/// mainnet address (`--address`, `--lock`, `--verify`). "Proven" means proven
/// against the source predicate by alpha, unaudited code; a compiler bug or a
/// contract that does not mean what the author intended still loses funds.
fn warn_mainnet_funding(color: bool) {
    let (yellow, reset) = if color {
        ("\x1b[1;33m", "\x1b[0m")
    } else {
        ("", "")
    };
    eprintln!(
        "{yellow}warning[funding/mainnet]{reset}: this is a real Bitcoin mainnet address \
         produced by alpha, unaudited software."
    );
    eprintln!(
        "  a bug in the compiler, or a contract that does not mean what you think, can lock \
         your coins permanently."
    );
    eprintln!("  never fund it unless you are prepared to lose those funds entirely.");
}

const USAGE: &str = "\
usage: seal <file.sl> [options]

  <file.sl>              check syntax and semantics (template level)
  --args <file.json>     bind externs and instantiate with concrete values

output modes (choose at most one):
  --tokens               dump the token stream
  --ast                  dump the parsed AST
  --report               print proven facts (bounds, paths)        [needs --args]
  --script               print the lowered tapscript per leaf       [needs --args]
  --address              assemble and print the taproot address     [needs --args]
  --cost                 print the worst-case spend cost per leaf    [needs --args]
  --lock                 write <file>.lock                          [needs --args]
  --certify              prove optimized == naive == predicate       [needs --args]
  --json                 emit the full compile result as JSON         [needs --args]
                         (diagnostics with line/col, address, leaves, certification,
                         gate verdict) -- the machine/embedder surface; exits 0

  --verify <file.lock>   re-derive and exact-match an existing lockfile
  --allow-unproven       emit a fundable address even if a leaf is not proven
                         over its full domain (prints a per-leaf warning; never
                         overrides a real divergence)
  --version              print the compiler version
  -h, --help             print this help

--address, --lock, and --verify produce a fundable Bitcoin address; the driver
certifies every leaf first and refuses to emit unless each is proven (override
the unproven case, not a divergence, with --allow-unproven).

These are real mainnet addresses from alpha, unaudited software. Never fund one
unless you are prepared to lose those funds entirely.

exit codes: 0 success, 1 compile/verification failure, 2 usage error,
            3 i/o error, 4 internal compiler bug";

fn main() -> ExitCode {
    let argv: Vec<String> = std::env::args().skip(1).collect();
    let mut path: Option<String> = None;
    let mut flag: Option<String> = None;
    let mut args_path: Option<String> = None;
    let mut verify_path: Option<String> = None;
    let mut allow_unproven = false;
    let mut i = 0;
    while i < argv.len() {
        match argv[i].as_str() {
            "-h" | "--help" => {
                println!("{USAGE}");
                return ExitCode::SUCCESS;
            }
            "--version" => {
                println!("seal {}", env!("CARGO_PKG_VERSION"));
                return ExitCode::SUCCESS;
            }
            mode @ ("--tokens" | "--ast" | "--report" | "--script" | "--address" | "--lock"
            | "--certify" | "--cost" | "--json") => {
                if let Some(prev) = &flag {
                    eprintln!(
                        "seal: error: `{prev}` and `{mode}` are mutually exclusive output modes"
                    );
                    return ExitCode::from(2);
                }
                flag = Some(mode.to_string());
            }
            "--verify" => {
                i += 1;
                match argv.get(i) {
                    Some(p) => verify_path = Some(p.clone()),
                    None => {
                        eprintln!("seal: error: `--verify` needs a lockfile path");
                        return ExitCode::from(2);
                    }
                }
            }
            "--allow-unproven" => allow_unproven = true,
            "--args" => {
                i += 1;
                match argv.get(i) {
                    Some(p) => args_path = Some(p.clone()),
                    None => {
                        eprintln!("seal: error: `--args` needs a file path");
                        return ExitCode::from(2);
                    }
                }
            }
            p if !p.starts_with('-') && path.is_none() => path = Some(p.to_string()),
            other => {
                eprintln!("seal: error: unexpected argument `{other}`\n\n{USAGE}");
                return ExitCode::from(2);
            }
        }
        i += 1;
    }
    let Some(path) = path else {
        eprintln!("seal: error: no input file\n\n{USAGE}");
        return ExitCode::from(2);
    };

    // I/O lives in the driver; the library `compile` is pure.
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("seal: error: cannot read {path}: {e}");
            return ExitCode::from(3);
        }
    };
    let args_src = match &args_path {
        Some(ap) => match std::fs::read_to_string(ap) {
            Ok(s) => Some(s),
            Err(e) => {
                eprintln!("seal: error: cannot read {ap}: {e}");
                return ExitCode::from(3);
            }
        },
        None => None,
    };

    // Diagnostics, verdicts, and status go to stderr; the requested data (the
    // output mode) goes to stdout. Color only on a TTY (and never if NO_COLOR).
    let color = seal::diagnostics::use_color(true);

    // `--verify` always re-derives a fundable address (so it certifies); the
    // output flags otherwise map to how far the shared pipeline runs.
    let target = if verify_path.is_some() {
        Target::Fund
    } else {
        match flag.as_deref() {
            Some("--script") => Target::Lower,
            Some("--certify") => Target::Certify,
            Some("--cost") => Target::Cost,
            Some("--address") | Some("--lock") | Some("--json") => Target::Fund,
            _ => Target::Check,
        }
    };

    let result = compile(
        &src,
        args_src.as_deref(),
        target,
        CompileOptions {
            allow_unproven,
            hrp: "bc",
        },
    );

    // `--json` is the machine surface (the same structured result a web IDE
    // consumes): emit the whole result -- including the gate verdict, any
    // internal error, and every diagnostic with line/col -- as JSON to stdout
    // and exit 0. The JSON itself carries success/failure, so a consumer reads
    // the data rather than the exit code.
    if flag.as_deref() == Some("--json") {
        println!(
            "{}",
            seal::compile::result_to_json(&result, &src, args_src.as_deref())
        );
        return ExitCode::SUCCESS;
    }

    // A token-stream invariant violation is a compiler bug: distinct exit code,
    // and (as before) no other output.
    if let Some(e) = &result.internal_error {
        eprintln!("seal: internal compiler error (please report): {e}");
        return ExitCode::from(4);
    }

    if flag.as_deref() == Some("--tokens") {
        for t in &result.tokens {
            println!("{:>5}..{:<5} {:?}", t.span.start, t.span.end, t.kind);
        }
    }

    // Certification verdicts + the gate notes (stderr), when the gate ran.
    if let (Some(reports), Some(gate)) = (&result.certification, &result.gate) {
        render_certification(reports, gate, allow_unproven, color);
    }

    if flag.as_deref() == Some("--script")
        && let Some(leaves) = &result.leaves
    {
        for leaf in leaves {
            println!("leaf {} ({} bytes)", leaf.name, leaf.script.len());
            println!("  asm: {}", seal::codegen::script::asm(&leaf.ops));
            println!("  hex: {}", hex(&leaf.script));
            println!(
                "  witness (first = deepest): {}",
                leaf.witness_order.join(", ")
            );
        }
    }

    // Assembled, fundable artifacts (present only when the gate allowed it).
    if let Some(asm) = &result.assembled {
        if flag.as_deref() == Some("--cost")
            && let Some(costs) = &result.costs
        {
            for sc in costs {
                println!(
                    "cost {}: script {} B, control {} B, witness {} B (worst-case) => witness {} WU = {:.2} vB; input {} WU = {:.2} vB",
                    sc.name,
                    sc.script_bytes,
                    sc.control_bytes,
                    sc.witness_elem_bytes,
                    sc.max_witness_weight,
                    sc.max_vbytes,
                    sc.max_input_weight,
                    sc.max_input_vbytes
                );
            }
        }
        if flag.as_deref() == Some("--address") {
            print_output(
                &asm.output,
                &asm.address,
                result.leaves.as_deref().unwrap_or(&[]),
            );
        }
        if flag.as_deref() == Some("--lock") {
            let lock_path = std::path::Path::new(&path).with_extension("lock");
            match std::fs::write(&lock_path, &asm.lockfile) {
                Ok(()) => eprintln!("seal: wrote {}", lock_path.display()),
                Err(e) => {
                    eprintln!("seal: error: cannot write {}: {e}", lock_path.display());
                    return ExitCode::from(3);
                }
            }
        }
        if let Some(vp) = &verify_path {
            match std::fs::read_to_string(vp) {
                Ok(existing) if existing == asm.lockfile => {
                    eprintln!("seal: lockfile verified -- the address re-derives exactly ({vp})");
                }
                Ok(_) => {
                    eprintln!(
                        "seal: error: lockfile mismatch -- the rebuild does not reproduce {vp} (source, args, or compiler version changed)"
                    );
                    return ExitCode::FAILURE;
                }
                Err(e) => {
                    eprintln!("seal: error: cannot read {vp}: {e}");
                    return ExitCode::from(3);
                }
            }
        }

        // A real mainnet address was just emitted, written, or re-derived.
        if matches!(flag.as_deref(), Some("--address" | "--lock")) || verify_path.is_some() {
            warn_mainnet_funding(color);
        }
    }

    // Proven facts (stdout), present only when the interval engine ran clean.
    if flag.as_deref() == Some("--report")
        && let Some((report, paths)) = &result.facts
    {
        for (spend, name, iv) in &report.lets {
            println!("{spend}.{name} in [{}, {}]  (proven, bounds)", iv.lo, iv.hi);
        }
        for p in &paths.paths {
            let open = if p.open {
                " (OPEN: anyone can spend)"
            } else {
                ""
            };
            println!("path {} [{}]{}", p.name, p.kind, open);
            for param in &p.params {
                println!(
                    "  witness {}: {}  - {:?}",
                    param.name, param.ty, param.class
                );
            }
            if let Some((k, n)) = p.threshold {
                println!("  threshold: {k} of {n}");
            }
            for o in &p.obligations {
                println!("  obligation: {o}");
            }
        }
    }

    // Diagnostics render against whichever input each one describes.
    let index = LineIndex::new(&src);
    let args_index = args_src.as_deref().map(LineIndex::new);
    for (file, d) in &result.diagnostics {
        match file {
            DiagFile::Source => eprintln!("{}", d.render(&path, &src, &index, color)),
            DiagFile::Args => {
                if let (Some(ap), Some(asrc), Some(aidx)) = (&args_path, &args_src, &args_index) {
                    eprintln!("{}", d.render(ap, asrc, aidx, color));
                }
            }
        }
    }

    if flag.as_deref() == Some("--ast") {
        match &result.contract {
            Some(c) => println!("{c:#?}"),
            None => eprintln!("seal: error: no contract produced (parse failed)"),
        }
    }

    // An internal-class error (a compiler bug surfacing as a diagnostic) exits
    // 4, distinct from an ordinary compile failure (1).
    let errors = result.error_count();
    if errors == 0 && result.contract.is_some() && !result.gate_failed() {
        if args_path.is_some() {
            eprintln!(
                "seal: ok -- instantiated, {} externs bound",
                result.bound_externs
            );
        } else {
            eprintln!("seal: ok -- checks pass (template level)");
        }
        ExitCode::SUCCESS
    } else if result.has_internal_error() {
        ExitCode::from(4)
    } else {
        ExitCode::FAILURE
    }
}

/// Render every leaf's certification verdict, then the gate notes (warning or
/// refusal). The DECISION already lives in `gate` (computed by the library);
/// this only presents it. All output goes to stderr.
fn render_certification(
    reports: &[seal::verify::certify::LeafReport],
    gate: &GateOutcome,
    allow_unproven: bool,
    color: bool,
) {
    use seal::verify::certify::{CertStatus, ProvenKind};
    let (red, yellow, green, reset) = if color {
        ("\x1b[1;31m", "\x1b[1;33m", "\x1b[1;32m", "\x1b[0m")
    } else {
        ("", "", "", "")
    };
    for r in reports {
        let name = &r.name;
        let (col, detail) = match &r.status {
            CertStatus::Certified { checked } => (
                green,
                format!("certified -- {checked} witnesses (exhaustive)"),
            ),
            CertStatus::Proven {
                kind: ProvenKind::FullInt { var, breakpoints },
            } => (
                green,
                format!(
                    "proven -- full Int domain (every CScriptNum value of `{var}`, {breakpoints} cells)"
                ),
            ),
            CertStatus::Proven {
                kind: ProvenKind::FullSymbolic { atoms },
            } => (
                green,
                format!(
                    "proven -- full symbolic domain (every assignment of {atoms} witness atoms)"
                ),
            ),
            CertStatus::Proven {
                kind: ProvenKind::T2OnlySymbolic { atoms, t1_reason },
            } => (
                yellow,
                format!(
                    "optimizer proven equivalent to naive ({atoms} atoms), but the predicate is not independently proven ({t1_reason})"
                ),
            ),
            CertStatus::Differential { checked, reason } => (
                yellow,
                format!(
                    "optimizer proven equivalent to naive ({checked} witnesses), but the predicate is not independently proven ({reason})"
                ),
            ),
            CertStatus::BoundedChecked { checked, lo, hi } => (
                yellow,
                format!(
                    "checked only over the window [{lo}, {hi}] ({checked} witnesses), not the full integer domain"
                ),
            ),
            CertStatus::Unbounded { reason } => (
                yellow,
                format!("not proven -- the witness domain was not exhausted ({reason})"),
            ),
            CertStatus::Failed { detail } => (red, format!("DIVERGENCE -- {detail}")),
        };
        eprintln!("certify `{name}`: {col}{detail}{reset}");
    }

    let funding = gate.funding;
    if gate.divergence {
        eprintln!(
            "{red}error[certify/divergence]{reset}: refusing to {} -- a leaf is known-wrong",
            if funding {
                "emit a fundable address"
            } else {
                "certify this contract"
            }
        );
        eprintln!(
            "  = note: a concrete witness makes the scripts or the predicate disagree -- this is a compiler-correctness failure"
        );
        eprintln!("  = note: --allow-unproven cannot override a divergence");
    } else if gate.unproven > 0 {
        if allow_unproven {
            eprintln!(
                "{yellow}warning[certify/unproven]{reset}: {} leaf(s) not proven over their full domain -- proceeding because --allow-unproven was passed",
                gate.unproven
            );
            if funding {
                eprintln!(
                    "  = note: you are funding an address whose correctness is not fully proven -- do so at your own risk"
                );
            }
        } else {
            eprintln!(
                "{red}error[certify/unproven]{reset}: {} leaf(s) not proven over their full domain",
                gate.unproven
            );
            if funding {
                eprintln!("  = note: refusing to emit a fundable address that is not fully proven");
            }
            eprintln!(
                "  = help: prove the leaves above, or pass --allow-unproven to accept the risk and emit anyway"
            );
        }
    }

    // Fail-closed coverage gap (only ever set for a funding target).
    if gate.coverage_gap {
        eprintln!(
            "{red}error[certify/coverage]{reset}: an assembled leaf has no certification -- refusing to emit a fundable address"
        );
    }
}
