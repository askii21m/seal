//! T4: differential of our interpreter against Bitcoin Core's own consensus
//! test corpus (src/test/data/script_tests.json, vendored under tests/data/).
//!
//! Our interpreter is the executable target semantics; the deepest item in the
//! trusted base is whether it matches what Bitcoin
//! actually enforces. The faithful check is a regtest differential against a
//! live bitcoind (Phase 4, M7); absent a node, Core's script_tests.json is the
//! next best authority -- it IS the corpus Core's own consensus tests run.
//!
//! Scope and soundness of the mapping. Core's vectors are legacy-script-model
//! and flag-parameterized; our interpreter is fixed tapscript (BIP342). So we
//! restrict to the subset where the two are directly comparable and a mismatch
//! is unambiguously a bug in OUR interpreter, not a legacy/tapscript rule
//! delta:
//!   - expected result is OK or EVAL_FALSE (a clean value-based accept/reject,
//!     not a policy-flag rejection like MINIMALDATA/CLEANSTACK/SIG_*);
//!   - no segwit witness entry;
//!   - both scripts assemble using ONLY the opcodes our compiler emits and our
//!     interpreter executes (arithmetic, comparison, stack, hashes, IF/VERIFY)
//!     -- excluding signature, timelock, and disabled/legacy-only opcodes;
//!   - the run-time tapscript rule deltas (MINIMALIF, CLEANSTACK, minimal
//!     numbers) are detected and excluded explicitly (see EXPLAINED_DELTAS),
//!     never silently tolerated.
//!
//! Within that subset, our interpreter must match Core exactly. The legacy
//! execution model (scriptSig then scriptPubKey on one stack, pre-P2SH) maps
//! to our model as execute(scriptSig ++ scriptPubKey, empty witness).

use seal::verify::interp::{Context, execute};

/// A tolerant JSON value, enough for this corpus (arrays, strings, and atoms
/// we ignore). The repo's strict args parser rejects the float BTC amounts in
/// segwit rows (which we skip anyway), so a small local parser is simpler.
enum V {
    Arr(Vec<V>),
    Str(String),
    Other,
}

fn skip_ws(b: &[u8], i: &mut usize) {
    while *i < b.len() && matches!(b[*i], b' ' | b'\n' | b'\t' | b'\r' | b',') {
        *i += 1;
    }
}

fn parse_val(b: &[u8], i: &mut usize) -> Option<V> {
    skip_ws(b, i);
    match *b.get(*i)? {
        b'[' => {
            *i += 1;
            let mut items = Vec::new();
            loop {
                skip_ws(b, i);
                if *b.get(*i)? == b']' {
                    *i += 1;
                    return Some(V::Arr(items));
                }
                items.push(parse_val(b, i)?);
            }
        }
        b'"' => {
            *i += 1;
            let mut s = String::new();
            loop {
                let c = *b.get(*i)?;
                *i += 1;
                match c {
                    b'"' => return Some(V::Str(s)),
                    b'\\' => {
                        let e = *b.get(*i)?;
                        *i += 1;
                        match e {
                            b'n' => s.push('\n'),
                            b't' => s.push('\t'),
                            b'r' => s.push('\r'),
                            b'u' => {
                                *i += 4; // skip the code point; not in any field we read
                                s.push('?');
                            }
                            other => s.push(other as char),
                        }
                    }
                    _ => s.push(c as char), // corpus fields are ASCII
                }
            }
        }
        _ => {
            while *i < b.len()
                && !matches!(b[*i], b',' | b']' | b'}' | b' ' | b'\n' | b'\t' | b'\r')
            {
                *i += 1;
            }
            Some(V::Other)
        }
    }
}

/// Opcodes our compiler emits and our interpreter executes, with the names
/// Core uses in script_tests.json. Signature/timelock opcodes are excluded
/// (they need a context/oracle and the sig scheme differs from legacy).
fn opcode_byte(name: &str) -> Option<u8> {
    Some(match name {
        "IF" => 0x63,
        "NOTIF" => 0x64,
        "ELSE" => 0x67,
        "ENDIF" => 0x68,
        "VERIFY" => 0x69,
        "2DROP" => 0x6d,
        "DROP" => 0x75,
        "DUP" => 0x76,
        "NIP" => 0x77,
        "OVER" => 0x78,
        "PICK" => 0x79,
        "ROLL" => 0x7a,
        "SWAP" => 0x7c,
        "TUCK" => 0x7d,
        "SIZE" => 0x82,
        "EQUAL" => 0x87,
        "EQUALVERIFY" => 0x88,
        "1ADD" => 0x8b,
        "1SUB" => 0x8c,
        "NEGATE" => 0x8f,
        "ABS" => 0x90,
        "NOT" => 0x91,
        "0NOTEQUAL" => 0x92,
        "ADD" => 0x93,
        "SUB" => 0x94,
        "BOOLAND" => 0x9a,
        "BOOLOR" => 0x9b,
        "NUMEQUAL" => 0x9c,
        "NUMEQUALVERIFY" => 0x9d,
        "NUMNOTEQUAL" => 0x9e,
        "LESSTHAN" => 0x9f,
        "GREATERTHAN" => 0xa0,
        "LESSTHANOREQUAL" => 0xa1,
        "GREATERTHANOREQUAL" => 0xa2,
        "MIN" => 0xa3,
        "MAX" => 0xa4,
        "WITHIN" => 0xa5,
        "RIPEMD160" => 0xa6,
        "SHA1" => 0xa7, // now executed (interp matches Core); see src/sha1.rs
        "SHA256" => 0xa8,
        "HASH160" => 0xa9,
        "HASH256" => 0xaa,
        _ => return None,
    })
}

/// Minimal push of a byte string (mirrors Core/our serializer's push forms).
fn push_data(out: &mut Vec<u8>, data: &[u8]) {
    match data.len() {
        0 => out.push(0x00),
        1..=75 => {
            out.push(data.len() as u8);
            out.extend_from_slice(data);
        }
        76..=255 => {
            out.push(0x4c);
            out.push(data.len() as u8);
            out.extend_from_slice(data);
        }
        _ => {
            out.push(0x4d);
            out.push((data.len() & 0xff) as u8);
            out.push(((data.len() >> 8) & 0xff) as u8);
            out.extend_from_slice(data);
        }
    }
}

fn encode_num(v: i64) -> Vec<u8> {
    if v == 0 {
        return Vec::new();
    }
    let neg = v < 0;
    let mut abs = v.unsigned_abs();
    let mut out = Vec::new();
    while abs > 0 {
        out.push((abs & 0xff) as u8);
        abs >>= 8;
    }
    if out.last().unwrap() & 0x80 != 0 {
        out.push(if neg { 0x80 } else { 0x00 });
    } else if neg {
        *out.last_mut().unwrap() |= 0x80;
    }
    out
}

/// Assemble one Core script-asm string into bytes, or None if it uses a token
/// (opcode) outside our supported set -- those tests are out of scope.
fn assemble(src: &str) -> Option<Vec<u8>> {
    let mut out = Vec::new();
    for tok in src.split_whitespace() {
        if let Some(hex) = tok.strip_prefix("0x") {
            // Raw bytes appended verbatim (opcodes and/or push data).
            if hex.len() % 2 != 0 {
                return None;
            }
            for i in (0..hex.len()).step_by(2) {
                out.push(u8::from_str_radix(&hex[i..i + 2], 16).ok()?);
            }
        } else if tok.len() >= 2 && tok.starts_with('\'') && tok.ends_with('\'') {
            push_data(&mut out, &tok.as_bytes()[1..tok.len() - 1]);
        } else if let Ok(n) = tok.parse::<i64>() {
            match n {
                0 => out.push(0x00),
                -1 => out.push(0x4f),
                1..=16 => out.push(0x50 + n as u8),
                _ => push_data(&mut out, &encode_num(n)),
            }
        } else {
            out.push(opcode_byte(tok)?);
        }
    }
    Some(out)
}

/// A 0x-token script may smuggle in a raw opcode byte outside our set; reject
/// any script byte that is an executed opcode we do not support (so a raw
/// 0x.. test cannot silently exercise an unmodeled opcode). Pushes (<= 0x4e,
/// and OP_0/1NEGATE/1-16) and our supported opcode bytes are allowed.
fn only_supported_bytes(script: &[u8]) -> bool {
    const SUPPORTED: &[u8] = &[
        0x63, 0x64, 0x67, 0x68, 0x69, 0x6d, 0x75, 0x76, 0x77, 0x78, 0x79, 0x7a, 0x7c, 0x7d, 0x82,
        0x87, 0x88, 0x8b, 0x8c, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x9a, 0x9b, 0x9c, 0x9d, 0x9e,
        0x9f, 0xa0, 0xa1, 0xa2, 0xa3, 0xa4, 0xa5, 0xa6, 0xa7, 0xa8, 0xa9, 0xaa,
    ];
    let mut i = 0;
    while i < script.len() {
        let b = script[i];
        if b <= 0x4b {
            i += 1 + b as usize; // direct push of b bytes
        } else if b == 0x4c {
            let Some(&n) = script.get(i + 1) else {
                return false;
            };
            i += 2 + n as usize;
        } else if b == 0x4d {
            let (Some(&lo), Some(&hi)) = (script.get(i + 1), script.get(i + 2)) else {
                return false;
            };
            i += 3 + (lo as usize | ((hi as usize) << 8));
        } else if b == 0x4e {
            return false; // PUSHDATA4: out of scope
        } else if b == 0x4f || (0x51..=0x60).contains(&b) {
            i += 1; // OP_1NEGATE / OP_1..OP_16
        } else if SUPPORTED.contains(&b) {
            i += 1;
        } else {
            return false; // an opcode we do not execute (or a legacy-only one)
        }
    }
    i == script.len() // a push overrunning the end leaves i > len: out of scope
}

struct Outcome {
    considered: usize,
    agreed: usize,
    /// Disagreements explained by a tapscript rule our interpreter enforces
    /// but the legacy vector's flags do not (CLEANSTACK, minimal encoding,
    /// MINIMALIF). The opcodes still COMPUTED identically; only a wrapper rule
    /// differs. These are not bugs.
    known_deltas: usize,
    mismatches: Vec<String>,
}

/// Does our interpreter's rejection reason come from a tapscript-stricter
/// wrapper rule (not an opcode-computation disagreement)? Such a rejection on
/// a legacy-OK vector is an expected rule delta, not a divergence.
fn is_tapscript_delta(err: &str) -> bool {
    let e = err.to_ascii_lowercase();
    e.contains("cleanstack") || e.contains("minimal")
}

fn run_corpus() -> Outcome {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/data/script_tests.json");
    let src = std::fs::read_to_string(path).expect("vendored script_tests.json");
    let bytes = src.as_bytes();
    let mut pos = 0;
    let V::Arr(tests) = parse_val(bytes, &mut pos).expect("parse script_tests.json") else {
        panic!("expected a JSON array");
    };

    let oracle = |_pk: &[u8], _s: &[u8]| false; // no CHECKSIG in scope
    let ctx = Context {
        locktime: 0,
        sequence: 0xffff_ffff,
        tx_version: 2,
        verify_sig: &oracle,
    };

    let mut considered = 0;
    let mut agreed = 0;
    let mut known_deltas = 0;
    let mut mismatches = Vec::new();

    for t in &tests {
        let V::Arr(cols) = t else { continue };
        // Skip comment rows (a single string) and segwit rows (first col is an
        // array: [wit.., amount]).
        if cols.len() < 4 {
            continue;
        }
        if matches!(cols[0], V::Arr(_)) {
            continue;
        }
        let (V::Str(sig), V::Str(spk), V::Str(expected)) = (&cols[0], &cols[1], &cols[3]) else {
            continue;
        };
        // Only clean value-based outcomes -- never a policy-flag rejection.
        if expected != "OK" && expected != "EVAL_FALSE" {
            continue;
        }
        let (Some(sig_b), Some(spk_b)) = (assemble(sig), assemble(spk)) else {
            continue;
        };
        let mut script = sig_b;
        script.extend_from_slice(&spk_b);
        if !only_supported_bytes(&script) {
            continue;
        }

        considered += 1;
        let result = execute(&script, &[], &ctx);
        let ours_ok = result.is_ok();
        let core_ok = expected == "OK";
        if ours_ok == core_ok {
            agreed += 1;
        } else if core_ok && result.as_ref().err().is_some_and(|e| is_tapscript_delta(e)) {
            // Legacy accepted under lenient flags; we reject under a stricter
            // tapscript wrapper rule. The opcodes computed fine. Not a bug.
            known_deltas += 1;
        } else {
            let why = result.err().unwrap_or_else(|| "accepted".into());
            mismatches.push(format!(
                "[{sig}] [{spk}] expected={expected} ours_ok={ours_ok} ({why})"
            ));
        }
    }
    Outcome {
        considered,
        agreed,
        known_deltas,
        mismatches,
    }
}

/// Our interpreter must agree with Bitcoin Core on every in-scope vector of
/// Core's own consensus test corpus. A mismatch is either a real interpreter
/// bug or an undocumented tapscript/legacy rule delta -- both must be
/// surfaced, never silently tolerated.
#[test]
fn interp_matches_bitcoin_core_script_tests() {
    let o = run_corpus();
    eprintln!(
        "core differential: {} considered, {} agreed, {} known tapscript deltas, {} mismatches",
        o.considered,
        o.agreed,
        o.known_deltas,
        o.mismatches.len()
    );
    if !o.mismatches.is_empty() {
        for m in o.mismatches.iter().take(60) {
            eprintln!("  MISMATCH {m}");
        }
        panic!(
            "{} opcode-computation mismatches vs Bitcoin Core (see above)",
            o.mismatches.len()
        );
    }
    // Teeth: the validation must rest on real agreements, not be all-deltas.
    assert!(
        o.agreed >= 50,
        "only {} genuine agreements (filter too aggressive?)",
        o.agreed
    );
}
