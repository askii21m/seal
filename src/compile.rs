//! The compile pipeline as one pure library function, shared by the `seal` CLI
//! and any embedder (e.g. a WASM web IDE).
//!
//! [`compile`] performs NO I/O and never prints or exits: it returns every
//! artifact the pipeline produced PLUS the fail-closed funding-gate DECISION as
//! data, so the caller renders results and chooses its own exit behaviour. The
//! CLI and an embedder calling the same `compile` cannot derive a different
//! address from the same input -- a divergence there would be a fund-loss bug,
//! so the single shared code path is the safety property, not a convenience.
//!
//! The control flow mirrors the driver exactly: each stage runs only when the
//! prior stages were clean, and the gate refuses an unproven/divergent/uncovered
//! leaf before any fundable artifact is assembled.

use crate::analysis::intervals::Report;
use crate::analysis::paths::PathReport;
use crate::analysis::sema::ContractInfo;
use crate::codegen::lower::LoweredLeaf;
use crate::cost::SpendCost;
use crate::diagnostics::{Diagnostic, Severity};
use crate::json::Json;
use crate::output::taproot::ContractOutput;
use crate::syntax::ast::Contract;
use crate::syntax::lexer::Token;
use crate::syntax::span::{LineIndex, Span};
use crate::verify::certify::{Assurance, LeafReport};

/// What the caller wants built. Drives exactly how far the pipeline runs and
/// whether the funding gate applies, mirroring the CLI's output modes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Target {
    /// Syntax + semantics + (with args) instantiate + analyses. No lowering.
    /// Covers the CLI's default check, `--tokens`, `--ast`, `--report`.
    Check,
    /// `Check` + lower + optimize (the CLI's `--script`).
    Lower,
    /// `Lower` + certify the leaves under a non-funding gate (`--certify`).
    Certify,
    /// `Lower` + assemble the taproot output WITHOUT the funding gate (`--cost`).
    Cost,
    /// `Lower` + certify + funding gate + assemble + lockfile (`--address`,
    /// `--lock`, `--verify`). A refused gate yields NO assembled output.
    Fund,
}

/// Which input a diagnostic refers to, so an embedder can attribute it to the
/// right editor pane (and the CLI renders it against the right file).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DiagFile {
    Source,
    Args,
}

/// Tuning the caller passes in; kept explicit so neither the CLI nor an embedder
/// hardcodes policy in two places.
#[derive(Debug, Clone, Copy)]
pub struct CompileOptions {
    /// Emit a fundable artifact even if a leaf is not proven over its full
    /// domain (never overrides a real divergence). The CLI's `--allow-unproven`.
    pub allow_unproven: bool,
    /// bech32m HRP for the address (mainnet `"bc"`). Explicit so an embedder can
    /// target testnet/regtest without the gate logic changing.
    pub hrp: &'static str,
}

impl Default for CompileOptions {
    fn default() -> Self {
        CompileOptions {
            allow_unproven: false,
            hrp: "bc",
        }
    }
}

/// The fail-closed gate DECISION (no rendering). `may_proceed` already folds in
/// the divergence rule, the unproven rule, and the coverage check, so it is the
/// single source of truth both the CLI and an embedder read.
#[derive(Debug, Clone)]
pub struct GateOutcome {
    /// A leaf actively diverges (script != predicate on a concrete witness).
    /// Never overridable -- the gate must not fund a known-wrong compile.
    pub divergence: bool,
    /// Count of leaves not proven over their full domain.
    pub unproven: usize,
    /// A leaf to be assembled has no certification report (a coverage hole);
    /// only ever set for a funding target.
    pub coverage_gap: bool,
    /// Whether a fundable artifact may be emitted / the compile may exit 0.
    pub may_proceed: bool,
    /// True for the funding targets (affects only the caller's wording).
    pub funding: bool,
}

/// The assembled, fundable output (present only when the gate allowed it).
#[derive(Debug, Clone)]
pub struct Assembled {
    pub output: ContractOutput,
    pub address: String,
    /// The rendered `.lock` content; the caller writes it (`--lock`) or compares
    /// it (`--verify`).
    pub lockfile: String,
}

/// Everything the pipeline produced. Each field is populated as far as the
/// chosen [`Target`] and the input's validity allowed; the caller reads what it
/// needs and ignores the rest.
#[derive(Debug, Clone)]
pub struct CompileResult {
    /// All diagnostics, in pipeline order, tagged by which input they describe.
    pub diagnostics: Vec<(DiagFile, Diagnostic)>,
    /// A token-stream invariant violation -- a COMPILER BUG, not user error.
    /// When set, the pipeline stopped immediately after lexing.
    pub internal_error: Option<String>,
    /// The token stream (always; lexing is the first stage and is total).
    pub tokens: Vec<Token>,
    /// The parsed contract (`None` if the parse failed).
    pub contract: Option<Contract>,
    /// Number of externs bound from args (for the caller's status line).
    pub bound_externs: usize,
    /// Proven interval facts + path facts, present only when the interval engine
    /// ran clean (the CLI's `--report` prerequisite).
    pub facts: Option<(Report, PathReport)>,
    /// Optimized leaves, present when lowering ran (clean or not).
    pub leaves: Option<Vec<LoweredLeaf>>,
    /// Per-leaf certification verdicts, present when certification ran.
    pub certification: Option<Vec<LeafReport>>,
    /// The funding-gate decision, present exactly when certification ran.
    pub gate: Option<GateOutcome>,
    /// Assembled taproot output + address + lockfile, present when assembly ran
    /// AND (for a funding target) the gate allowed it.
    pub assembled: Option<Assembled>,
    /// Worst-case spend costs, present only for the [`Target::Cost`] target.
    pub costs: Option<Vec<SpendCost>>,
}

impl CompileResult {
    /// Count of error-severity diagnostics across both inputs.
    pub fn error_count(&self) -> usize {
        self.diagnostics
            .iter()
            .filter(|(_, d)| d.severity == Severity::Error)
            .count()
    }

    /// An internal-class error (the token-invariant violation, or a compiler bug
    /// surfacing as a poison/internal diagnostic). The CLI maps this to a
    /// distinct exit code.
    pub fn has_internal_error(&self) -> bool {
        self.internal_error.is_some()
            || self.diagnostics.iter().any(|(_, d)| {
                d.severity == Severity::Error
                    && (d.code == "lower/poison" || d.code.ends_with("/internal"))
            })
    }

    /// The funding gate ran and refused (only meaningful when the gate ran).
    pub fn gate_failed(&self) -> bool {
        self.gate.as_ref().is_some_and(|g| !g.may_proceed)
    }
}

/// Run the pipeline for `target` over `source` (and optional `args` JSON).
///
/// Pure: no filesystem, clock, randomness, or stdout/stderr. Deterministic in
/// `(source, args, target, opts, compiler version)`.
pub fn compile(
    source: &str,
    args: Option<&str>,
    target: Target,
    opts: CompileOptions,
) -> CompileResult {
    let mut result = CompileResult {
        diagnostics: Vec::new(),
        internal_error: None,
        tokens: Vec::new(),
        contract: None,
        bound_externs: 0,
        facts: None,
        leaves: None,
        certification: None,
        gate: None,
        assembled: None,
        costs: None,
    };
    let mut diags: Vec<(DiagFile, Diagnostic)> = Vec::new();

    // Lex, then the token-stream invariant: a violation is a compiler bug, so we
    // stop here and surface it as an internal error rather than a user diag.
    let (tokens, _lex_diags) = crate::syntax::lexer::lex(source);
    if let Err(e) = crate::syntax::lexer::verify_token_stream_invariants(source, &tokens) {
        result.internal_error = Some(e);
        result.tokens = tokens;
        return result;
    }
    result.tokens = tokens;

    let (contract, parse_diags) = crate::syntax::parser::parse_source(source);
    for d in parse_diags {
        diags.push((DiagFile::Source, d));
    }

    // Semantic checks run only on a syntactically clean parse; a broken parse
    // would produce misleading semantic noise.
    if diags.is_empty()
        && let Some(c) = &contract
    {
        let (sema_diags, info) = crate::analysis::sema::analyze(c);
        let sema_clean = sema_diags.is_empty();
        for d in sema_diags {
            diags.push((DiagFile::Source, d));
        }
        if sema_clean && let Some(args_src) = args {
            instantiated(
                source,
                c,
                &info,
                args_src,
                target,
                opts,
                &mut result,
                &mut diags,
            );
        }
    }

    result.contract = contract;
    result.diagnostics = diags;
    result
}

/// The instantiated half of the pipeline (everything that needs concrete args):
/// bind -> instantiate -> limits -> intervals -> paths -> lower -> certify/gate
/// -> assemble. Stages are gated exactly as the driver gates them.
#[allow(clippy::too_many_arguments)]
fn instantiated(
    source: &str,
    c: &Contract,
    info: &ContractInfo,
    args_src: &str,
    target: Target,
    opts: CompileOptions,
    result: &mut CompileResult,
    diags: &mut Vec<(DiagFile, Diagnostic)>,
) {
    // Args JSON parse / bind errors attribute to the args input.
    let json = match crate::json::parse(args_src) {
        Ok(j) => j,
        Err(e) => {
            diags.push((
                DiagFile::Args,
                Diagnostic::error("args/json", e.msg, Span::at(e.offset as u32)),
            ));
            return;
        }
    };
    let mut env = match crate::analysis::consteval::bind_args(info, &json) {
        Ok(env) => env,
        Err(errors) => {
            for e in errors {
                diags.push((
                    DiagFile::Args,
                    Diagnostic::error("args/bind", e, Span::at(0)),
                ));
            }
            return;
        }
    };
    result.bound_externs = env.len();

    let inst = crate::analysis::consteval::instantiate(c, &mut env);
    let inst_clean = inst.iter().all(|d| d.severity != Severity::Error);
    for d in inst {
        diags.push((DiagFile::Source, d));
    }
    if !inst_clean {
        return;
    }

    // Resource limits run BEFORE the interval engine and lowering, so an
    // over-limit contract is rejected before any large allocation (DoS guard).
    let lim = crate::analysis::limits::analyze(c, info, &env);
    let limits_clean = lim.is_empty();
    for d in lim {
        diags.push((DiagFile::Source, d));
    }
    if !limits_clean {
        return;
    }

    // Interval engine (bounds).
    let (g1, report) = crate::analysis::intervals::analyze(c, &env);
    let g1_clean = g1.is_empty();
    for d in g1 {
        diags.push((DiagFile::Source, d));
    }

    // Path analyses (feasibility, authorization, non-malleability). Always run:
    // they emit diagnostics even when intervals were dirty.
    let (pdiags, paths) = crate::analysis::paths::analyze(c, info, &env);
    let paths_clean = pdiags.iter().all(|d| d.severity != Severity::Error);
    for d in pdiags {
        diags.push((DiagFile::Source, d));
    }

    let wants_lower = target != Target::Check;
    if wants_lower && g1_clean && paths_clean {
        let (ldiags, naive) = crate::codegen::lower::lower(c, info, &env, &report);
        let lower_clean = ldiags.iter().all(|d| d.severity != Severity::Error);
        for d in ldiags {
            diags.push((DiagFile::Source, d));
        }
        // Everything downstream of lowering runs only on a clean lowering: a
        // failed lowering has no trustworthy leaves to certify, assemble, or
        // print, so `result.leaves.is_some()` means "lowered clean".
        if lower_clean {
            let leaves: Vec<LoweredLeaf> = naive
                .iter()
                .map(crate::codegen::optimize::optimize)
                .collect();

            // Certify whenever we report verdicts (--certify) or emit a fundable
            // address (--address/--lock/--verify): never hand back an
            // uncertified address.
            let certify_mode = target == Target::Certify;
            let funding = target == Target::Fund;
            if certify_mode || funding {
                let marker = [0xAAu8; 64];
                let oracle = |_pk: &[u8], s: &[u8]| s == marker.as_slice();
                let ctx = crate::verify::interp::Context {
                    locktime: 0,
                    sequence: 0xffff_fffe,
                    tx_version: 2,
                    verify_sig: &oracle,
                };
                let reports =
                    crate::verify::certify::certify(c, info, &env, &naive, &leaves, &marker, &ctx);
                result.gate = Some(gate_decision(
                    &reports,
                    opts.allow_unproven,
                    funding,
                    &leaves,
                ));
                result.certification = Some(reports);
            }

            // `gate_ok` is false only when a funding artifact was requested and
            // the gate refused it; a bare --cost never runs the gate, so it
            // assembles.
            let needs_assembly = matches!(target, Target::Fund | Target::Cost);
            let gate_ok = result.gate.as_ref().is_none_or(|g| g.may_proceed);
            if needs_assembly && gate_ok {
                match crate::output::taproot::assemble_contract(c, &env, &leaves) {
                    Err(d) => {
                        for di in d {
                            diags.push((DiagFile::Source, di));
                        }
                    }
                    Ok(out) => {
                        if target == Target::Cost {
                            result.costs =
                                Some(crate::cost::analyze(info, &env, &leaves, &out.assembled));
                        }
                        let address = crate::output::bech32m::encode_p2tr(
                            opts.hrp,
                            &out.assembled.output_key,
                        );
                        let lockfile = crate::output::lockfile::render(
                            source, args_src, info, &env, &leaves, &out, &address,
                        );
                        result.assembled = Some(Assembled {
                            output: out,
                            address,
                            lockfile,
                        });
                    }
                }
            }
            result.leaves = Some(leaves);
        }
    }

    // Proven facts are surfaced only when the interval engine ran clean (the
    // driver's `--report` precondition).
    if g1_clean {
        result.facts = Some((report, paths));
    }
}

/// The fail-closed gate, as a pure decision (no rendering).
///
/// `may_proceed` folds in all three rules, in the driver's precedence:
/// a divergence blocks unconditionally; otherwise an unproven leaf blocks unless
/// `allow_unproven`; and (for a funding target) a coverage gap always blocks.
/// Callers render the per-leaf verdicts and notes from the [`LeafReport`]s and
/// these fields; this function is the only place the decision is made.
pub fn gate_decision(
    reports: &[LeafReport],
    allow_unproven: bool,
    funding: bool,
    leaves: &[LoweredLeaf],
) -> GateOutcome {
    let mut divergence = false;
    let mut unproven = 0usize;
    for r in reports {
        match r.status.assurance() {
            Assurance::Proven => {}
            Assurance::Unproven => unproven += 1,
            Assurance::Divergence => divergence = true,
        }
    }
    // Fail-closed COVERAGE: every leaf that will be assembled into the address
    // MUST carry a certify report. The spend->leaf->report mapping is 1:1 by
    // construction, but the gate must not TRUST that implicitly -- an uncovered
    // leaf would be funded ungated. Only enforced for funding targets.
    let coverage_gap = funding
        && !leaves
            .iter()
            .all(|l| reports.iter().any(|r| r.name == l.name));

    // Refuse on any of: an active divergence, an unproven leaf without the
    // override, or a coverage gap on a funded leaf.
    let may_proceed = !(divergence || (unproven > 0 && !allow_unproven) || coverage_gap);

    GateOutcome {
        divergence,
        unproven,
        coverage_gap,
        may_proceed,
        funding,
    }
}

// --- JSON serialization of a CompileResult (the structured output a web IDE
// consumes). Built on the zero-dependency `json::Json` tree + `json::to_string`.

fn jstr(s: impl Into<String>) -> Json {
    Json::Str(s.into())
}

fn jobj(fields: Vec<(&str, Json)>) -> Json {
    Json::Object(
        fields
            .into_iter()
            .map(|(k, v)| (k.to_string(), v))
            .collect(),
    )
}

fn hex_of(bytes: &[u8]) -> String {
    let mut s = String::with_capacity(bytes.len() * 2);
    for b in bytes {
        s.push(char::from_digit((b >> 4) as u32, 16).unwrap_or('?'));
        s.push(char::from_digit((b & 0xf) as u32, 16).unwrap_or('?'));
    }
    s
}

/// The realized taptree topology, as a nested object an embedder can draw. A
/// `branch` has `left`/`right` children; a `leaf` carries its array `index`, the
/// spend `name`, and its `depth` (= sibling-hash count). Mirrors the build-order
/// of [`crate::output::taproot::LeafTree`] (the commitment itself sorts each branch).
fn tree_to_json(t: &crate::output::taproot::LeafTree, names: &[String], depths: &[usize]) -> Json {
    use crate::output::taproot::LeafTree;
    match t {
        LeafTree::Leaf(i) => jobj(vec![
            ("kind", jstr("leaf")),
            ("index", Json::Int(*i as i128)),
            ("name", jstr(names.get(*i).cloned().unwrap_or_default())),
            (
                "depth",
                Json::Int(depths.get(*i).copied().unwrap_or(0) as i128),
            ),
        ]),
        LeafTree::Branch(l, r) => jobj(vec![
            ("kind", jstr("branch")),
            ("left", tree_to_json(l, names, depths)),
            ("right", tree_to_json(r, names, depths)),
        ]),
    }
}

/// The full taproot output as data: the internal/output keys, the tweak, the
/// merkle root, the NUMS disclosure, the tree topology, and per-leaf tapleaf
/// hash + merkle path + control block. Everything an interactive taptree (or an
/// independent verifier) needs. All bytes are big-endian hex.
fn taproot_to_json(out: &crate::output::taproot::ContractOutput, result: &CompileResult) -> Json {
    let a = &out.assembled;
    let names: Vec<String> = result
        .leaves
        .as_ref()
        .map(|ls| ls.iter().map(|l| l.name.clone()).collect())
        .unwrap_or_default();
    let depths: Vec<usize> = a.leaves.iter().map(|l| l.path.len()).collect();

    let mut fields: Vec<(&str, Json)> = vec![
        ("internalKey", jstr(hex_of(&a.internal_key))),
        ("outputKey", jstr(hex_of(&a.output_key))),
        ("tweak", jstr(hex_of(&a.tweak))),
        ("parity", Json::Int(i128::from(a.parity))),
    ];
    if let Some(root) = &a.merkle_root {
        fields.push(("merkleRoot", jstr(hex_of(root))));
    }
    if let Some(r) = &out.nums_r {
        fields.push(("numsR", jstr(hex_of(r))));
    }
    if let Some(tree) = &out.tree {
        fields.push(("tree", tree_to_json(tree, &names, &depths)));
    }

    let leaf_arr: Vec<Json> = a
        .leaves
        .iter()
        .enumerate()
        .map(|(i, l)| {
            jobj(vec![
                ("name", jstr(names.get(i).cloned().unwrap_or_default())),
                ("tapleafHash", jstr(hex_of(&l.hash))),
                ("depth", Json::Int(l.path.len() as i128)),
                (
                    "merklePath",
                    Json::Array(l.path.iter().map(|h| jstr(hex_of(h))).collect()),
                ),
                ("controlBlock", jstr(hex_of(&l.control_block))),
            ])
        })
        .collect();
    fields.push(("leaves", Json::Array(leaf_arr)));

    jobj(fields)
}

fn sev_str(s: Severity) -> &'static str {
    match s {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Note => "note",
        Severity::Help => "help",
    }
}

/// Serialize a [`CompileResult`] to a standard JSON string for an embedder (a
/// web IDE). Diagnostics carry both the byte span and 1-based line/col (computed
/// from `source`/`args` via [`LineIndex`]), so the frontend can place editor
/// squiggles without re-parsing. Optional artifacts appear only when the
/// pipeline produced them: an ABSENT key means "not produced" (cleaner for a JS
/// consumer than a null, which this JSON subset does not have anyway).
pub fn result_to_json(result: &CompileResult, source: &str, args: Option<&str>) -> String {
    let src_index = LineIndex::new(source);
    let args_index = args.map(LineIndex::new);

    let mut top: Vec<(String, Json)> = Vec::new();
    top.push((
        "ok".to_string(),
        Json::Bool(
            result.internal_error.is_none()
                && result.error_count() == 0
                && result.contract.is_some()
                && !result.gate_failed(),
        ),
    ));
    if let Some(e) = &result.internal_error {
        top.push(("internalError".to_string(), jstr(e.clone())));
    }
    top.push((
        "boundExterns".to_string(),
        Json::Int(result.bound_externs as i128),
    ));

    let diags: Vec<Json> = result
        .diagnostics
        .iter()
        .map(|(file, d)| {
            let (fname, idx, text): (&str, &LineIndex, &str) = match file {
                DiagFile::Source => ("source", &src_index, source),
                DiagFile::Args => (
                    "args",
                    args_index.as_ref().unwrap_or(&src_index),
                    args.unwrap_or(source),
                ),
            };
            diag_to_json(fname, d, idx, text)
        })
        .collect();
    top.push(("diagnostics".to_string(), Json::Array(diags)));

    if let Some(asm) = &result.assembled {
        top.push(("address".to_string(), jstr(asm.address.clone())));
        top.push((
            "outputKey".to_string(),
            jstr(hex_of(&asm.output.assembled.output_key)),
        ));
        top.push(("lockfile".to_string(), jstr(asm.lockfile.clone())));
        top.push(("taproot".to_string(), taproot_to_json(&asm.output, result)));
    }

    if let Some(leaves) = &result.leaves {
        let ls: Vec<Json> = leaves
            .iter()
            .map(|l| {
                jobj(vec![
                    ("name", jstr(l.name.clone())),
                    ("bytes", Json::Int(l.script.len() as i128)),
                    ("hex", jstr(hex_of(&l.script))),
                    ("asm", jstr(crate::codegen::script::asm(&l.ops))),
                    (
                        "witnessOrder",
                        Json::Array(l.witness_order.iter().map(|w| jstr(w.clone())).collect()),
                    ),
                ])
            })
            .collect();
        top.push(("leaves".to_string(), Json::Array(ls)));
    }

    if let Some(reports) = &result.certification {
        top.push((
            "certification".to_string(),
            Json::Array(reports.iter().map(cert_to_json).collect()),
        ));
    }
    if let Some(g) = &result.gate {
        top.push((
            "gate".to_string(),
            jobj(vec![
                ("mayProceed", Json::Bool(g.may_proceed)),
                ("divergence", Json::Bool(g.divergence)),
                ("unproven", Json::Int(g.unproven as i128)),
                ("coverageGap", Json::Bool(g.coverage_gap)),
                ("funding", Json::Bool(g.funding)),
            ]),
        ));
    }

    if let Some(costs) = &result.costs {
        let cs: Vec<Json> = costs
            .iter()
            .map(|sc| {
                jobj(vec![
                    ("name", jstr(sc.name.clone())),
                    ("scriptBytes", Json::Int(sc.script_bytes as i128)),
                    ("controlBytes", Json::Int(sc.control_bytes as i128)),
                    ("witnessBytes", Json::Int(sc.witness_elem_bytes as i128)),
                    ("maxWitnessWeight", Json::Int(sc.max_witness_weight as i128)),
                    ("maxInputWeight", Json::Int(sc.max_input_weight as i128)),
                ])
            })
            .collect();
        top.push(("costs".to_string(), Json::Array(cs)));
    }

    if let Some((report, paths)) = &result.facts {
        let lets: Vec<Json> = report
            .lets
            .iter()
            .map(|(spend, name, iv)| {
                jobj(vec![
                    ("spend", jstr(spend.clone())),
                    ("name", jstr(name.clone())),
                    ("lo", Json::Int(iv.lo)),
                    ("hi", Json::Int(iv.hi)),
                ])
            })
            .collect();
        let path_arr: Vec<Json> = paths
            .paths
            .iter()
            .map(|p| {
                let params: Vec<Json> = p
                    .params
                    .iter()
                    .map(|param| {
                        jobj(vec![
                            ("name", jstr(param.name.clone())),
                            ("ty", jstr(param.ty.to_string())),
                            ("class", jstr(format!("{:?}", param.class))),
                        ])
                    })
                    .collect();
                let mut fields = vec![
                    ("name", jstr(p.name.clone())),
                    ("kind", jstr(p.kind.to_string())),
                    ("open", Json::Bool(p.open)),
                    ("params", Json::Array(params)),
                    (
                        "obligations",
                        Json::Array(p.obligations.iter().map(|o| jstr(o.clone())).collect()),
                    ),
                ];
                if let Some((k, n)) = p.threshold {
                    fields.push((
                        "threshold",
                        jobj(vec![
                            ("required", Json::Int(k)),
                            ("of", Json::Int(n as i128)),
                        ]),
                    ));
                }
                jobj(fields)
            })
            .collect();
        top.push((
            "facts".to_string(),
            jobj(vec![
                ("lets", Json::Array(lets)),
                ("paths", Json::Array(path_arr)),
            ]),
        ));
    }

    crate::json::to_string(&Json::Object(top))
}

fn diag_to_json(file: &str, d: &Diagnostic, idx: &LineIndex, text: &str) -> Json {
    let start = idx.line_col(text, d.span.start);
    let end = idx.line_col(text, d.span.end);
    let notes: Vec<Json> = d
        .notes
        .iter()
        .map(|n| {
            jobj(vec![
                ("severity", jstr(sev_str(n.severity))),
                ("message", jstr(n.message.clone())),
            ])
        })
        .collect();
    let mut fields = vec![
        ("file", jstr(file)),
        ("code", jstr(d.code)),
        ("severity", jstr(sev_str(d.severity))),
        ("message", jstr(d.message.clone())),
        (
            "span",
            jobj(vec![
                ("start", Json::Int(d.span.start as i128)),
                ("end", Json::Int(d.span.end as i128)),
            ]),
        ),
        (
            "start",
            jobj(vec![
                ("line", Json::Int(start.line as i128)),
                ("col", Json::Int(start.col as i128)),
            ]),
        ),
        (
            "end",
            jobj(vec![
                ("line", Json::Int(end.line as i128)),
                ("col", Json::Int(end.col as i128)),
            ]),
        ),
        ("notes", Json::Array(notes)),
    ];
    if let Some(label) = &d.label {
        fields.push(("label", jstr(label.clone())));
    }
    jobj(fields)
}

fn cert_to_json(r: &LeafReport) -> Json {
    use crate::verify::certify::{CertStatus, ProvenKind};
    let assurance = match r.status.assurance() {
        Assurance::Proven => "proven",
        Assurance::Unproven => "unproven",
        Assurance::Divergence => "divergence",
    };
    let status = match &r.status {
        CertStatus::Certified { checked } => jobj(vec![
            ("kind", jstr("certified")),
            ("checked", Json::Int(*checked as i128)),
        ]),
        CertStatus::Proven {
            kind: ProvenKind::FullInt { var, breakpoints },
        } => jobj(vec![
            ("kind", jstr("proven_int")),
            ("var", jstr(var.clone())),
            ("cells", Json::Int(*breakpoints as i128)),
        ]),
        CertStatus::Proven {
            kind: ProvenKind::FullSymbolic { atoms },
        } => jobj(vec![
            ("kind", jstr("proven_symbolic")),
            ("atoms", Json::Int(*atoms as i128)),
        ]),
        CertStatus::Proven {
            kind: ProvenKind::T2OnlySymbolic { atoms, t1_reason },
        } => jobj(vec![
            ("kind", jstr("t2_only_symbolic")),
            ("atoms", Json::Int(*atoms as i128)),
            ("t1Reason", jstr(t1_reason.clone())),
        ]),
        CertStatus::Differential { checked, reason } => jobj(vec![
            ("kind", jstr("differential")),
            ("checked", Json::Int(*checked as i128)),
            ("reason", jstr(reason.clone())),
        ]),
        CertStatus::BoundedChecked { checked, lo, hi } => jobj(vec![
            ("kind", jstr("bounded_checked")),
            ("checked", Json::Int(*checked as i128)),
            ("lo", Json::Int(*lo)),
            ("hi", Json::Int(*hi)),
        ]),
        CertStatus::Unbounded { reason } => jobj(vec![
            ("kind", jstr("unbounded")),
            ("reason", jstr(reason.clone())),
        ]),
        CertStatus::Failed { detail } => jobj(vec![
            ("kind", jstr("divergence")),
            ("detail", jstr(detail.clone())),
        ]),
    };
    jobj(vec![
        ("name", jstr(r.name.clone())),
        ("assurance", jstr(assurance)),
        ("status", status),
    ])
}
