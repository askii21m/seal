//! `seal`, the Seal compiler.
//! A `.sl` contract goes through the safety checks, an optimized tapscript
//! pass, and finally a P2TR address.
//!
//! Golden corpus: `tests/corpus/*.sl`, which the compiler must stay green against.
//!
//! Pipeline:
//!   `syntax`     source text to a typed AST
//!   `analysis`   type checking, instantiation, interval and feasibility analysis
//!   `codegen`    lowering to tapscript and optimization
//!   `verify`     certifying each leaf against its source
//!   `output`     taproot assembly, address, and lockfile
//!   `compile`    drives the stages above and the fail-closed funding gate
//!
//! Engineering bar (this code touches real money):
//! - Totality: no component panics on any input; errors are diagnostics.
//! - Determinism: compilation is a pure function of
//!   (source, externs, target, compiler version). No HashMap iteration order,
//!   no time, no ambient randomness, anywhere, ever.
//! - Invariants are code: each component exports its invariant checker
//!   (e.g. [`syntax::lexer::verify_token_stream_invariants`]) and all tests hold it.

pub mod analysis;
pub mod codegen;
pub mod crypto;
pub mod output;
pub mod syntax;
pub mod verify;

pub mod compile;
pub mod cost;
pub mod diagnostics;
pub mod json;
