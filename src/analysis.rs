//! Semantic analysis: type checking, instantiation, interval and feasibility
//! reasoning, and the policy limits each leaf must respect.

pub mod consteval;
pub mod intervals;
pub mod limits;
pub mod paths;
pub mod sema;
