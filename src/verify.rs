//! Per-compile certification: proving each spend path enforces its source,
//! the reference interpreter and decision procedure behind that proof, and the
//! witness satisfier.

pub mod certify;
pub mod decide;
pub mod interp;
pub mod satisfy;
