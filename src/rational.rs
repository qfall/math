//! This module contains the type [`Q`] for rationals with arbitrary length and
//! constructions over it.

mod mat_q;
mod poly_over_q;
mod q;

pub use mat_q::MatQ;
pub use poly_over_q::PolyOverQ;
pub use q::Q;
