//! # minihandle
//!
//! Simple Rust crate for managing handles, a.k.a. weak references, a.k.a. generational indices;
//! as well as creating pools of values referred to by such handles.
//!
//! See [http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html](http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html)
//!
//! ## Features:
//!
//! `"index"` (disabled by default) - provides a simplified implementation of an index manager / array which doesn't handle the generation/sequence/cycle number.
//!
//! ## Dependencies:
//!
//! - [`static_assertions`](https://crates.io/crates/static_assertions)
//! - [`num-traits`](https://crates.io/crates/num-traits (optional, used by the `"index"` feature))
//! - path dependency on [`miniunchecked`](https://github.com/alex05447/miniunchecked) (TODO: Github dependency?)

mod handle_manager;
mod util;

#[cfg(feature = "index")]
mod index_manager;

pub use handle_manager::*;

#[cfg(feature = "index")]
pub use index_manager::*;

pub(crate) use util::*;
