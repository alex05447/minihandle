//! Simple Rust crate for managing handles, a.k.a. weak references, a.k.a. generational indices;
//! as well as creating pools of values referred to by such handles.
//!
//! See [http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html](http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html)

mod handle_manager;
mod util;

#[cfg(feature = "index")]
mod index_manager;

pub use handle_manager::*;

#[cfg(feature = "index")]
pub use index_manager::*;

pub(crate) use util::*;
