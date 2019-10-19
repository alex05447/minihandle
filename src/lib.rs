#[macro_use]
extern crate static_assertions;

mod handle_manager;
mod index_manager;

pub use handle_manager::{Handle, HandleArray, HandleManager};
pub use index_manager::IndexArray;
