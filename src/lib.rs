#[macro_use]
extern crate static_assertions;

mod handle_manager;

#[cfg(feature = "index")]
mod index_manager;

pub use handle_manager::{
    Generation, Handle, HandleArray, HandleManager, Index, Metadata, MAX_HANDLES,
};

#[cfg(feature = "index")]
pub use index_manager::{IndexArray, IndexManager};
