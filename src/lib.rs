#[macro_use]
extern crate static_assertions;

mod handle_manager;

#[cfg(feature = "index")]
mod index_manager;

pub use handle_manager::{
    HandleGeneration, Handle, HandleArray, HandleManager, HandleIndex, HandleMetadata, MAX_HANDLES,
};

#[cfg(feature = "index")]
pub use index_manager::{IndexArray, IndexManager, Index};
