mod handle;
mod handle_array;
mod handle_manager;

pub use {
    handle::{HandleGeneration, Handle, HandleIndex, HandleMetadata, MAX_HANDLES},
    handle_array::HandleArray,
    handle_manager::HandleManager
};