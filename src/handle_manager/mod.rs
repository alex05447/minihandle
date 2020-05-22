mod handle;
mod handle_array;
mod handle_manager;

pub use handle::{Generation, Handle, Index, Metadata, MAX_HANDLES};
pub use handle_array::HandleArray;
pub use handle_manager::HandleManager;
