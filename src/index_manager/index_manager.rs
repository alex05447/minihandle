use num_traits::{PrimInt, Unsigned};

/// Like [`HandleManager`], but uses a simple index instead of a
/// generational handle.
///
/// Intended for use cases where the user has full control over index lifetime
/// and requires just a simple unique index allocator the `IndexManager` provides.
///
/// [`HandleManager`]: struct.HandleManager.html
#[derive(Clone)]
pub struct IndexManager<I>
where
    I: PrimInt + Unsigned,
{
    num_indices: u32,
    next_index: I,
    free_indices: Vec<I>,
}

impl<I> IndexManager<I>
where
    I: PrimInt + Unsigned,
{
    /// Create a new `IndexManager`.
    ///
    /// [`IndexManager`]: struct.IndexManager.html
    pub fn new() -> Self {
        Self {
            num_indices: 0,
            next_index: I::zero(),
            free_indices: Vec::new(),
        }
    }

    /// Creates a new index.
    ///
    /// # Panics
    ///
    /// Panics if enough indices are allocated to overflow the underlying index type.
    pub fn create(&mut self) -> I {
        if let Some(index) = self.free_indices.pop() {
            return index;
        }

        let index = self.next_index;
        self.next_index = self
            .next_index
            .checked_add(&I::one())
            .expect("Index overflow.");

        self.num_indices += 1;

        index
    }

    /// Frees the `index`.
    ///
    /// It's up to the user to ensure the `index` is valid and unique.
    ///
    /// NOTE - this only checks the same `index` is not freed more than once in debug configuration.
    pub fn destroy(&mut self, index: I) {
        debug_assert!(!self.free_indices.contains(&index));
        debug_assert!(self.num_indices > 0);

        self.num_indices -= 1;
        self.free_indices.push(index);
    }

    /// Returns the current number of valid [`create`]'d indices by this [`IndexManager`].
    ///
    /// [`create`]: #method.create
    /// [`IndexManager`]: struct.IndexManager.html
    pub fn len(&self) -> u32 {
        self.num_indices
    }

    /// Clears the [`IndexManager`], invalidating the allocated indices
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    ///
    /// [`IndexManager`]: struct.IndexManager.html
    pub fn clear(&mut self) {
        self.num_indices = 0;
        self.next_index = I::zero();
        self.free_indices.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_manager() {
        let mut im = IndexManager::<u32>::new();

        let index_0 = im.create();
        assert_eq!(index_0, 0);

        let index_1 = im.create();
        assert_eq!(index_1, 1);

        im.destroy(index_0);

        let index_2 = im.create();
        assert_eq!(index_2, 0);

        im.destroy(index_1);

        let index_3 = im.create();
        assert_eq!(index_3, 1);
    }
}
