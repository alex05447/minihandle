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
    /// Creates a new `IndexManager`.
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
        let index = if self.free_indices.len() > 0 {
            self.free_indices.pop().unwrap()
        } else {
            let index = self.next_index;
            self.next_index = self
                .next_index
                .checked_add(&I::one())
                .expect("Index overflow.");
            index
        };

        self.num_indices = self.num_indices.checked_add(1).expect("Index overflow.");

        index
    }

    /// Returns `true` if the `index` is valid - i.e. it was previously [`created`] by this [`IndexManager`]
    /// and has not been [`destroyed`] yet.
    ///
    /// NOTE: unlike [`HandleManager`], this does not protect against the A-B-A problem -
    /// a reallocated index will be considered valid.
    ///
    /// [`created`]: #method.create
    /// [`Handle`]: struct.Handle.html
    /// [`destroyed`]: #method.destroy
    /// [`IndexManager`]: struct.IndexManager.html
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn is_valid(&self, index: I) -> bool {
        (index < self.next_index) && !self.free_indices.contains(&index)
    }

    /// Destoys the `index`, i.e. makes [`is_valid`] by this [`IndexManager`] return `false` for it.
    /// Returns `true` if the `handle` was [`valid`] and was destroyed; else return `false`.
    ///
    /// NOTE: unlike [`HandleManager`], this does not protect against the A-B-A problem -
    /// a reallocated index will be considered valid.
    ///
    /// [`is_valid`]: #method.is_valid
    /// [`valid`]: #method.is_valid
    /// [`IndexManager`]: struct.IndexManager.html
    pub fn destroy(&mut self, index: I) -> bool {
        if !self.is_valid(index) {
            false
        } else {
            debug_assert!(self.num_indices > 0);
            self.num_indices -= 1;

            if self.num_indices == 0 {
                self.free_indices.clear();
                self.next_index = I::zero();
            } else {
                self.free_indices.push(index);
            }

            true
        }
    }

    /// Returns the current number of valid [`created`] indices by this [`IndexManager`].
    ///
    /// [`created`]: #method.create
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
        assert!(im.is_valid(index_0));

        let index_1 = im.create();
        assert_eq!(index_1, 1);
        assert!(im.is_valid(index_0));
        assert!(im.is_valid(index_1));

        im.destroy(index_0);
        assert!(!im.is_valid(index_0));
        assert!(im.is_valid(index_1));

        let index_2 = im.create();
        assert_eq!(index_2, 0);
        assert!(im.is_valid(index_0));
        assert!(im.is_valid(index_1));
        assert!(im.is_valid(index_2));

        im.destroy(index_1);
        assert!(im.is_valid(index_0));
        assert!(!im.is_valid(index_1));
        assert!(im.is_valid(index_2));

        let index_3 = im.create();
        assert_eq!(index_3, 1);
        assert!(im.is_valid(index_0));
        assert!(im.is_valid(index_1));
        assert!(im.is_valid(index_2));
        assert!(im.is_valid(index_3));
    }
}
