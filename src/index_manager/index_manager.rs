use num_traits::{FromPrimitive, PrimInt, Unsigned};

/// Trait for the index type used by the [`IndexManager`] - a primitive unsigned integer.
pub trait Index: PrimInt + Unsigned + FromPrimitive {}

impl<T: PrimInt + Unsigned + FromPrimitive> Index for T {}

/// Like [`HandleManager`](crate::HandleManager), but uses a simple [`index`](Index) instead of a
/// generational handle.
///
/// Intended for use cases where the user has full control over index lifetime
/// and requires just a simple unique index allocator the [`IndexManager`] provides.
#[derive(Clone)]
pub struct IndexManager<I: Index> {
    num_indices: I,
    next_index: I,
    free_indices: Vec<I>,
}

impl<I: Index> IndexManager<I> {
    /// Creates a new [`IndexManager`].
    pub fn new() -> Self {
        Self {
            num_indices: I::zero(),
            next_index: I::zero(),
            free_indices: Vec::new(),
        }
    }

    /// Allocates a new [`index`](Index), unique for this [`IndexManager`].
    ///
    /// # Panics
    ///
    /// Panics if enough indices are allocated to overflow the underlying [`index`](Index) type.
    pub fn create(&mut self) -> I {
        let index = if let Some(index) = self.free_indices.pop() {
            index
        } else {
            let index = self.next_index;
            self.next_index = self
                .next_index
                .checked_add(&I::one())
                .expect("index overflow");
            index
        };

        self.num_indices = self
            .num_indices
            .checked_add(&I::one())
            .expect("index overflow");

        index
    }

    /// Returns `true` if the [`index`](Index) is valid - i.e. it was previously [`created`](IndexManager::create) by this [`IndexManager`]
    /// and has not been [`destroyed`](IndexManager::destroy) yet.
    ///
    /// NOTE: unlike [`HandleManager`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn is_valid(&self, index: I) -> bool {
        (index < self.next_index) && !self.free_indices.contains(&index)
    }

    /// Destoys the [`index`](Index), i.e. makes [`is_valid`](IndexManager::is_valid) by this [`IndexManager`] return `false` for it.
    /// Returns `true` if the [`index`](Index) was [`valid`](IndexManager::is_valid) and was destroyed; else return `false`.
    ///
    /// NOTE: unlike [`HandleManager`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn destroy(&mut self, index: I) -> bool {
        if !self.is_valid(index) {
            false
        } else {
            self.destroy_impl(index);
            true
        }
    }

    /// Returns the current number of [`valid`](IndexManager::is_valid) indices, [`created`](IndexManager::create) by this [`IndexManager`].
    pub fn len(&self) -> I {
        self.num_indices
    }

    /// Returns `true` if [`len`](IndexManager::len) returns `0`.
    pub fn is_empty(&self) -> bool {
        self.len() == I::zero()
    }

    /// Clears the [`IndexManager`], invalidating the allocated indices
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    pub fn clear(&mut self) {
        self.num_indices = I::zero();
        self.next_index = I::zero();
        self.free_indices.clear();
    }

    /// The caller guarantees `index` is a valid index, confirmed by [`is_valid`](IndexManager::is_valid) immediately before.
    pub(crate) fn destroy_impl(&mut self, index: I) {
        debug_assert!(self.num_indices > I::zero());
        self.num_indices = self.num_indices - I::one();

        if self.num_indices == I::zero() {
            self.free_indices.clear();
            self.next_index = I::zero();
        } else {
            self.free_indices.push(index);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_manager() {
        let mut im = IndexManager::<u32>::new();
        assert_eq!(im.len(), 0);
        assert!(im.is_empty());

        let index_0 = im.create();
        assert_eq!(index_0, 0);

        assert!(im.is_valid(index_0));
        assert_eq!(im.len(), 1);

        let index_1 = im.create();
        assert_eq!(index_1, 1);

        assert!(im.is_valid(index_0));
        assert!(im.is_valid(index_1));
        assert_eq!(im.len(), 2);

        assert!(im.destroy(index_0));
        assert!(!im.destroy(index_0));

        assert!(!im.is_valid(index_0));
        assert!(im.is_valid(index_1));
        assert_eq!(im.len(), 1);

        let index_2 = im.create(); // <- index reused
        assert_eq!(index_2, 0);

        assert!(im.is_valid(index_0)); // <- valid again
        assert!(im.is_valid(index_1));
        assert!(im.is_valid(index_2));
        assert_eq!(im.len(), 2);

        assert!(im.destroy(index_1));
        assert!(!im.destroy(index_1));

        assert!(im.is_valid(index_0));
        assert!(!im.is_valid(index_1));
        assert!(im.is_valid(index_2));
        assert_eq!(im.len(), 1);

        let index_3 = im.create(); // <- index reused
        assert_eq!(index_3, 1);

        assert!(im.is_valid(index_0));
        assert!(im.is_valid(index_1)); // <- valid again
        assert!(im.is_valid(index_2));
        assert!(im.is_valid(index_3));
        assert_eq!(im.len(), 2);
    }

    #[test]
    fn clear() {
        let mut im = IndexManager::<u32>::new();
        assert_eq!(im.len(), 0);
        assert!(im.is_empty());

        let index_0 = im.create();
        assert_eq!(index_0, 0);

        assert!(im.is_valid(index_0));
        assert_eq!(im.len(), 1);

        im.clear();

        assert!(!im.is_valid(index_0));
        assert_eq!(im.len(), 0);
        assert!(im.is_empty());

        let index_1 = im.create(); // <- index reused
        assert_eq!(index_1, 0);

        assert!(im.is_valid(index_0)); // <- valid again
        assert!(im.is_valid(index_1));
        assert_eq!(im.len(), 1);
    }
}
