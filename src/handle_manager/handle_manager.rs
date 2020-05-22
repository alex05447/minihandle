use std::collections::VecDeque;

use crate::{Generation, Handle, Index, Metadata, MAX_HANDLES};

/// Creates, validates and destroys [`Handle`]'s, a.k.a. weak references, a.k.a. generational indices.
///
/// [`Handle`]: struct.Handle.html
pub struct HandleManager {
    min_num_free_indices: Index,
    num_handles: Index,
    generations: Vec<Generation>,
    free_indices: VecDeque<Index>,
}

impl HandleManager {
    /// Creates a new [`HandleManager`].
    ///
    /// `min_num_free_indices` - this many [`Handle`]'s need to be freed before
    /// the oldest freed index will be reused with a new generation (sequence).
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn new(min_num_free_indices: Index) -> Self {
        Self {
            min_num_free_indices: min_num_free_indices.min(MAX_HANDLES),
            num_handles: 0,
            generations: Vec::new(),
            free_indices: VecDeque::new(),
        }
    }

    /// Creates a new unique [`Handle`] with associated `metadata`.
    ///
    /// NOTE: the [`HandleManager`] does not keep track of the [`metadata`] of created handles,
    /// so it cannot disambiguate between the handles with the same [`index`] and [`generation`] parts, but different [`metadata`].
    ///
    /// # Panics
    ///
    /// Panics if this would allocate more than [`MAX_HANDLES`] handles.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`MAX_HANDLES`]: constant.MAX_HANDLES.html
    /// [`metadata`]: struct.Handle.html#method.metadata
    /// [`index`]: struct.Handle.html#method.index
    /// [`generation`]: struct.Handle.html#method.generation
    pub fn create(&mut self, metadata: Metadata) -> Handle {
        let index = if self.free_indices.len() > self.min_num_free_indices as usize {
            self.free_indices.pop_front().unwrap()
        } else {
            assert!(
                self.generations.len() < MAX_HANDLES as usize,
                "Attempted to allocate more than MAX_HANDLES handles."
            );

            self.generations.push(0);
            (self.generations.len() - 1) as Index
        };

        self.num_handles += 1;

        debug_assert!((index as usize) < self.generations.len());
        let generation = *unsafe { self.generations.get_unchecked(index as usize) };

        Handle::new(index, generation, metadata)
    }

    /// Returns `true` if the [`handle`] is valid - i.e. it was previously [`created`] by this [`HandleManager`]
    /// and has not been [`destroyed`] yet.
    ///
    /// NOTE: the [`HandleManager`] does not keep track of the [`metadata`] of created handles,
    /// so it cannot disambiguate between the handles with the same [`index`] and [`generation`] parts, but different [`metadata`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`created`]: #method.create
    /// [`HandleManager`]: struct.HandleManager.html
    /// [`destroyed`]: #method.destroy
    /// [`metadata`]: struct.Handle.html#method.metadata
    /// [`index`]: struct.Handle.html#method.index
    /// [`generation`]: struct.Handle.html#method.generation
    pub fn is_valid(&self, handle: Handle) -> bool {
        self.is_valid_impl(handle).is_some()
    }

    /// Destoys the [`handle`], i.e. makes [`is_valid`] by this [`HandleManager`] return `false` for it.
    /// Returns `true` if the [`handle`] was [`valid`] and was destroyed; else return `false`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`HandleManager`]: struct.HandleManager.html
    /// [`valid`]: #method.is_valid
    pub fn destroy(&mut self, handle: Handle) -> bool {
        if let Some(index) = self.is_valid_impl(handle) {
            if index as usize >= self.generations.len() {
                false
            } else {
                let generation = unsafe { self.generations.get_unchecked_mut(index as usize) };
                *generation = generation.wrapping_add(1);
                self.free_indices.push_back(index);
                debug_assert!(self.num_handles > 0);
                self.num_handles -= 1;
                true
            }
        } else {
            false
        }
    }

    /// Returns the current number of valid [`handles`], [`created`] by this [`HandleManager`].
    ///
    /// [`handles`]: struct.Handle.html
    /// [`created`]: #method.create
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn len(&self) -> u32 {
        self.num_handles
    }

    /// Returns `true` if [`len`] returns `0`.
    ///
    /// [`len`]: #method.len
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`HandleManager`], invalidating the allocated handles
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    ///
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn clear(&mut self) {
        self.num_handles = 0;
        self.generations.clear();
        self.free_indices.clear();
    }

    pub(crate) fn is_valid_impl(&self, handle: Handle) -> Option<Index> {
        if let Some((index, generation, _)) = handle.unwrap() {
            if index as usize >= self.generations.len() {
                None
            } else {
                if *unsafe { self.generations.get_unchecked(index as usize) } == generation {
                    Some(index)
                } else {
                    None
                }
            }
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_manager() {
        let mut hm = HandleManager::new(0);
        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        let handle_0 = hm.create(7);

        assert!(hm.is_valid(handle_0));
        assert_eq!(hm.len(), 1);
        assert!(!hm.is_empty());

        assert_eq!(handle_0.index().unwrap(), 0);
        assert_eq!(handle_0.generation().unwrap(), 0);
        assert_eq!(handle_0.metadata().unwrap(), 7);
        assert_eq!(handle_0.unwrap(), Some((0, 0, 7)));

        let handle_1 = hm.create(9);

        assert!(hm.is_valid(handle_0));
        assert!(hm.is_valid(handle_1));
        assert_eq!(hm.len(), 2);
        assert!(!hm.is_empty());

        assert_eq!(handle_1.index().unwrap(), 1);
        assert_eq!(handle_1.generation().unwrap(), 0);
        assert_eq!(handle_1.metadata().unwrap(), 9);
        assert_eq!(handle_1.unwrap(), Some((1, 0, 9)));

        assert!(hm.destroy(handle_0));
        assert!(!hm.destroy(handle_0));

        assert!(!hm.is_valid(handle_0));
        assert!(hm.is_valid(handle_1));
        assert_eq!(hm.len(), 1);
        assert!(!hm.is_empty());

        let handle_2 = hm.create(21);

        assert!(!hm.is_valid(handle_0));
        assert!(hm.is_valid(handle_1));
        assert!(hm.is_valid(handle_2));
        assert_eq!(hm.len(), 2);
        assert!(!hm.is_empty());

        assert_eq!(handle_2.index().unwrap(), 0);
        assert_eq!(handle_2.generation().unwrap(), 1);
        assert_eq!(handle_2.metadata().unwrap(), 21);
        assert_eq!(handle_2.unwrap(), Some((0, 1, 21)));

        assert!(hm.destroy(handle_1));

        assert!(!hm.destroy(handle_0));
        assert!(!hm.destroy(handle_1));

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(hm.is_valid(handle_2));
        assert_eq!(hm.len(), 1);
        assert!(!hm.is_empty());

        let handle_3 = hm.create(42);

        assert_eq!(hm.len(), 2);

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(hm.is_valid(handle_2));
        assert!(hm.is_valid(handle_3));

        assert_eq!(handle_3.index().unwrap(), 1);
        assert_eq!(handle_3.generation().unwrap(), 1);
        assert_eq!(handle_3.metadata().unwrap(), 42);
        assert_eq!(handle_3.unwrap(), Some((1, 1, 42)));

        assert!(hm.destroy(handle_2));

        assert!(!hm.destroy(handle_0));
        assert!(!hm.destroy(handle_1));
        assert!(!hm.destroy(handle_2));

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(hm.is_valid(handle_3));
        assert_eq!(hm.len(), 1);
        assert!(!hm.is_empty());

        assert!(hm.destroy(handle_3));

        assert!(!hm.destroy(handle_0));
        assert!(!hm.destroy(handle_1));
        assert!(!hm.destroy(handle_2));
        assert!(!hm.destroy(handle_3));

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());
    }

    #[test]
    fn handle_manager_with_free_index_queue() {
        let mut hm = HandleManager::new(4);
        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        let handle_0 = hm.create(0);
        let handle_1 = hm.create(0);
        let handle_2 = hm.create(0);
        let handle_3 = hm.create(0);
        let handle_4 = hm.create(0);

        assert_eq!(hm.len(), 5);
        assert!(!hm.is_empty());

        assert!(hm.destroy(handle_0));
        assert!(hm.destroy(handle_1));
        assert!(hm.destroy(handle_2));
        assert!(hm.destroy(handle_3));
        assert!(hm.destroy(handle_4));

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
        assert!(!hm.is_valid(handle_4));

        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        let handle_5 = hm.create(0);

        assert_eq!(hm.len(), 1);
        assert!(!hm.is_empty());

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
        assert!(!hm.is_valid(handle_4));
        assert!(hm.is_valid(handle_5));

        assert_eq!(handle_5.index().unwrap(), 0); // <- index `0` reused.
        assert_eq!(handle_5.generation().unwrap(), 1);
        assert_eq!(handle_5.metadata().unwrap(), 0);
        assert_eq!(handle_5.unwrap(), Some((0, 1, 0)));

        assert!(hm.destroy(handle_5));
        assert!(!hm.destroy(handle_5));

        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
        assert!(!hm.is_valid(handle_4));
        assert!(!hm.is_valid(handle_5));
    }

    #[test]
    fn clear() {
        let mut hm = HandleManager::new(0);
        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        let handle_0 = hm.create(0);

        assert!(hm.is_valid(handle_0));
        assert_eq!(hm.len(), 1);

        hm.clear();

        assert!(!hm.is_valid(handle_0));
        assert_eq!(hm.len(), 0);
        assert!(hm.is_empty());

        let handle_1 = hm.create(0);

        assert!(hm.is_valid(handle_0)); // <- valid again
        assert!(hm.is_valid(handle_1));
        assert_eq!(hm.len(), 1);
    }
}
