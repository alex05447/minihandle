use std::collections::VecDeque;

use super::handle::Handle;

/// Creates, validates and destroys [`Handle`]'s, a.k.a. weak references, a.k.a. generational indices.
///
/// [`Handle`]: struct.Handle.html
pub struct HandleManager {
    min_num_free_indices: u32,
    num_handles: u32,
    generations: Vec<u16>,
    free_indices: VecDeque<u32>,
}

impl HandleManager {
    /// Creates a new [`HandleManager`].
    ///
    /// `min_num_free_indices` - this many [`Handle`]'s need to be freed before
    /// the oldest freed index will be reused with a new generation (sequence).
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn new(min_num_free_indices: u32) -> Self {
        Self {
            min_num_free_indices,
            num_handles: 0,
            generations: Vec::new(),
            free_indices: VecDeque::new(),
        }
    }

    /// Creates a new unique [`Handle`] with associated `metadata`.
    ///
    /// # Panics
    ///
    /// Panics if more than `std::u32::MAX` handles are allocated.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn create(&mut self, metadata: u16) -> Handle {
        let index = if self.free_indices.len() as u32 > self.min_num_free_indices {
            self.free_indices.pop_front().unwrap() as usize
        } else {
            assert!(
                self.generations.len() < std::u32::MAX as usize,
                "More than u32::MAX handles allocated."
            );

            self.generations.push(0);
            (self.generations.len() - 1) as usize
        };

        self.num_handles += 1;

        debug_assert!(index < self.generations.len());
        let generation = *unsafe { self.generations.get_unchecked(index) };

        Handle::new(index as u32, generation, metadata)
    }

    /// Returns `true` if the [`Handle`] is valid - i.e. it was previously [`created`] by this [`HandleManager`]
    /// and has not been [`destroyed`] yet.
    ///
    /// [`created`]: #method.create
    /// [`Handle`]: struct.Handle.html
    /// [`destroyed`]: #method.destroy
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn is_valid(&self, handle: Handle) -> bool {
        if let Some(index) = handle.index() {
            let index = index as usize;
            if index >= self.generations.len() {
                false
            } else {
                let generation = handle.generation().expect("Invalid handle.");
                *unsafe { self.generations.get_unchecked(index) } == generation
            }
        } else {
            false
        }
    }

    /// Destoys the `handle`, i.e. makes [`is_valid`] by this [`HandleManager`] return `false` for it.
    /// Returns `true` if the `handle` was [`valid`] and was destroyed; else return `false`.
    ///
    /// [`is_valid`]: #method.is_valid
    /// [`valid`]: #method.is_valid
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn destroy(&mut self, handle: Handle) -> bool {
        if let Some(index) = handle.index() {
            let index = index as usize;

            if index >= self.generations.len() {
                false
            } else {
                *unsafe { self.generations.get_unchecked_mut(index) } += 1;
                self.free_indices.push_back(index as u32);
                self.num_handles -= 1;
                true
            }
        } else {
            false
        }
    }

    /// Returns the current number of valid [`created`] [`Handle`]'s by this [`HandleManager`].
    ///
    /// [`created`]: #method.create
    /// [`Handle`]: struct.Handle.html
    /// [`HandleManager`]: struct.HandleManager.html
    pub fn len(&self) -> u32 {
        self.num_handles
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
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_manager() {
        let mut hm = HandleManager::new(0);

        assert_eq!(hm.len(), 0);

        let handle_0 = hm.create(7);

        assert_eq!(hm.len(), 1);

        assert!(hm.is_valid(handle_0));

        assert_eq!(handle_0.index().unwrap(), 0);
        assert_eq!(handle_0.generation().unwrap(), 0);
        assert_eq!(handle_0.metadata().unwrap(), 7);

        let handle_1 = hm.create(9);

        assert_eq!(hm.len(), 2);

        assert!(hm.is_valid(handle_1));

        assert_eq!(handle_1.index().unwrap(), 1);
        assert_eq!(handle_1.generation().unwrap(), 0);
        assert_eq!(handle_1.metadata().unwrap(), 9);

        assert!(hm.destroy(handle_0));

        assert_eq!(hm.len(), 1);

        assert!(!hm.is_valid(handle_0));
        assert!(hm.is_valid(handle_1));

        let handle_2 = hm.create(21);

        assert_eq!(hm.len(), 2);

        assert!(hm.is_valid(handle_2));

        assert_eq!(handle_2.index().unwrap(), 0);
        assert_eq!(handle_2.generation().unwrap(), 1);
        assert_eq!(handle_2.metadata().unwrap(), 21);

        assert!(hm.destroy(handle_1));

        assert_eq!(hm.len(), 1);

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(hm.is_valid(handle_2));

        let handle_3 = hm.create(42);

        assert_eq!(hm.len(), 2);

        assert!(hm.is_valid(handle_3));

        assert_eq!(handle_3.index().unwrap(), 1);
        assert_eq!(handle_3.generation().unwrap(), 1);
        assert_eq!(handle_3.metadata().unwrap(), 42);

        assert!(hm.destroy(handle_2));

        assert_eq!(hm.len(), 1);

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(hm.is_valid(handle_3));

        assert!(hm.destroy(handle_3));

        assert_eq!(hm.len(), 0);

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
    }

    #[test]
    fn handle_manager_with_free_index_queue() {
        let mut hm = HandleManager::new(4);

        assert_eq!(hm.len(), 0);

        let handle_0 = hm.create(0);
        let handle_1 = hm.create(0);
        let handle_2 = hm.create(0);
        let handle_3 = hm.create(0);
        let handle_4 = hm.create(0);

        assert_eq!(hm.len(), 5);

        assert!(hm.destroy(handle_0));
        assert!(hm.destroy(handle_1));
        assert!(hm.destroy(handle_2));
        assert!(hm.destroy(handle_3));
        assert!(hm.destroy(handle_4));

        assert_eq!(hm.len(), 0);

        let handle_5 = hm.create(0);

        assert_eq!(hm.len(), 1);

        assert!(hm.is_valid(handle_5));

        assert_eq!(handle_5.index().unwrap(), 0); // <- index `0` reused.
        assert_eq!(handle_5.generation().unwrap(), 1);
        assert_eq!(handle_5.metadata().unwrap(), 0);

        assert!(hm.destroy(handle_5));

        assert_eq!(hm.len(), 0);

        assert!(!hm.is_valid(handle_0));
        assert!(!hm.is_valid(handle_1));
        assert!(!hm.is_valid(handle_2));
        assert!(!hm.is_valid(handle_3));
        assert!(!hm.is_valid(handle_4));
        assert!(!hm.is_valid(handle_5));
    }
}
