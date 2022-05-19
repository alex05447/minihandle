use {crate::*, std::collections::VecDeque};

/// Creates, validates and destroys [`Handle`]'s, a.k.a. weak references, a.k.a. generational indices.
pub struct HandleManager {
    min_num_free_indices: HandleIndex,
    num_handles: HandleIndex,
    generations: Vec<HandleGeneration>,
    free_indices: VecDeque<HandleIndex>,
}

impl HandleManager {
    /// Creates a new [`HandleManager`].
    ///
    /// `min_num_free_indices` - this many [`Handle`]'s need to be freed before
    /// the oldest freed index will be reused with a new generation (sequence).
    /// This helps with generation churn, preventing patological use cases from
    /// overflowing the generation counter for some inices much sooner than others.
    pub fn new(min_num_free_indices: HandleIndex) -> Self {
        Self {
            min_num_free_indices: min_num_free_indices.min(MAX_HANDLES),
            num_handles: 0,
            generations: Vec::new(),
            free_indices: VecDeque::new(),
        }
    }

    /// Creates a new unique [`Handle`] with associated `metadata`.
    ///
    /// NOTE: the [`HandleManager`] does not keep track of the [`metadata`](Handle::metadata) of created handles,
    /// so it cannot disambiguate between the handles with the same [`index`](Handle::index) and [`generation`](Handle::generation) parts,
    /// but different [`metadata`](Handle::metadata).
    ///
    /// # Panics
    ///
    /// Panics if this would allocate more than [`MAX_HANDLES`] handles.
    pub fn create(&mut self, metadata: HandleMetadata) -> Handle {
        let index = if self.free_indices.len() > self.min_num_free_indices as usize {
            unsafe {
                debug_unwrap(
                    self.free_indices.pop_front(),
                    "free index queue is not empty",
                )
            }
        } else {
            assert!(
                self.generations.len() < MAX_HANDLES as usize,
                "attempted to allocate more than MAX_HANDLES handles"
            );

            let index = self.generations.len() as _;
            self.generations.push(0);
            index
        };

        debug_assert!((index as usize) < self.generations.len());
        let generation = *unsafe { self.generations.get_unchecked(index as usize) };

        self.num_handles += 1;

        Handle::new(index, generation, metadata)
    }

    /// Returns `true` if the [`Handle`] is valid - i.e. it was previously [`created`](HandleManager::create) by this [`HandleManager`]
    /// and has not been [`destroyed`](HandleManager::destroy) yet.
    ///
    /// NOTE: the [`HandleManager`] does not keep track of the [`metadata`](Handle::metadata) of created handles,
    /// so it cannot disambiguate between the handles with the same [`index`](Handle::index) and [`generation`](Handle::generation) parts,
    /// but different [`metadata`](Handle::metadata).
    pub fn is_valid(&self, handle: Handle) -> bool {
        self.is_valid_impl(handle).is_some()
    }

    /// Destoys the [`Handle`], i.e. makes [`is_valid`](HandleManager::is_valid) by this [`HandleManager`] return `false` for it.
    /// Returns `true` if the [`Handle`] was valid and was destroyed; else return `false`.
    pub fn destroy(&mut self, handle: Handle) -> bool {
        let num_handles = &mut self.num_handles;
        let generations = &mut self.generations;
        let free_indices = &mut self.free_indices;

        handle
            .unwrap()
            .and_then(|(index, generation, _)| {
                generations
                    .get_mut(index as usize)
                    .and_then(|existing_generation| {
                        (*existing_generation == generation).then(|| (index, existing_generation))
                    })
            })
            .map(|(index, generation)| {
                Self::destroy_impl(index, num_handles, generation, free_indices)
            })
            .is_some()
    }

    /// Returns the current number of valid [`Handle`]'s, [`created`](HandleManager::create) by this [`HandleManager`].
    pub fn len(&self) -> u32 {
        self.num_handles
    }

    /// Returns `true` if [`len`](HandleManager::len) returns `0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`HandleManager`], invalidating the allocated handles
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    pub fn clear(&mut self) {
        self.num_handles = 0;
        self.generations.clear();
        self.free_indices.clear();
    }

    pub(crate) fn is_valid_impl(&self, handle: Handle) -> Option<HandleIndex> {
        handle.unwrap().and_then(|(index, generation, _)| {
            self.generations
                .get(index as usize)
                .and_then(|existing_generation| (*existing_generation == generation).then(|| index))
        })
    }

    /// Destroys a handle by its index.
    /// The caller guarantees `index` is a valid handle index, returned by [`is_valid_impl`](HandleManager::is_valid_impl) immediately before.
    pub(crate) fn destroy_by_index(&mut self, index: HandleIndex) {
        debug_assert!((index as usize) < self.generations.len());
        let generation = unsafe { self.generations.get_unchecked_mut(index as usize) };
        Self::destroy_impl(
            index,
            &mut self.num_handles,
            generation,
            &mut self.free_indices,
        )
    }

    fn destroy_impl(
        index: HandleIndex,
        num_handles: &mut HandleIndex,
        generation: &mut HandleGeneration,
        free_indices: &mut VecDeque<HandleIndex>,
    ) {
        *generation = generation.wrapping_add(1);
        free_indices.push_back(index);
        debug_assert!(*num_handles > 0);
        *num_handles -= 1;
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
