use super::handle::Handle;
use super::handle_manager::HandleManager;

/// Associates a single `T` value with a [`Handle`].
///
/// Internally stores `T` objects in a dense array,
/// remapping the [`Handle`]'s index to object index through an indirection table.
///
/// [`Handle`]: struct.Handle.html
pub struct HandleArray<T> {
    metadata: u16,
    handle_manager: HandleManager,
    indices: Vec<u32>,
    array: Vec<T>,
}

impl<T> HandleArray<T> {
    /// Create a new [`HandleArray`].
    ///
    /// `min_num_free_indices` - this many [`Handle`]'s need to be freed before
    /// the oldest freed index will be reused with a new generation (sequence).
    ///
    /// All handles returned by this [`HandleArray`] will share the `metadata` value.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn new(metadata: u16, min_num_free_indices: u32) -> Self {
        Self {
            metadata,
            handle_manager: HandleManager::new(min_num_free_indices),
            indices: Vec::new(),
            array: Vec::new(),
        }
    }

    /// Inserts the `value` in the array, returning the [`Handle`] which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later.
    ///
    /// # Panics
    ///
    /// Panics if more than `std::u32::MAX` objects are inserted.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    pub fn insert(&mut self, value: T) -> Handle {
        let handle = self.handle_manager.create(self.metadata);
        let index = handle.index().expect("Invalid handle.") as usize;

        if index >= self.indices.len() {
            self.indices.resize(index + 1, std::u32::MAX);
        }

        self.indices[index] = self.array.len() as u32;
        self.array.push(value);

        handle
    }

    /// Returns `true` if the [`Handle`] is valid - i.e. it was previously returned by [`insert`]
    /// and has not been [`remove`]'ed yet.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`insert`]: #method.insert
    /// [`remove`]: #method.remove
    pub fn is_valid(&self, handle: Handle) -> bool {
        self.handle_manager.is_valid(handle)
    }

    /// If the [`Handle`] [`is_valid`], returns the reference to the `value` which was [`insert`]'ed
    /// when this handle was returned.
    /// Else returns `None`.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`insert`]: #method.insert
    pub fn get(&self, handle: Handle) -> Option<&T> {
        if !self.handle_manager.is_valid(handle) {
            None
        } else {
            let index = handle.index().expect("Invalid handle.") as usize;
            debug_assert!(index < self.indices.len());

            let object_index = self.indices[index];
            debug_assert!((object_index as usize) < self.array.len());

            Some(&self.array[object_index as usize])
        }
    }

    /// If the [`Handle`] [`is_valid`], returns the mutable reference to the `value` which was [`insert`]'ed
    /// when this handle was returned.
    /// Else returns `None`.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`insert`]: #method.insert
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        if !self.handle_manager.is_valid(handle) {
            None
        } else {
            let index = handle.index().expect("Invalid handle.") as usize;
            debug_assert!(index < self.indices.len());

            let object_index = self.indices[index];
            debug_assert!((object_index as usize) < self.array.len());

            Some(&mut self.array[object_index as usize])
        }
    }

    /// If the [`Handle`] [`is_valid`], removes and returns the `value` which was [`insert`]'ed
    /// when this handle was returned, and invalidates the handle.
    /// Else returns `None`.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`insert`]: #method.insert
    pub fn remove(&mut self, handle: Handle) -> Option<T> {
        if !self.handle_manager.is_valid(handle) {
            None
        } else {
            let index = handle.index().expect("Invalid handle.") as usize;
            debug_assert!(index < self.indices.len());

            let object_index = self.indices[index];
            debug_assert!((object_index as usize) < self.array.len());

            let destroyed = self.handle_manager.destroy(handle);
            debug_assert!(destroyed);

            // Move the last object to the free slot and patch its index in the index array.
            self.indices[index] = std::u32::MAX;

            let last_object_index = (self.array.len() - 1) as u32;

            if object_index != last_object_index {
                let last_index = self
                    .indices
                    .iter()
                    .position(|index| *index == last_object_index)
                    .unwrap();
                self.indices[last_index] = object_index;
            }

            Some(self.array.swap_remove(object_index as usize))
        }
    }

    /// Returns the current number of valid [`insert`]'ed [`Handle`]'s / `T`'s in this [`HandleArray`]
    ///
    /// [`insert`]: #method.insert
    /// [`Handle`]: struct.Handle.html
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns `true` if [`len`] returns `0`.
    ///
    /// [`len`]: #method.len
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<T> std::ops::Deref for HandleArray<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.array.deref()
    }
}

impl<T> std::ops::DerefMut for HandleArray<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.array.deref_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_array() {
        let mut ha = HandleArray::<u32>::new(0, 0);

        assert_eq!(ha.len(), 0);

        let handle_0 = ha.insert(7);

        assert_eq!(ha.len(), 1);

        assert!(ha.is_valid(handle_0));

        assert_eq!(*ha.get(handle_0).unwrap(), 7);

        let handle_1 = ha.insert(9);

        assert_eq!(ha.len(), 2);

        assert!(ha.is_valid(handle_1));

        assert_eq!(*ha.get(handle_1).unwrap(), 9);

        for val in ha.iter() {
            assert!(*val == 7 || *val == 9)
        }

        let value_1 = ha.get_mut(handle_1).unwrap();

        *value_1 = 42;

        assert_eq!(*ha.get(handle_1).unwrap(), 42);

        for val in ha.iter() {
            assert!(*val == 7 || *val == 42)
        }

        for (_idx, val) in ha.iter_mut().enumerate() {
            *val += 1;
        }

        let removed_0 = ha.remove(handle_0);

        assert_eq!(removed_0.unwrap(), 8);

        assert_eq!(ha.len(), 1);

        assert!(!ha.is_valid(handle_0));

        let removed_1 = ha.remove(handle_1);

        assert_eq!(removed_1.unwrap(), 43);

        assert_eq!(ha.len(), 0);

        assert!(!ha.is_valid(handle_1));
    }
}
