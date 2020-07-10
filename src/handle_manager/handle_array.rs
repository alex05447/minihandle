use crate::{Handle, HandleManager, HandleIndex, HandleMetadata};

/// Associates a single `T` value with a [`Handle`].
///
/// Internally stores `T` objects in a dense array,
/// remapping the [`Handle`]'s index to object index through an indirection array.
///
/// [`Handle`]: struct.Handle.html
pub struct HandleArray<T> {
    /// All handles returned by this handle array share this metadata value.
    metadata: HandleMetadata,
    /// Manages the handles returned by this handle array, corresponding to indices in the `indices` indirection array.
    handle_manager: HandleManager,
    /// Maps the handle's index to the object's actual index in the `array`;
    /// thus may contain holes filled with `INVALID_INDEX`.
    indices: Vec<HandleIndex>,
    /// Actual dense object storage.
    array: Vec<T>,
}

impl<T> HandleArray<T> {
    const INVALID_INDEX: HandleIndex = HandleIndex::MAX;

    /// Creates a new [`HandleArray`].
    ///
    /// `min_num_free_indices` - this many [`Handle`]'s need to be freed before
    /// the oldest freed index will be reused with a new generation (sequence).
    ///
    /// All handles returned by this [`HandleArray`] will share the `metadata` value.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn new(metadata: HandleMetadata, min_num_free_indices: HandleIndex) -> Self {
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
    /// Panics if this would insert more than [`MAX_HANDLES`] values.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    /// [`MAX_HANDLES`]: constant.MAX_HANDLES.html
    pub fn insert(&mut self, value: T) -> Handle {
        let handle = self.handle_manager.create(self.metadata);
        let index = handle.index().expect("invalid handle") as usize;

        if index >= self.indices.len() {
            self.indices.resize(index + 1, Self::INVALID_INDEX);
        }

        debug_assert!(unsafe { *self.indices.get_unchecked(index) == Self::INVALID_INDEX });
        *unsafe { self.indices.get_unchecked_mut(index) } = self.array.len() as HandleIndex;
        self.array.push(value);

        handle
    }

    /// Inserts the `value` in the array, returning the [`Handle`] which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later,
    /// and the mutable reference to the inserted `value`.
    ///
    /// # Panics
    ///
    /// Panics if this would insert more than [`MAX_HANDLES`] values.
    ///
    /// [`Handle`]: struct.Handle.html
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    /// [`MAX_HANDLES`]: constant.MAX_HANDLES.html
    pub fn insert_entry(&mut self, value: T) -> (Handle, &mut T) {
        let handle = self.insert(value);

        (handle, self.array.last_mut().unwrap())
    }

    /// Returns `true` if the [`handle`] is valid - i.e. it was previously returned by [`insert`] / [`insert_entry`] by this [`HandleArray`]
    /// and has not been [`removed`] yet.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`insert`]: #method.insert
    /// [`insert_entry`]: #method.insert_entry
    /// [`HandleArray`]: struct.HandleArray.html
    /// [`removed`]: #method.remove
    pub fn is_valid(&self, handle: Handle) -> bool {
        self.is_valid_impl(handle).is_some()
    }

    /// If the [`handle`] [`is_valid`], returns the reference to the `value` which was [`inserted`]
    /// when this handle was returned by this [`HandleArray`].
    /// Else returns `None`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn get(&self, handle: Handle) -> Option<&T> {
        if let Some(index) = self.is_valid_impl(handle) {
            debug_assert!((index as usize) < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index as usize) };

            debug_assert!((object_index as usize) < self.array.len());
            Some(unsafe { self.array.get_unchecked(object_index as usize) })
        } else {
            None
        }
    }

    /// If the [`handle`] [`is_valid`], returns the mutable reference to the `value` which was [`inserted`]
    /// when this handle was returned by this [`HandleArray`].
    /// Else returns `None`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        if let Some(index) = self.is_valid_impl(handle) {
            debug_assert!((index as usize) < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index as usize) };

            debug_assert!((object_index as usize) < self.array.len());
            Some(unsafe { self.array.get_unchecked_mut(object_index as usize) })
        } else {
            None
        }
    }

    /// If the [`handle`] [`is_valid`], removes and returns the `value` which was [`inserted`]
    /// when this handle was returned by this [`HandleArray`], and invalidates the [`handle`].
    /// Else returns `None`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn remove(&mut self, handle: Handle) -> Option<T> {
        if let Some(index) = self.is_valid_impl(handle) {
            debug_assert!((index as usize) < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index as usize) };

            debug_assert!((object_index as usize) < self.array.len());

            let destroyed = self.handle_manager.destroy(handle);
            debug_assert!(destroyed);

            // Move the last object to the free slot and patch its index in the index array.
            *unsafe { self.indices.get_unchecked_mut(index as usize) } = Self::INVALID_INDEX;

            debug_assert!(self.array.len() > 0);
            let last_object_index = (self.array.len() - 1) as HandleIndex;

            if object_index != last_object_index {
                for index in self.indices.iter_mut() {
                    if *index == last_object_index {
                        *index = object_index;
                        break;
                    }
                }
            }

            Some(self.array.swap_remove(object_index as usize))
        } else {
            None
        }
    }

    /// Returns the current number of valid [`handles`] / values, [`inserted`] in this [`HandleArray`].
    ///
    /// [`handles`]: struct.Handle.html
    /// [`inserted`]: #method.insert
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

    /// Clears the [`HandleArray`], removing all values and invalidating the allocated handles
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    ///
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn clear(&mut self) {
        self.handle_manager.clear();
        self.indices.clear();
        self.array.clear();
    }

    fn is_valid_impl(&self, handle: Handle) -> Option<HandleIndex> {
        if let Some(metadata) = handle.metadata() {
            if metadata != self.metadata {
                return None;
            }
        } else {
            return None;
        }

        self.handle_manager.is_valid_impl(handle)
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

impl<T> std::iter::IntoIterator for HandleArray<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        self.array.into_iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn handle_array() {
        let mut ha = HandleArray::<u32>::new(0, 0);

        assert_eq!(ha.len(), 0);
        assert!(ha.is_empty());

        let handle_0 = ha.insert(7);

        assert!(ha.is_valid(handle_0));
        assert_eq!(ha.len(), 1);
        assert!(!ha.is_empty());

        assert_eq!(ha.get(handle_0), Some(&7));

        let handle_1 = ha.insert(9);

        assert!(ha.is_valid(handle_0));
        assert!(ha.is_valid(handle_1));
        assert_eq!(ha.len(), 2);
        assert!(!ha.is_empty());

        assert_eq!(ha.get(handle_1), Some(&9));

        for val in ha.iter() {
            assert!(*val == 7 || *val == 9)
        }

        let value_1 = ha.get_mut(handle_1).unwrap();

        *value_1 = 42;

        assert_eq!(ha.get(handle_1), Some(&42));

        for val in ha.iter() {
            assert!(*val == 7 || *val == 42)
        }

        for val in ha.iter_mut() {
            *val += 1;
        }

        for val in ha.iter() {
            assert!(*val == 8 || *val == 43)
        }

        let removed_0 = ha.remove(handle_0);
        assert_eq!(removed_0, Some(8));

        assert!(!ha.is_valid(handle_0));
        assert!(ha.is_valid(handle_1));
        assert_eq!(ha.len(), 1);
        assert!(!ha.is_empty());

        let removed_1 = ha.remove(handle_1);
        assert_eq!(removed_1, Some(43));

        assert!(!ha.is_valid(handle_0));
        assert!(!ha.is_valid(handle_1));
        assert_eq!(ha.len(), 0);
        assert!(ha.is_empty());
    }

    #[test]
    fn into_iter() {
        let mut ha = HandleArray::<u32>::new(0, 0);

        ha.insert(0);
        ha.insert(1);
        ha.insert(2);
        ha.insert(3);

        for (idx, val) in ha.into_iter().enumerate() {
            assert_eq!(idx, val as usize);
        }

        //ha.insert(4);
    }

    #[test]
    fn iter() {
        let mut ha = HandleArray::<u32>::new(0, 0);

        ha.insert(0);
        ha.insert(1);
        ha.insert(2);
        ha.insert(3);

        for (idx, val) in ha.iter().enumerate() {
            assert_eq!(idx, *val as usize);
        }

        ha.insert(4);
    }
}
