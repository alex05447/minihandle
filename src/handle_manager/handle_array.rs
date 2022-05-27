use {
    crate::*,
    static_assertions::*,
    std::{
        iter::IntoIterator,
        ops::{Deref, DerefMut},
    },
};

type ObjectIndex = HandleIndex;

/// Associates a single `T` value with a [`Handle`].
///
/// Internally stores `T` objects in a dense array,
/// remapping the [`Handle`]'s index to object index through an indirection array.
///
/// Derefs to a `[T]` slice.
///
/// Also known as a pool, or a typed arena (TODO: consider renaming?).
#[derive(Clone)]
pub struct HandleArray<T> {
    /// All handles returned by this handle array share this metadata value.
    metadata: HandleMetadata,
    /// Manages the handles returned by this handle array, corresponding to indices in the `indices` indirection array.
    handle_manager: HandleManager,
    /// Maps the handle's index to the object's actual index in the `array`;
    /// thus may contain holes filled with `INVALID_INDEX`.
    indices: Vec<ObjectIndex>,
    /// Actual dense object storage.
    array: Vec<T>,
}

/// NOTE: this can never be confused with a valid handle index, because [`MAX_HANDLES`] is less than [`INVALID_INDEX`].
const INVALID_INDEX: HandleIndex = HandleIndex::MAX;

const_assert!(MAX_HANDLES < INVALID_INDEX);

impl<T> HandleArray<T> {
    /// Creates a new [`HandleArray`].
    ///
    /// `min_num_free_indices` - see [`HandleManager::new`].
    ///
    /// All handles returned by this [`HandleArray`] will share the `metadata` value.
    pub fn new(metadata: HandleMetadata, min_num_free_indices: HandleIndex) -> Self {
        Self {
            metadata,
            handle_manager: HandleManager::new(min_num_free_indices),
            indices: Vec::new(),
            array: Vec::new(),
        }
    }

    /// Inserts the `value` in the array, returning the [`Handle`] which may be used to
    /// [`get`](HandleArray::get) / [`get_mut`](HandleArray::get_mut) / [`remove`](HandleArray::remove) it later.
    ///
    /// # Panics
    ///
    /// Panics if this would insert more than [`MAX_HANDLES`] values.
    pub fn insert(&mut self, value: T) -> Handle {
        let handle = self.handle_manager.create(self.metadata);
        let index = unsafe { debug_unwrap(handle.index(), "invalid handle") } as usize;

        let object_index = self.array.len() as ObjectIndex;

        if index == self.indices.len() {
            debug_assert_eq!(index, self.indices.len());
            self.indices.push(object_index);
        } else {
            debug_assert!(index < self.indices.len());
            let object_index_ = unsafe { self.indices.get_unchecked_mut(index) };
            debug_assert!(*object_index_ == INVALID_INDEX);
            *object_index_ = object_index;
        }

        self.array.push(value);

        handle
    }

    /// Inserts the `value` in the array, returning the [`Handle`] which may be used to
    /// [`get`](HandleArray::get) / [`get_mut`](HandleArray::get_mut) / [`remove`](HandleArray::remove) it later,
    /// and the mutable reference to the inserted `value`.
    ///
    /// # Panics
    ///
    /// Panics if this would insert more than [`MAX_HANDLES`] values.
    pub fn insert_entry(&mut self, value: T) -> (Handle, &mut T) {
        let handle = self.insert(value);

        (handle, unsafe {
            debug_unwrap(self.array.last_mut(), "empty object array")
        })
    }

    /// Returns `true` if the [`Handle`] is valid - i.e. it was previously
    /// returned by [`insert`](HandleArray::insert) / [`insert_entry`](HandleArray::insert_entry)
    /// by this [`HandleArray`] and has not been [`removed`](HandleArray::remove) yet.
    pub fn is_valid(&self, handle: Handle) -> bool {
        self.is_valid_impl(handle).is_some()
    }

    /// If the [`Handle`] [`is_valid`](HandleArray::is_valid), returns the reference to the `value` which was [`inserted`](HandleArray::insert)
    /// when this handle was returned by this [`HandleArray`].
    /// Else returns `None`.
    pub fn get(&self, handle: Handle) -> Option<&T> {
        self.is_valid_impl(handle).map(|(_, object_index)| {
            debug_assert!((object_index as usize) < self.array.len());
            unsafe { self.array.get_unchecked(object_index as usize) }
        })
    }

    /// If the [`Handle`] [`is_valid`](HandleArray::is_valid), returns the mutable reference to the `value` which was [`inserted`](HandleArray::insert)
    /// when this handle was returned by this [`HandleArray`].
    /// Else returns `None`.
    pub fn get_mut(&mut self, handle: Handle) -> Option<&mut T> {
        self.is_valid_impl(handle).map(move |(_, object_index)| {
            debug_assert!((object_index as usize) < self.array.len());
            unsafe { self.array.get_unchecked_mut(object_index as usize) }
        })
    }

    /// If the [`Handle`] [`is_valid`](HandleArray::is_valid), removes and returns the `value` which was [`inserted`](HandleArray::insert)
    /// when this handle was returned by this [`HandleArray`], and invalidates the [`Handle`].
    /// Else returns `None`.
    pub fn remove(&mut self, handle: Handle) -> Option<T> {
        self.is_valid_impl(handle).map(|(index, object_index)| {
            debug_assert!((object_index as usize) < self.array.len());

            self.handle_manager.destroy_by_index(index);

            // Move the last object to the free slot and patch its index in the index array.
            *unsafe { self.indices.get_unchecked_mut(index as usize) } = INVALID_INDEX;

            debug_assert!(self.array.len() > 0);
            let last_object_index = (self.array.len() - 1) as ObjectIndex;

            if object_index != last_object_index {
                self.indices
                    .iter_mut()
                    .find_map(|index| (*index == last_object_index).then(|| *index = object_index));
            }

            unsafe { swap_remove(&mut self.array, object_index as usize) }
        })
    }

    /// Returns the current number of valid [`Handle`]'s / values, [`inserted`](HandleArray::insert) in this [`HandleArray`].
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns `true` if [`len`](HandleArray::len) returns `0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`HandleArray`], removing all values and invalidating the allocated handles
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    pub fn clear(&mut self) {
        self.handle_manager.clear();
        self.indices.clear();
        self.array.clear();
    }

    /// Returns the tuple of (handle index, object index) for a valid `handle`.
    fn is_valid_impl(&self, handle: Handle) -> Option<(HandleIndex, ObjectIndex)> {
        handle
            .metadata()
            .and_then(|metadata| {
                (metadata == self.metadata)
                    .then(|| self.handle_manager.is_valid_impl(handle))
                    .flatten()
            })
            .map(|index| {
                debug_assert!((index as usize) < self.indices.len());
                (index, *unsafe {
                    self.indices.get_unchecked(index as usize)
                })
            })
    }
}

impl<T> Deref for HandleArray<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.array.deref()
    }
}

impl<T> DerefMut for HandleArray<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.array.deref_mut()
    }
}

impl<T> IntoIterator for HandleArray<T> {
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
