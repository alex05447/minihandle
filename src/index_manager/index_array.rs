use num_traits::{FromPrimitive, PrimInt, Unsigned};

use super::index_manager::IndexManager;

/// Like [`HandleArray`], but uses a simple index instead of a
/// generational handle.
///
/// Intended for use cases where the user has full control over index lifetime
/// and requires just a simple array index indirection the `IndexArray` provides.
///
/// [`HandleArray`]: struct.HandleArray.html
pub struct IndexArray<T, I>
where
    I: PrimInt + Unsigned + FromPrimitive,
{
    index_manager: IndexManager<I>,
    indices: Vec<I>,
    array: Vec<T>,
}

impl<T, I> IndexArray<T, I>
where
    I: PrimInt + Unsigned + FromPrimitive,
{
    /// Creates a new [`IndexArray`].
    ///
    /// [`IndexArray`]: struct.IndexArray.html
    pub fn new() -> Self {
        Self {
            index_manager: IndexManager::new(),
            indices: Vec::new(),
            array: Vec::new(),
        }
    }

    /// Inserts the `value` in the array, returning the index which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later.
    ///
    /// # Panics
    ///
    /// Panics if enough objects are inserted to overflow the underlying index type.
    ///
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    pub fn insert(&mut self, value: T) -> I {
        let index = self.index_manager.create();
        let index_usize = index.to_usize().unwrap();

        if index_usize >= self.indices.len() {
            self.indices.resize(index_usize + 1, I::max_value());
        }

        *unsafe { self.indices.get_unchecked_mut(index_usize) } =
            I::from_usize(self.array.len()).unwrap();
        self.array.push(value);

        index
    }

    /// Inserts the `value` in the array, returning the index which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later,
    /// and the mutable reference to the inserted `value`.
    ///
    /// # Panics
    ///
    /// Panics if enough objects are inserted to overflow the underlying index type.
    ///
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    pub fn insert_entry(&mut self, value: T) -> (I, &mut T) {
        let index = self.insert(value);

        (index, self.array.last_mut().unwrap())
    }

    /// Returns the reference to the `value` which was [`inserted`]
    /// when this index was returned.
    ///
    /// NOTE - this does not check whether the `index` is valid.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// [`inserted`]: #method.insert
    pub fn get(&self, index: I) -> &T {
        let index_usize = index.to_usize().unwrap();

        assert!(index_usize < self.indices.len(), "Index out of bounds.");
        let object_index = *unsafe { self.indices.get_unchecked(index_usize) };
        let object_index_usize = object_index.to_usize().unwrap();

        assert!(object_index_usize < self.array.len(), "Invalid index.");
        unsafe { self.array.get_unchecked(object_index_usize) }
    }

    /// Returns the mutable reference to the `value` which was [`inserted`]
    /// when this index was returned.
    ///
    /// NOTE - this does not check whether the `index` is valid.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// [`inserted`]: #method.insert
    pub fn get_mut(&mut self, index: I) -> &mut T {
        let index_usize = index.to_usize().unwrap();

        assert!(index_usize < self.indices.len(), "Index out of bounds.");
        let object_index = *unsafe { self.indices.get_unchecked(index_usize) };
        let object_index_usize = object_index.to_usize().unwrap();

        assert!(object_index_usize < self.array.len(), "Invalid index.");
        unsafe { self.array.get_unchecked_mut(object_index_usize) }
    }

    /// Removes and returns the `value` which was [`inserted`]
    /// when this index was returned, and frees the index.
    ///
    /// NOTE - this does not check whether the `index` is valid.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// [`inserted`]: #method.insert
    pub fn remove(&mut self, index: I) -> T {
        let index_usize = index.to_usize().unwrap();

        assert!(index_usize < self.indices.len(), "Index out of bounds.");
        let object_index = *unsafe { self.indices.get_unchecked(index_usize) };
        let object_index_usize = object_index.to_usize().unwrap();

        assert!(object_index_usize < self.array.len(), "Invalid index.");
        self.index_manager.destroy(index);

        // Move the last object to the free slot and patch its index in the index array.
        *unsafe { self.indices.get_unchecked_mut(index_usize) } = I::max_value();

        let last_object_index = I::from_usize(self.array.len() - 1).unwrap();

        if object_index != last_object_index {
            let last_index = self
                .indices
                .iter()
                .position(|index| *index == last_object_index)
                .unwrap();
            debug_assert!(last_index < self.indices.len());
            *unsafe { self.indices.get_unchecked_mut(last_index) } = object_index;
        }

        self.array.swap_remove(object_index_usize)
    }

    /// Returns the current number of [`inserted`] indices/objects in this [`IndexArray`].
    ///
    /// [`inserted`]: #method.insert
    /// [`IndexArray`]: struct.IndexArray.html
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns `true` if [`len`] returns `0`.
    ///
    /// [`len`]: #method.len
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`IndexArray`], removing all values.
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    ///
    /// [`IndexArray`]: struct.IndexArray.html
    pub fn clear(&mut self) {
        self.index_manager.clear();
        self.indices.clear();
        self.array.clear();
    }
}

impl<T, I> std::ops::Deref for IndexArray<T, I>
where
    I: PrimInt + Unsigned + FromPrimitive,
{
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.array.deref()
    }
}

impl<T, I> std::ops::DerefMut for IndexArray<T, I>
where
    I: PrimInt + Unsigned + FromPrimitive,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.array.deref_mut()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn index_array() {
        let mut ia = IndexArray::<u32, u8>::new();

        assert_eq!(ia.len(), 0);

        let index_0 = ia.insert(7);

        assert_eq!(ia.len(), 1);

        assert_eq!(*ia.get(index_0), 7);

        let index_1 = ia.insert(9);

        assert_eq!(ia.len(), 2);

        assert_eq!(*ia.get(index_1), 9);

        for val in ia.iter() {
            assert!(*val == 7 || *val == 9)
        }

        let value_1 = ia.get_mut(index_1);

        *value_1 = 42;

        assert_eq!(*ia.get(index_1), 42);

        for val in ia.iter() {
            assert!(*val == 7 || *val == 42)
        }

        for val in ia.iter_mut() {
            *val += 1;
        }

        let removed_0 = ia.remove(index_0);

        assert_eq!(removed_0, 8);

        assert_eq!(ia.len(), 1);

        let removed_1 = ia.remove(index_1);

        assert_eq!(removed_1, 43);

        assert_eq!(ia.len(), 0);
    }
}
