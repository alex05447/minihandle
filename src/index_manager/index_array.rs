use num_traits::{FromPrimitive};

use crate::{IndexManager, Index};

/// Like [`HandleArray`], but uses a simple [`index`] instead of a
/// generational handle.
///
/// Intended for use cases where the user has full control over index lifetime
/// and requires just a simple array index indirection the `IndexArray` provides.
///
/// [`HandleArray`]: struct.HandleArray.html
/// [`index`]: trait.Index.html
pub struct IndexArray<T, I>
where
    I: Index + FromPrimitive,
{
    /// Manages the indices returned by this index array, corresponding to indices in the `indices` indirection array.
    index_manager: IndexManager<I>,
    /// Maps the public index to the object's actual index in the `array`;
    /// thus may contain holes filled with `I::max_value()`.
    indices: Vec<I>,
    array: Vec<T>,
}

impl<T, I> IndexArray<T, I>
where
    I: Index + FromPrimitive,
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

    /// Inserts the `value` in the array, returning the [`index`] which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later.
    ///
    /// # Panics
    ///
    /// Panics if this would insert enough objects to overflow the underlying [`index`] type.
    ///
    /// [`index`]: trait.Index.html
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    pub fn insert(&mut self, value: T) -> I {
        let index = self.index_manager.create();
        let index_usize = index.to_usize().unwrap();

        if index_usize >= self.indices.len() {
            self.indices.resize(index_usize + 1, I::max_value());
        }

        debug_assert!(unsafe { *self.indices.get_unchecked(index_usize) == I::max_value() });
        *unsafe { self.indices.get_unchecked_mut(index_usize) } =
            I::from_usize(self.array.len()).unwrap();
        self.array.push(value);

        index
    }

    /// Inserts the `value` in the array, returning the [`index`] which may be used to
    /// [`get`] / [`get_mut`] / [`remove`] it later,
    /// and the mutable reference to the inserted `value`.
    ///
    /// # Panics
    ///
    /// Panics if this would insert enough objects to overflow the underlying [`index`] type.
    ///
    /// [`index`]: trait.Index.html
    /// [`get`]: #method.get
    /// [`get_mut`]: #method.get_mut
    /// [`remove`]: #method.remove
    pub fn insert_entry(&mut self, value: T) -> (I, &mut T) {
        let index = self.insert(value);

        (index, self.array.last_mut().unwrap())
    }

    /// Returns `true` if the [`index`] is valid - i.e. it was previously returned by [`insert`] / [`insert_entry`] by this [`IndexArray`]
    /// and has not been [`removed`] yet.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`] will be considered valid.
    ///
    /// [`index`]: trait.Index.html
    /// [`insert`]: #method.insert
    /// [`insert_entry`]: #method.insert_entry
    /// [`IndexArray`]: struct.IndexArray.html
    /// [`removed`]: #method.remove
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn is_valid(&self, index: I) -> bool {
        self.index_manager.is_valid(index)
    }

    /// If the [`index`] [`is_valid`], returns the reference to the `value` which was [`inserted`]
    /// when this handle was returned by this [`IndexArray`].
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`] will be considered valid.
    ///
    /// [`index`]: trait.Index.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`IndexArray`]: struct.IndexArray.html
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn get(&self, index: I) -> Option<&T> {
        if self.is_valid(index) {
            let index_usize = index.to_usize().unwrap();

            debug_assert!(index_usize < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index_usize) };

            let object_index_usize = object_index.to_usize().unwrap();
            debug_assert!(object_index_usize < self.array.len());

            Some(unsafe { self.array.get_unchecked(object_index_usize) })
        } else {
            None
        }
    }

    /// If the [`index`] [`is_valid`], returns the reference to the `value` which was [`inserted`]
    /// when this handle was returned by this [`IndexArray`].
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`] will be considered valid.
    ///
    /// [`index`]: trait.Index.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`IndexArray`]: struct.IndexArray.html
    /// [`HandleArray`]: struct.HandleArray.html
    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        if self.is_valid(index) {
            let index_usize = index.to_usize().unwrap();

            debug_assert!(index_usize < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index_usize) };

            let object_index_usize = object_index.to_usize().unwrap();

            debug_assert!(object_index_usize < self.array.len());
            Some(unsafe { self.array.get_unchecked_mut(object_index_usize) })
        } else {
            None
        }
    }

    /// If the [`index`] [`is_valid`], removes and returns the `value` which was [`inserted`]
    /// when this handle was returned by this [`IndexArray`], and invalidates the [`index`].
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`] will be considered valid.
    ///
    /// [`index`]: trait.Index.html
    /// [`handle`]: struct.Handle.html
    /// [`is_valid`]: #method.is_valid
    /// [`inserted`]: #method.insert
    /// [`IndexArray`]: struct.IndexArray.html
    pub fn remove(&mut self, index: I) -> Option<T> {
        if self.is_valid(index) {
            let index_usize = index.to_usize().unwrap();

            debug_assert!(index_usize < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index_usize) };

            let object_index_usize = object_index.to_usize().unwrap();

            debug_assert!(object_index_usize < self.array.len());

            let destroyed = self.index_manager.destroy(index);
            debug_assert!(destroyed);

            // Move the last object to the free slot and patch its index in the index array.
            *unsafe { self.indices.get_unchecked_mut(index_usize) } = I::max_value();

            debug_assert!(self.array.len() > 0);
            let last_object_index = I::from_usize(self.array.len() - 1).unwrap();

            if object_index != last_object_index {
                for index in self.indices.iter_mut() {
                    if *index == last_object_index {
                        *index = object_index;
                        break;
                    }
                }
            }

            Some(self.array.swap_remove(object_index_usize))
        } else {
            None
        }
    }

    /// Returns the current number of valid indices / values, [`inserted`] in this [`IndexArray`].
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

    /// Clears the [`IndexArray`], removing all values and invalidating the allocated indices
    /// (but only until they are allocated again).
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
    I: Index + FromPrimitive,
{
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.array.deref()
    }
}

impl<T, I> std::ops::DerefMut for IndexArray<T, I>
where
    I: Index + FromPrimitive,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.array.deref_mut()
    }
}

impl<T, I> std::iter::IntoIterator for IndexArray<T, I>
where
    I: Index + FromPrimitive,
{
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
    fn index_array() {
        let mut ia = IndexArray::<u32, u8>::new();

        assert_eq!(ia.len(), 0);

        let index_0 = ia.insert(7);

        assert!(ia.is_valid(index_0));
        assert_eq!(ia.len(), 1);

        assert_eq!(ia.get(index_0), Some(&7));

        let index_1 = ia.insert(9);

        assert!(ia.is_valid(index_0));
        assert!(ia.is_valid(index_1));
        assert_eq!(ia.len(), 2);

        assert_eq!(ia.get(index_1), Some(&9));

        for val in ia.iter() {
            assert!(*val == 7 || *val == 9)
        }

        let value_1 = ia.get_mut(index_1).unwrap();

        *value_1 = 42;

        assert_eq!(ia.get(index_1), Some(&42));

        for val in ia.iter() {
            assert!(*val == 7 || *val == 42)
        }

        for val in ia.iter_mut() {
            *val += 1;
        }

        for val in ia.iter() {
            assert!(*val == 8 || *val == 43)
        }

        let removed_0 = ia.remove(index_0);
        assert_eq!(removed_0, Some(8));

        assert!(!ia.is_valid(index_0));
        assert!(ia.is_valid(index_1));
        assert_eq!(ia.len(), 1);

        let index_2 = ia.insert(1); // <- reuses index `0`.

        assert!(ia.is_valid(index_0)); // <- reuses index `0`.
        assert!(ia.is_valid(index_1));
        assert!(ia.is_valid(index_2));
        assert_eq!(ia.len(), 2);

        assert_eq!(ia.get(index_0), Some(&1)); // <- reuses index `0`.
        assert_eq!(ia.get(index_2), Some(&1));

        let removed_2 = ia.remove(index_2);
        assert_eq!(removed_2, Some(1));

        assert!(!ia.is_valid(index_0));
        assert!(ia.is_valid(index_1));
        assert!(!ia.is_valid(index_2));
        assert_eq!(ia.len(), 1);

        let removed_1 = ia.remove(index_1);
        assert_eq!(removed_1, Some(43));

        assert!(!ia.is_valid(index_0));
        assert!(!ia.is_valid(index_1));
        assert!(!ia.is_valid(index_2));
        assert_eq!(ia.len(), 0);
    }

    #[test]
    fn into_iter() {
        let mut ia = IndexArray::<u32, u8>::new();

        ia.insert(0);
        ia.insert(1);
        ia.insert(2);
        ia.insert(3);

        for (idx, val) in ia.into_iter().enumerate() {
            assert_eq!(idx, val as usize);
        }

        //ia.insert(4);
    }

    #[test]
    fn iter() {
        let mut ia = IndexArray::<u32, u8>::new();

        ia.insert(0);
        ia.insert(1);
        ia.insert(2);
        ia.insert(3);

        for (idx, val) in ia.iter().enumerate() {
            assert_eq!(idx, *val as usize);
        }

        ia.insert(4);
    }
}
