use {
    crate::*,
    std::{
        iter::IntoIterator,
        ops::{Deref, DerefMut},
    },
};

/// Like [`HandleArray`], but uses a simple [`index`](Index) instead of a
/// generational handle.
///
/// Internally stores `T` objects in a dense array,
/// remapping the [`index`](Index) to object index through an indirection array.
///
/// Derefs to a `[T]` slice.
///
/// Intended for use cases where the user has full control over index lifetime
/// and requires just a simple array index indirection the [`IndexArray`] provides.
pub struct IndexArray<T, I>
where
    I: Index,
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
    I: Index,
{
    // Needs `Bounded::max_value()` to be `const`.
    //const INVALID_INDEX: I = I::max_value();

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

    /// Inserts the `value` in the array, returning the [`index`](Index) which may be used to
    /// [`get`](IndexArray::get) / [`get_mut`](IndexArray::get_mut) / [`remove`](IndexArray::remove) it later.
    ///
    /// # Panics
    ///
    /// Panics if this would insert enough objects to overflow the underlying [`index`](Index) type.
    pub fn insert(&mut self, value: T) -> I {
        let index = self.index_manager.create();
        let index_usize = index.to_usize().expect("index not convertible to usize");

        // Needs `Bounded::max_value()` to be `const`.
        // let invalid_index = Self::INVALID_INDEX;
        let invalid_index = I::max_value();

        let object_index =
            I::from_usize(self.array.len()).expect("index not convertible from usize");

        if index_usize == self.indices.len() {
            debug_assert_eq!(index_usize, self.indices.len());
            self.indices.push(object_index);
        } else {
            debug_assert!(index_usize < self.indices.len());
            let object_index_ = unsafe { self.indices.get_unchecked_mut(index_usize) };
            debug_assert!(*object_index_ == invalid_index);
            *object_index_ = object_index;
        }

        self.array.push(value);

        index
    }

    /// Inserts the `value` in the array, returning the [`index`](Index) which may be used to
    /// [`get`](IndexArray::get) / [`get_mut`](IndexArray::get_mut) / [`remove`](IndexArray::remove) it later,
    /// and the mutable reference to the inserted `value`.
    ///
    /// # Panics
    ///
    /// Panics if this would insert enough objects to overflow the underlying [`index`](Index) type.
    pub fn insert_entry(&mut self, value: T) -> (I, &mut T) {
        let index = self.insert(value);

        (index, unsafe { debug_unwrap(self.array.last_mut(), "empty object array") })
    }

    /// Returns `true` if the [`index`](Index) is valid - i.e. it was previously
    /// returned by [`insert`](IndexArray::insert) / [`insert_entry`](IndexArray::insert_entry)
    /// by this [`IndexArray`] and has not been [`removed`](IndexArray::remove) yet.
    ///
    /// NOTE: unlike [`IndexArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn is_valid(&self, index: I) -> bool {
        self.index_manager.is_valid(index)
    }

    /// If the [`index`](Index) [`is_valid`](IndexArray::is_valid), returns the reference to the `value` which was [`inserted`](IndexArray::inserted)
    /// when this handle was returned by this [`IndexArray`].
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn get(&self, index: I) -> Option<&T> {
        self.is_valid_impl(index).map(|(_, _, object_index_usize)| {
            debug_assert!(object_index_usize < self.array.len());
            unsafe { self.array.get_unchecked(object_index_usize) }
        })
    }

    /// If the [`index`](Index) [`is_valid`](IndexArray::is_valid), returns the mutable reference to the `value` which was [`inserted`](IndexArray::inserted)
    /// when this handle was returned by this [`IndexArray`].
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn get_mut(&mut self, index: I) -> Option<&mut T> {
        self.is_valid_impl(index)
            .map(move |(_, _, object_index_usize)| {
                debug_assert!(object_index_usize < self.array.len());
                unsafe { self.array.get_unchecked_mut(object_index_usize) }
            })
    }

    /// If the [`index`](Index) [`is_valid`](IndexArray::is_valid), removes and returns the `value` which was [`inserted`](IndexArray::inserted)
    /// when this handle was returned by this [`IndexArray`], and invalidates the [`index`](Index).
    /// Else returns `None`.
    ///
    /// NOTE: unlike [`HandleArray`], this does not protect against the A-B-A problem -
    /// a reallocated [`index`](Index) will be considered valid.
    pub fn remove(&mut self, index: I) -> Option<T> {
        self.is_valid_impl(index)
            .map(|(index_usize, object_index, object_index_usize)| {
                debug_assert!(object_index_usize < self.array.len());

                self.index_manager.destroy_impl(index);

                // Needs `Bounded::max_value()` to be `const`.
                // let invalid_index = Self::INVALID_INDEX;
                let invalid_index = I::max_value();

                // Move the last object to the free slot and patch its index in the index array.
                *unsafe { self.indices.get_unchecked_mut(index_usize) } = invalid_index;

                debug_assert!(self.array.len() > 0);
                let last_object_index =
                    I::from_usize(self.array.len() - 1).expect("index not convertible from usize");

                if object_index != last_object_index {
                    self.indices.iter_mut().find_map(|index| {
                        (*index == last_object_index).then(|| *index = object_index)
                    });
                }

                unsafe { swap_remove(&mut self.array, object_index_usize) }
            })
    }

    /// Returns the current number of valid [`indices`](Index) / values, [`inserted`](IndexArray::inserted) in this [`IndexArray`].
    pub fn len(&self) -> usize {
        self.array.len()
    }

    /// Returns `true` if [`len`](IndexArray::len) returns `0`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Clears the [`IndexArray`], removing all values and invalidating the allocated indices
    /// (but only until they are allocated again).
    ///
    /// Has no effect on the allocated capacity of the internal data structures.
    pub fn clear(&mut self) {
        self.index_manager.clear();
        self.indices.clear();
        self.array.clear();
    }

    /// Returns the tuple of (index (as usize), object index, object index (as usize)) for a valid `index`.
    fn is_valid_impl(&self, index: I) -> Option<(usize, I, usize)> {
        self.index_manager.is_valid(index).then(|| {
            let index_usize = index.to_usize().expect("index not convertible to usize");

            debug_assert!(index_usize < self.indices.len());
            let object_index = *unsafe { self.indices.get_unchecked(index_usize) };

            (
                index_usize,
                object_index,
                object_index
                    .to_usize()
                    .expect("index not convertible to usize"),
            )
        })
    }
}

impl<T, I> Deref for IndexArray<T, I>
where
    I: Index,
{
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.array.deref()
    }
}

impl<T, I> DerefMut for IndexArray<T, I>
where
    I: Index,
{
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.array.deref_mut()
    }
}

impl<T, I> IntoIterator for IndexArray<T, I>
where
    I: Index,
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
