use std::fmt::{Debug, Display, Formatter};
use std::num::NonZeroU64;

/// Handle, a.k.a. weak reference, a.k.a. generational index.
///
/// Some (array) index + generation (sequence) number, disambiguating reused indices, if any, solving the A-B-A problem.
///
/// See [http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html](http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html)
///
/// NOTE - internally represented as a 64-bit integer.
/// Good for opaque pointer-sized storage, like Lua lightuserdata, on 64-bit platforms,
/// but won't fork for x86.
///
/// TODO - review this layout.
///
/// |   metadata  |  generation |       index       | reserved |
/// |:-----------:|:-----------:|:-----------------:|:--------:|
/// |   16 bits   |   16 bits   |      30 bits      |  2 bits  |
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Handle(Option<NonZeroU64>);

impl Display for Handle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if self.is_valid() {
            write!(
                f,
                "[i:{} g:{} m:{}]",
                self.index().unwrap(),
                self.generation().unwrap(),
                self.metadata().unwrap()
            )
        } else {
            write!(f, "[invalid handle]")
        }
    }
}

impl Debug for Handle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        <Self as Display>::fmt(self, f)
    }
}

impl Default for Handle {
    fn default() -> Self {
        Handle::invalid()
    }
}

const RESERVED_BITS: u64 = 2;
const RESERVED_OFFSET: u64 = 0;
//const RESERVED_MASK: u64 = (1 << RESERVED_BITS) - 1;

const INDEX_BITS: u64 = 30;
const INDEX_OFFSET: u64 = RESERVED_OFFSET + RESERVED_BITS;
const INDEX_MASK: u64 = (1 << INDEX_BITS) - 1;

const GENERATION_BITS: u64 = 16;
const GENERATION_OFFSET: u64 = INDEX_OFFSET + INDEX_BITS;
const GENERATION_MASK: u64 = (1 << GENERATION_BITS) - 1;

const METADATA_BITS: u64 = 16;
const METADATA_OFFSET: u64 = GENERATION_OFFSET + GENERATION_BITS;
const METADATA_MASK: u64 = (1 << METADATA_BITS) - 1;

const_assert!(handle_bits; RESERVED_BITS + INDEX_BITS + GENERATION_BITS + METADATA_BITS == 64);

impl Handle {
    pub fn invalid() -> Self {
        Self(None)
    }

    pub fn is_valid(&self) -> bool {
        self.0.is_some()
    }

    /// Build a new handle from its components.
    ///
    /// # Panics
    ///
    /// Panics if `index` value overflows `30` bits.
    pub fn new(index: u32, generation: u16, metadata: u16) -> Self {
        assert!(
            (index as u64) < INDEX_MASK,
            "Index overflow - index is {}, max value is {}.",
            index,
            INDEX_MASK
        );

        let handle = 1
            | (index as u64 & INDEX_MASK) << INDEX_OFFSET
            | (generation as u64 & GENERATION_MASK) << GENERATION_OFFSET
            | (metadata as u64 & METADATA_MASK) << METADATA_OFFSET;

        Self(Some(NonZeroU64::new(handle).unwrap()))
    }

    /// Builds the handle from an opaque pointer-sized value, previously returned by [`to_ptr`].
    ///
    /// Checks the reserved (lowest) bits of the value.
    /// If the reserved bits are unset (like they would be for a sufficienty aligned pointer),
    /// `ptr` does not represent a valid [`Handle`] and the function returns `None`.
    ///
    /// Otherwise the function returns `Some(...)`, but this does not guarantee that `ptr` represents a [`Handle`].
    ///
    /// [`to_ptr`]: #method.to_ptr
    /// [`Handle`]: struct.Handle.html
    pub fn from_ptr(ptr: u64) -> Option<Self> {
        // Valid handles have the reserved bits set to `1`.
        if read_bits(ptr, RESERVED_BITS, RESERVED_OFFSET) != 1 {
            None
        } else {
            Some(Self(Some(NonZeroU64::new(ptr).unwrap())))
        }
    }

    /// If the [`Handle`] is valid, returns its internal representation, otherwise returns `None`.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn to_ptr(&self) -> Option<u64> {
        self.0.map(NonZeroU64::get)
    }

    /// Extracts the [`Handle`]'s index part, or `None` if the handle is not valid.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn index(&self) -> Option<u32> {
        self.0.map(Self::index_impl)
    }

    /// Extracts the [`Handle`]'s generation part, or `None` if the handle is not valid.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn generation(&self) -> Option<u16> {
        self.0.map(Self::generation_impl)
    }

    /// Extracts the [`Handle`]'s metadata part, or `None` if the handle is not valid.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn metadata(&self) -> Option<u16> {
        self.0.map(Self::metadata_impl)
    }

    /// Extracts the [`Handle`]'s index, generation and metadata parts, in that order, or `None` if the handle is not valid.
    ///
    /// [`Handle`]: struct.Handle.html
    pub fn unwrap(&self) -> Option<(u32, u16, u16)> {
        self.0.map(|h| {
            (
                Self::index_impl(h),
                Self::generation_impl(h),
                Self::metadata_impl(h),
            )
        })
    }

    fn index_impl(h: NonZeroU64) -> u32 {
        read_bits(h.get(), INDEX_BITS, INDEX_OFFSET) as u32
    }

    fn generation_impl(h: NonZeroU64) -> u16 {
        read_bits(h.get(), GENERATION_BITS, GENERATION_OFFSET) as u16
    }

    fn metadata_impl(h: NonZeroU64) -> u16 {
        read_bits(h.get(), METADATA_BITS, METADATA_OFFSET) as u16
    }

    /*
        fn reserved(&self) -> Option<u8> {
            if let Some(handle) = self.0 {
                Some(
                    read_bits(
                        handle.get(),
                        RESERVED_BITS,
                        RESERVED_OFFSET
                    ) as u8
                )
            } else {
                None
            }
        }
    */
}

fn read_bits(source: u64, num_bits_to_read: u64, offset: u64) -> u64 {
    debug_assert!((num_bits_to_read + offset) <= 64);

    let read_mask = (1 << num_bits_to_read) - 1;

    (source >> offset) & read_mask
}
