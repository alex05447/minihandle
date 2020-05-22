use std::fmt::{Debug, Display, Formatter};
use std::num::NonZeroU64;

/// Inner representation of a valid handle uses these many bits.
type Inner = u64;

/// Inner representation of the handle's index part.
/// NOTE - max valid index value is [`MAX_HANDLES`](constant.MAX_HANDLES.html), as some bits are reserved.
pub type Index = u32;

/// Inner representation of the handle's generation part.
pub type Generation = u16;

/// Inner representation of the handle's metadata part.
pub type Metadata = u16;

const BITS_PER_BYTE: usize = 8;

/// Bit sizes and offsets within the handle's inner representation of its reserved, index, generation and metadata parts.
/// See the description of `Handle` for layout.

const HANDLE_BITS: Inner = 64;
const_assert!(_handle_bits; std::mem::size_of::<Inner>() * BITS_PER_BYTE == HANDLE_BITS as usize);

const RESERVED_BITS: Inner = 2;
const RESERVED_OFFSET: Inner = 0;
//const RESERVED_MASK: Inner = (1 << RESERVED_BITS) - 1;

const INDEX_BITS: Inner = 30;
const_assert!(reserved_and_index_bits; std::mem::size_of::<Index>() * BITS_PER_BYTE == (RESERVED_BITS + INDEX_BITS) as usize);

const INDEX_OFFSET: Inner = RESERVED_OFFSET + RESERVED_BITS;
const INDEX_MASK: Inner = (1 << INDEX_BITS) - 1;

/// Maximum number of unique indices, representable by the [`Handle`](struct.Handle.html).
pub const MAX_HANDLES: Index = INDEX_MASK as Index;

const GENERATION_BITS: Inner = 16;
const_assert!(generation_bits; std::mem::size_of::<Generation>() * BITS_PER_BYTE == GENERATION_BITS as usize);

const GENERATION_OFFSET: Inner = INDEX_OFFSET + INDEX_BITS;
const GENERATION_MASK: Inner = (1 << GENERATION_BITS) - 1;

const METADATA_BITS: Inner = 16;
const_assert!(metadata_bits; std::mem::size_of::<Metadata>() * BITS_PER_BYTE == METADATA_BITS as usize);

const METADATA_OFFSET: Inner = GENERATION_OFFSET + GENERATION_BITS;
const METADATA_MASK: Inner = (1 << METADATA_BITS) - 1;

const_assert!(handle_bits; RESERVED_BITS + INDEX_BITS + GENERATION_BITS + METADATA_BITS == HANDLE_BITS);

/// Handle, a.k.a. weak reference, a.k.a. generational index.
///
/// Some (array) `index` + `generation` (sequence) number, disambiguating reused indices, if any, solving the A-B-A problem.
/// As well as a `metadata` part to disambiguate between handles of different types.
///
/// See [http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html](http://bitsquid.blogspot.com/2014/08/building-data-oriented-entity-system.html)
///
/// NOTE - currently internally represented as a 64-bit integer.
/// Good for opaque pointer-sized storage, like Lua lightuserdata, on 64-bit platforms,
/// but won't fork for x86.
///
/// TODO - review this layout.
///
/// |   metadata  |  generation |       index       | reserved |
/// |:-----------:|:-----------:|:-----------------:|:--------:|
/// |   16 bits   |   16 bits   |      30 bits      |  2 bits  |
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct Handle(
    /// Valid handles are non-null (due to non-null reserved bits).
    /// Thus it's valid if `Some`, invalid if `None`, and has the same bit size as `u64`.
    Option<NonZeroU64>,
);

const_assert!(handle_size; std::mem::size_of::<Handle>() * BITS_PER_BYTE == HANDLE_BITS as usize);

impl Display for Handle {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some((index, generation, metadata)) = self.unwrap() {
            write!(f, "[i:{} g:{} m:{}]", index, generation, metadata)
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

impl Handle {
    /// Creates an invalid [`handle`].
    ///
    /// [`index`], [`generation`] and [`metadata`] return `None` for an invalid [`handle`],
    /// [`is_valid`] returns `false`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`index`]: #method.index
    /// [`generation`]: #method.generation
    /// [`metadata`]: #method.metadata
    /// [`is_valid`]: #method.is_valid
    pub fn invalid() -> Self {
        Self(None)
    }

    /// Returns `true` if the [`handle`] is valid (i.e. was not created by [`invalid`] or [`default`]).
    ///
    /// [`handle`]: struct.Handle.html
    /// [`invalid`]: #method.invalid
    /// [`default`]: #method.default
    pub fn is_valid(&self) -> bool {
        self.0.is_some()
    }

    /// Builds a new [`handle`] from its components.
    ///
    /// # Panics
    ///
    /// Panics if `index` value is larger then [`MAX_HANDLES`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`MAX_HANDLES`]: constant.MAX_HANDLES.html
    pub fn new(index: Index, generation: Generation, metadata: Metadata) -> Self {
        assert!(
            index < MAX_HANDLES,
            "Handle index overflow - index is {}, but max index value is {}.",
            index,
            MAX_HANDLES
        );

        let handle = 1
            | (index as u64 & INDEX_MASK) << INDEX_OFFSET
            | (generation as u64 & GENERATION_MASK) << GENERATION_OFFSET
            | (metadata as u64 & METADATA_MASK) << METADATA_OFFSET;

        Self(Some(NonZeroU64::new(handle).unwrap()))
    }

    /// Attempts to build the [`handle`] from an opaque value, previously returned by [`to_inner`].
    ///
    /// Checks the reserved bits of the value.
    /// If the reserved bits are unset (like they would be for a sufficienty aligned pointer),
    /// `inner` does not represent a valid [`Handle`] and the function returns `None`.
    ///
    /// Otherwise the function returns `Some`, but this does not guarantee that `inner` represents a [`Handle`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`to_inner`]: #method.to_inner
    /// [`Handle`]: struct.Handle.html
    pub fn from_inner(inner: Inner) -> Option<Self> {
        // Valid handles have the reserved bits set to `1`.
        if read_bits(inner, RESERVED_BITS, RESERVED_OFFSET) != 1 {
            None
        } else {
            debug_assert!(inner > 0);
            Some(Self(Some(NonZeroU64::new(inner).unwrap())))
        }
    }

    /// If the [`handle`] is [`valid`], returns its (non-null) opaque internal representation, otherwise returns `None`.
    ///
    /// [`handle`]: struct.Handle.html
    /// [`valid`]: #method.is_valid.html
    pub fn into_inner(self) -> Option<Inner> {
        self.0.map(NonZeroU64::get)
    }

    /// Extracts the [`handle`]'s index part, or `None` if the handle is not [`valid`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`valid`]: #method.is_valid.html
    pub fn index(&self) -> Option<Index> {
        self.0.map(Self::index_impl)
    }

    /// Extracts the [`handle`]'s generation part, or `None` if the handle is not [`valid`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`valid`]: #method.is_valid.html
    pub fn generation(&self) -> Option<Generation> {
        self.0.map(Self::generation_impl)
    }

    /// Extracts the [`handle`]'s metadata part, or `None` if the handle is not [`valid`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`valid`]: #method.is_valid.html
    pub fn metadata(&self) -> Option<Metadata> {
        self.0.map(Self::metadata_impl)
    }

    /// Extracts the [`handle`]'s index, generation and metadata parts, in that order, or `None` if the handle is not [`valid`].
    ///
    /// [`handle`]: struct.Handle.html
    /// [`valid`]: #method.is_valid.html
    pub fn unwrap(&self) -> Option<(Index, Generation, Metadata)> {
        self.0.map(|h| {
            (
                Self::index_impl(h),
                Self::generation_impl(h),
                Self::metadata_impl(h),
            )
        })
    }

    fn index_impl(h: NonZeroU64) -> Index {
        read_bits(h.get(), INDEX_BITS, INDEX_OFFSET) as Index
    }

    fn generation_impl(h: NonZeroU64) -> Generation {
        read_bits(h.get(), GENERATION_BITS, GENERATION_OFFSET) as Generation
    }

    fn metadata_impl(h: NonZeroU64) -> Metadata {
        read_bits(h.get(), METADATA_BITS, METADATA_OFFSET) as Metadata
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

fn read_bits(source: Inner, num_bits_to_read: Inner, offset: Inner) -> Inner {
    debug_assert!((num_bits_to_read + offset) <= HANDLE_BITS);

    let read_mask = (1 << num_bits_to_read) - 1;

    (source >> offset) & read_mask
}
