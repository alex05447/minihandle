use {
    static_assertions::*,
    std::{
        fmt::{Debug, Display, Formatter},
        mem::size_of,
        num::NonZeroU64,
    },
};

/// Inner representation of a valid handle uses this many bits.
pub type HandleInner = u64;

/// Inner representation of the handle's index part.
/// NOTE - max valid index value is [`MAX_HANDLES`](constant.MAX_HANDLES.html), as some bits are reserved.
pub type HandleIndex = u32;

/// Inner representation of the handle's generation part.
pub type HandleGeneration = u16;

/// Inner representation of the handle's metadata part.
pub type HandleMetadata = u16;

#[allow(dead_code)]
const BITS_PER_BYTE: usize = 8;

/// Bit sizes and offsets within the handle's inner representation of its reserved, index, generation and metadata parts.
/// See the description of `Handle` for layout.

const HANDLE_BITS: HandleInner = 64;
const_assert_eq!(
    size_of::<HandleInner>() * BITS_PER_BYTE,
    HANDLE_BITS as usize
);

const VALID_HANDLE_RESERVED_BITS: HandleInner = 1;

const RESERVED_BITS: HandleInner = 2;
const RESERVED_OFFSET: HandleInner = 0;
const RESERVED_MASK: HandleInner = (1 << RESERVED_BITS) - 1;

const INDEX_BITS: HandleInner = 30;
const_assert_eq!(
    size_of::<HandleIndex>() * BITS_PER_BYTE,
    (RESERVED_BITS + INDEX_BITS) as usize
);

const INDEX_OFFSET: HandleInner = RESERVED_OFFSET + RESERVED_BITS;
const INDEX_MASK: HandleInner = (1 << INDEX_BITS) - 1;

/// Maximum number of unique indices, representable by the [`Handle`].
pub const MAX_HANDLES: HandleIndex = INDEX_MASK as HandleIndex;

const GENERATION_BITS: HandleInner = 16;
const_assert_eq!(
    size_of::<HandleGeneration>() * BITS_PER_BYTE,
    GENERATION_BITS as usize
);

const GENERATION_OFFSET: HandleInner = INDEX_OFFSET + INDEX_BITS;
const GENERATION_MASK: HandleInner = (1 << GENERATION_BITS) - 1;

const METADATA_BITS: HandleInner = 16;
const_assert_eq!(
    size_of::<HandleMetadata>() * BITS_PER_BYTE,
    METADATA_BITS as usize
);

const METADATA_OFFSET: HandleInner = GENERATION_OFFSET + GENERATION_BITS;
const METADATA_MASK: HandleInner = (1 << METADATA_BITS) - 1;

const_assert_eq!(
    RESERVED_BITS + INDEX_BITS + GENERATION_BITS + METADATA_BITS,
    HANDLE_BITS
);

/// Handle, a.k.a. weak reference, a.k.a. generational index.
///
/// Some (array) `index` + `generation` (sequence / cycle) number, disambiguating reused indices, if any, solving the A-B-A problem.
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

const_assert_eq!(size_of::<Handle>() * BITS_PER_BYTE, HANDLE_BITS as usize);

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
    /// Creates an invalid [`Handle`].
    ///
    /// [`index`](Handle::index), [`generation`](Handle::generation) and [`metadata`](Handle::metadata) return `None` for an invalid [`Handle`],
    /// [`is_valid`](Handle::is_valid) returns `false`.
    pub fn invalid() -> Self {
        Self(None)
    }

    /// Returns `true` if the [`Handle`] is valid (i.e. was not created by [`invalid`](Handle::invalid) or [`default`](Handle::default)).
    pub fn is_valid(&self) -> bool {
        self.0.is_some()
    }

    /// Attempts to build the [`Handle`] from an opaque value, previously returned by [`into_inner`](Handle::into_inner).
    ///
    /// Checks the reserved bits of the value.
    /// If the reserved bits are null (like they would be for a sufficienty aligned pointer),
    /// or they do not match the pattern used by valid [`Handle`]'s,
    /// `inner` does not represent a valid [`Handle`] and the function returns `None`.
    ///
    /// Otherwise the function returns `Some`, but this by itself does not guarantee that `inner` represents an actual [`Handle`].
    pub fn from_inner(inner: HandleInner) -> Option<Self> {
        NonZeroU64::new(inner).and_then(|handle| {
            // Valid handles have the reserved bits set to `VALID_HANDLE_RESERVED_BITS`.
            (Self::reserved_impl(handle) == VALID_HANDLE_RESERVED_BITS).then(|| Self(Some(handle)))
        })
    }

    /// If the [`Handle`] is [`valid`](Handle::is_valid), returns its (non-null) opaque internal representation, otherwise returns `None`.
    pub fn into_inner(self) -> Option<HandleInner> {
        self.0.map(NonZeroU64::get)
    }

    /// Extracts the [`Handle`]'s index part, or `None` if the handle is not [`valid`](Handle::is_valid).
    pub fn index(&self) -> Option<HandleIndex> {
        self.0.map(Self::index_impl)
    }

    /// Extracts the [`Handle`]'s generation part, or `None` if the handle is not [`valid`](Handle::is_valid).
    pub fn generation(&self) -> Option<HandleGeneration> {
        self.0.map(Self::generation_impl)
    }

    /// Extracts the [`Handle`]'s metadata part, or `None` if the handle is not [`valid`](Handle::is_valid).
    pub fn metadata(&self) -> Option<HandleMetadata> {
        self.0.map(Self::metadata_impl)
    }

    /// Extracts the [`Handle`]'s index, generation and metadata parts, in that order, or `None` if the handle is not [`valid`](Handle::is_valid).
    pub fn unwrap(&self) -> Option<(HandleIndex, HandleGeneration, HandleMetadata)> {
        self.0.map(|h| {
            (
                Self::index_impl(h),
                Self::generation_impl(h),
                Self::metadata_impl(h),
            )
        })
    }

    /// Builds a new [`Handle`] from its components.
    ///
    /// The caller guarantees `index` is not greater than [`MAX_HANDLES`].
    pub(crate) fn new(
        index: HandleIndex,
        generation: HandleGeneration,
        metadata: HandleMetadata,
    ) -> Self {
        debug_assert!(
            index <= MAX_HANDLES,
            "handle index overflow - index is {}, but max index value is {}",
            index,
            MAX_HANDLES
        );

        let handle = (VALID_HANDLE_RESERVED_BITS as HandleInner & RESERVED_MASK) << RESERVED_OFFSET
            | (index as HandleInner & INDEX_MASK) << INDEX_OFFSET
            | (generation as HandleInner & GENERATION_MASK) << GENERATION_OFFSET
            | (metadata as HandleInner & METADATA_MASK) << METADATA_OFFSET;

        debug_assert!(handle > 0);
        Self(Some(unsafe { NonZeroU64::new_unchecked(handle) }))
    }

    fn index_impl(h: NonZeroU64) -> HandleIndex {
        read_bits(h.get(), INDEX_BITS, INDEX_OFFSET) as _
    }

    fn generation_impl(h: NonZeroU64) -> HandleGeneration {
        read_bits(h.get(), GENERATION_BITS, GENERATION_OFFSET) as _
    }

    fn metadata_impl(h: NonZeroU64) -> HandleMetadata {
        read_bits(h.get(), METADATA_BITS, METADATA_OFFSET) as _
    }

    fn reserved_impl(h: NonZeroU64) -> HandleInner {
        read_bits(h.get(), RESERVED_BITS, RESERVED_OFFSET) as _
    }
}

//  7 6 5 4 3 2 1 0  <- bit index
// |h_g_f_e_d_c_b_a|
//            ^ ^
//            |_|
//              |
// offset: 1, num_bits: 2
//
// Shifted by offset:
// |?_h_g_f_e_d_c_b|
//
// Read mask:
// |0_0_0_0_0_0_1_1|
//         &
// |?_h_g_f_e_d_c_b|
//         =
//             |c_b|
fn read_bits(val: HandleInner, num_bits: HandleInner, offset: HandleInner) -> HandleInner {
    debug_assert!((num_bits + offset) <= HANDLE_BITS);

    let read_mask = (1 << num_bits) - 1;

    (val >> offset) & read_mask
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(
        expected = "handle index overflow - index is 1073741824, but max index value is 1073741823"
    )]
    fn index_overflow() {
        let max_index = 1073741823;
        let _ = Handle::new(max_index, 0, 0);
        let _ = Handle::new(max_index + 1, 0, 0);
    }
}
