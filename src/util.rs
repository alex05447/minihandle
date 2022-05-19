fn debug_unreachable(msg: &'static str) -> ! {
    if cfg!(debug_assertions) {
        unreachable!("{}", msg)
    } else {
        unsafe { std::hint::unreachable_unchecked() }
    }
}

pub(crate) unsafe fn debug_unwrap<T>(val: Option<T>, msg: &'static str) -> T {
    if let Some(val) = val {
        val
    } else {
        debug_unreachable(msg)
    }
}

/// `Vec::swap_remove`, but without a panic.
/// The caller guarantess `index` is strictly less than `vec.len()`.
pub(crate) unsafe fn swap_remove<T>(vec: &mut Vec<T>, index: usize) -> T {
    let len = vec.len();
    debug_assert!(index < len);

    // We replace self[index] with the last element. Note that if the
    // bounds check above succeeds there must be a last element (which
    // can be self[index] itself).
    let value = std::ptr::read(vec.as_ptr().add(index));
    let base_ptr = vec.as_mut_ptr();
    std::ptr::copy(base_ptr.add(len - 1), base_ptr.add(index), 1);
    vec.set_len(len - 1);
    value
}
