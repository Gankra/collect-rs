//! A memory buffer with resizing.

use core::nonzero::NonZero;
use std::num::Int;
use std::ops::Deref;
use std::rt::heap;
use std::mem;

/// A safe wrapper around a heap allocated buffer of Ts, tracking capacity only.
///
/// Buffer makes no promises about the actual contents of this memory, that's up
/// to the user of the structure and can be manipulated using the standard pointer
/// utilities, accessible through the impl of `Deref<Target=*mut T>` for `Buffer<T>`.
///
/// As a result of this hands-off approach, `Buffer`s destructor does not attempt
/// to drop any of the contained elements; the destructor simply frees the contained
/// memory.
///
/// You can think of `Buffer<T>` as an approximation for `Box<[T]>` where the elements
/// are not guaranteed to be valid/initialized. It is meant to be used as a building
/// block for other collections, so they do not have to concern themselves with the
/// minutiae of allocating, reallocating, and deallocating memory.
pub struct Buffer<T> {
    buffer: NonZero<*mut T>,
    cap: usize
}

unsafe impl<T: Send> Send for Buffer<T> { }
unsafe impl<T: Sync> Sync for Buffer<T> { }

impl<T> Buffer<T> {
    /// Create a new, empty Buffer.
    ///
    /// ```
    /// # use collect::util::buffer::Buffer;
    ///
    /// let buffer: Buffer<usize> = Buffer::new();
    /// assert_eq!(buffer.capacity(), 0);
    /// ```
    pub fn new() -> Buffer<T> {
        Buffer {
            buffer: unsafe { NonZero::new(heap::EMPTY as *mut T) },
            cap: 0
        }
    }

    /// Create a new buffer with space for cap Ts.
    ///
    /// ```
    /// # use collect::util::buffer::Buffer;
    ///
    /// let buffer: Buffer<usize> = Buffer::allocate(128);
    /// assert_eq!(buffer.capacity(), 128);
    /// ```
    pub fn allocate(cap: usize) -> Buffer<T> {
        if cap == 0 { return Buffer::new() }

        Buffer {
            buffer: unsafe { allocate(NonZero::new(cap)) },
            cap: cap
        }
    }

    /// Reallocate this buffer to fit a new number of Ts.
    ///
    /// ```
    /// # use collect::util::buffer::Buffer;
    ///
    /// let mut buffer: Buffer<usize> = Buffer::allocate(128);
    /// assert_eq!(buffer.capacity(), 128);
    ///
    /// buffer.reallocate(1024);
    /// assert_eq!(buffer.capacity(), 1024);
    /// ```
    pub fn reallocate(&mut self, cap: usize) {
        *self = if self.cap == 0 || cap == 0 {
            Buffer::allocate(cap)
        } else {
            Buffer {
                buffer: unsafe {
                    reallocate(self.buffer,
                               NonZero::new(self.cap),
                               NonZero::new(cap))
                },
                cap: cap
            }
        }
    }

    /// Get the current capacity of the Buffer.
    ///
    /// ```
    /// # use collect::util::buffer::Buffer;
    ///
    /// let buffer: Buffer<usize> = Buffer::allocate(128);
    /// assert_eq!(buffer.capacity(), 128);
    /// ```
    pub fn capacity(&self) -> usize {
        self.cap
    }
}

#[unsafe_destructor]
impl<T> Drop for Buffer<T> {
    /// Safety Note:
    ///
    /// The Buffer will *only* deallocate the contained memory. It will
    /// *not* run any destructors on data in that memory.
    fn drop(&mut self) {
        if self.cap == 0 { return }
        unsafe { deallocate(self.buffer, NonZero::new(self.cap)) }
    }
}

impl<T> Deref for Buffer<T> {
    type Target = *mut T;

    fn deref(&self) -> &*mut T {
        &*self.buffer
    }
}

// Typed Allocation Utilities
//
// Unlike std::rt::heap these check for zero-sized types, capacity overflow,
// oom etc. and calculate the appropriate size and alignment themselves.

unsafe fn allocate<T>(cap: NonZero<usize>) -> NonZero<*mut T> {
    if mem::size_of::<T>() == 0 { return empty() }

    // Allocate
    let ptr = heap::allocate(allocation_size::<T>(cap), mem::align_of::<T>());

    // Check for allocation failure
    if ptr.is_null() { ::alloc::oom() }

    NonZero::new(ptr as *mut T)
}

unsafe fn reallocate<T>(ptr: NonZero<*mut T>,
                        old_cap: NonZero<usize>,
                        new_cap: NonZero<usize>) -> NonZero<*mut T> {
    if mem::size_of::<T>() == 0 { return empty() }

    let old_size = unchecked_allocation_size::<T>(old_cap);
    let new_size = allocation_size::<T>(new_cap);

    // Reallocate
    let ptr = heap::reallocate(*ptr as *mut u8, old_size, new_size, mem::align_of::<T>());

    // Check for allocation failure
    if ptr.is_null() { ::alloc::oom() }

    NonZero::new(ptr as *mut T)
}

unsafe fn deallocate<T>(ptr: NonZero<*mut T>, cap: NonZero<usize>) {
    if mem::size_of::<T>() == 0 { return }

    let old_size = unchecked_allocation_size::<T>(cap);

    heap::deallocate(*ptr as *mut u8, old_size, mem::align_of::<T>())
}

fn allocation_size<T>(cap: NonZero<usize>) -> usize {
    mem::size_of::<T>().checked_mul(*cap).expect("Capacity overflow")
}

fn unchecked_allocation_size<T>(cap: NonZero<usize>) -> usize {
    mem::size_of::<T>() * (*cap)
}

fn empty<T>() -> NonZero<*mut T> {
    unsafe { NonZero::new(heap::EMPTY as *mut T) }
}

#[cfg(test)]
mod test {
    use std::ptr;

    use util::buffer::Buffer;
    use super::empty;

    #[test]
    fn test_empty() {
        let buffer: Buffer<usize> = Buffer::new();
        assert_eq!(buffer.cap, 0);
        assert_eq!(buffer.buffer, empty());
    }

    #[test]
    fn test_allocate() {
        let buffer: Buffer<usize> = Buffer::allocate(8);

        assert_eq!(buffer.cap, 8);

        unsafe {
            ptr::write(buffer.offset(0), 8);
            ptr::write(buffer.offset(1), 4);
            ptr::write(buffer.offset(3), 5);
            ptr::write(buffer.offset(5), 3);
            ptr::write(buffer.offset(7), 6);

            assert_eq!(ptr::read(buffer.offset(0)), 8);
            assert_eq!(ptr::read(buffer.offset(1)), 4);
            assert_eq!(ptr::read(buffer.offset(3)), 5);
            assert_eq!(ptr::read(buffer.offset(5)), 3);
            assert_eq!(ptr::read(buffer.offset(7)), 6);
        };

        // Try a large buffer
        let buffer: Buffer<usize> = Buffer::allocate(1024 * 1024);

        unsafe {
            ptr::write(buffer.offset(1024 * 1024 - 1), 12);
            assert_eq!(ptr::read(buffer.offset(1024 * 1024 - 1)), 12);
        };
    }

    #[test]
    fn test_reallocate() {
        let mut buffer: Buffer<usize> = Buffer::allocate(8);
        assert_eq!(buffer.cap, 8);

        buffer.reallocate(16);
        assert_eq!(buffer.cap, 16);

        unsafe {
            // Put some data in the buffer
            ptr::write(buffer.offset(0), 8);
            ptr::write(buffer.offset(1), 4);
            ptr::write(buffer.offset(5), 3);
            ptr::write(buffer.offset(7), 6);
        };

        // Allocate so in-place fails.
        let _: Buffer<usize> = Buffer::allocate(128);

        buffer.reallocate(32);

        unsafe {
            // Ensure the data is still there.
            assert_eq!(ptr::read(buffer.offset(0)), 8);
            assert_eq!(ptr::read(buffer.offset(1)), 4);
            assert_eq!(ptr::read(buffer.offset(5)), 3);
            assert_eq!(ptr::read(buffer.offset(7)), 6);
        };
    }

    #[test]
    #[should_fail = "Capacity overflow."]
    fn test_allocate_capacity_overflow() {
        let _: Buffer<usize> = Buffer::allocate(10_000_000_000_000_000_000);
    }

    #[test]
    #[should_fail = "Capacity overflow."]
    fn test_fresh_reallocate_capacity_overflow() {
        let mut buffer: Buffer<usize> = Buffer::new();
        buffer.reallocate(10_000_000_000_000_000_000);
    }

    #[test]
    #[should_fail = "Capacity overflow."]
    fn test_reallocate_capacity_overflow() {
        let mut buffer: Buffer<usize> = Buffer::allocate(128);
        buffer.reallocate(10_000_000_000_000_000_000);
    }
}

