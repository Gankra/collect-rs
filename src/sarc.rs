//! Concurrency-enabled mechanisms for sharing mutable and/or immutable state
//! between tasks.

use alloc::heap::deallocate;
use core::atomic;
use core::borrow::BorrowFrom;
use core::clone::Clone;
use core::fmt::{mod, Show};
use core::cmp::{Eq, Ord, PartialEq, PartialOrd, Ordering};
use core::default::Default;
use core::kinds::{Sync, Send};
use core::mem::{min_align_of, size_of, drop};
use core::mem;
use core::ops::{Drop, Deref};
use core::option::Option;
use core::ptr::RawPtr;
use core::ptr;

/// An slim atomically reference counted wrapper for shared state.
///
/// Compared to an `Arc<T>`, `SArc<T>` has half of the memory overhead.
/// This is done in the spirit of paying only for what you use. Most people don't
/// use the weak reference count, and it's silly to bloat all reference counts with
/// a rarely used feature.
///
/// # Example
///
/// In this example, a large vector of floats is shared between several tasks.
/// With simple pipes, without `SArc`, a copy would have to be made for each
/// task.
///
/// ```rust
/// use collect::SArc;
/// use std::thread::Thread;
///
/// fn main() {
///     let numbers = Vec::from_fn(100, |i| i as f32);
///     let shared_numbers = SArc::new(numbers);
///
///     for _ in range(0u, 10) {
///         let child_numbers = shared_numbers.clone();
///
///         Thread::spawn(move || {
///             let local_numbers = child_numbers.as_slice();
///
///             // Work with the local numbers
///         }).detach();
///     }
/// }
/// ```
#[unsafe_no_drop_flag]
#[stable]
pub struct SArc<T> {
    // FIXME rust-lang/rust#12808: strange name to try to avoid interfering with
    // field accesses of the contained type via Deref
    _ptr: *mut ArcInner<T>,
}

struct ArcInner<T> {
    strong: atomic::AtomicUint,
    data:   T,
}

impl<T: Sync + Send> SArc<T> {
    /// Creates an atomically reference counted wrapper.
    #[inline]
    #[stable]
    pub fn new(data: T) -> SArc<T> {
        let x = box ArcInner {
            strong: atomic::AtomicUint::new(1),
            data: data,
        };
        SArc { _ptr: unsafe { mem::transmute(x) } }
    }
}

impl<T> SArc<T> {
    #[inline]
    fn inner(&self) -> &ArcInner<T> {
        // This unsafety is ok because while this arc is alive we're guaranteed
        // that the inner pointer is valid. Furthermore, we know that the
        // `ArcInner` structure itself is `Sync` because the inner data is
        // `Sync` as well, so we're ok loaning out an immutable pointer to
        // these contents.
        unsafe { &*self._ptr }
    }
}

/// Get the number of strong references to this value.
#[inline]
#[experimental]
pub fn strong_count<T>(this: &SArc<T>) -> uint { this.inner().strong.load(atomic::SeqCst) }

#[unstable = "waiting on stability of Clone"]
impl<T> Clone for SArc<T> {
    /// Duplicate an atomically reference counted wrapper.
    ///
    /// The resulting two `SArc` objects will point to the same underlying data
    /// object. However, one of the `SArc` objects can be sent to another task,
    /// allowing them to share the underlying data.
    #[inline]
    fn clone(&self) -> SArc<T> {
        // Using a relaxed ordering is alright here, as knowledge of the
        // original reference prevents other threads from erroneously deleting
        // the object.
        //
        // As explained in the [Boost documentation][1], Increasing the
        // reference counter can always be done with memory_order_relaxed: New
        // references to an object can only be formed from an existing
        // reference, and passing an existing reference from one thread to
        // another must already provide any required synchronization.
        //
        // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
        self.inner().strong.fetch_add(1, atomic::Relaxed);
        SArc { _ptr: self._ptr }
    }
}

impl<T> BorrowFrom<SArc<T>> for T {
    fn borrow_from(owned: &SArc<T>) -> &T {
        &**owned
    }
}

#[experimental = "Deref is experimental."]
impl<T> Deref<T> for SArc<T> {
    #[inline]
    fn deref(&self) -> &T {
        &self.inner().data
    }
}

impl<T: Send + Sync + Clone> SArc<T> {
    /// Acquires a mutable pointer to the inner contents by guaranteeing that
    /// the reference count is one (no sharing is possible).
    ///
    /// This is also referred to as a copy-on-write operation because the inner
    /// data is cloned if the reference count is greater than one.
    #[inline]
    #[experimental]
    pub fn make_unique(&mut self) -> &mut T {
        if self.inner().strong.load(atomic::SeqCst) != 1 {
            *self = SArc::new((**self).clone())
        }

        // This unsafety is ok because we're guaranteed that the pointer
        // returned is the *only* pointer that will ever be returned to T. Our
        // reference count is guaranteed to be 1 at this point, and we required
        // the Arc itself to be `mut`, so we're returning the only possible
        // reference to the inner data.
        let inner = unsafe { &mut *self._ptr };
        &mut inner.data
    }
}

// keep out of line to guide inlining.
unsafe fn do_drop<T>(this: &mut SArc<T>) {
    // This fence is needed to prevent reordering of use of the data and
    // deletion of the data. Because it is marked `Release`, the
    // decreasing of the reference count synchronizes with this `Acquire`
    // fence. This means that use of the data happens before decreasing
    // the reference count, which happens before this fence, which
    // happens before the deletion of the data.
    //
    // As explained in the [Boost documentation][1],
    //
    // It is important to enforce any possible access to the object in
    // one thread (through an existing reference) to *happen before*
    // deleting the object in a different thread. This is achieved by a
    // "release" operation after dropping a reference (any access to the
    // object through this reference must obviously happened before),
    // and an "acquire" operation before deleting the object.
    //
    // [1]: (www.boost.org/doc/libs/1_55_0/doc/html/atomic/usage_examples.html)
    atomic::fence(atomic::Acquire);

    drop(ptr::read(&this.inner().data));
    deallocate(this._ptr as *mut u8, size_of::<ArcInner<T>>(),
               min_align_of::<ArcInner<T>>());
}

#[unsafe_destructor]
#[experimental = "waiting on stability of Drop"]
impl<T: Sync + Send> Drop for SArc<T> {
    #[inline]
    fn drop(&mut self) {
        // This structure has #[unsafe_no_drop_flag], so this drop glue may run
        // more than once (but it is guaranteed to be zeroed after the first if
        // it's run more than once)
        if self._ptr.is_null() { return }

        // Because `fetch_sub` is already atomic, we do not need to synchronize
        // with other threads unless we are going to delete the object.
        if self.inner().strong.fetch_sub(1, atomic::Release) != 1 { return }

        unsafe { do_drop(self) }
    }
}

#[unstable = "waiting on PartialEq"]
impl<T: PartialEq> PartialEq for SArc<T> {
    fn eq(&self, other: &SArc<T>) -> bool { *(*self) == *(*other) }
    fn ne(&self, other: &SArc<T>) -> bool { *(*self) != *(*other) }
}
#[unstable = "waiting on PartialOrd"]
impl<T: PartialOrd> PartialOrd for SArc<T> {
    fn partial_cmp(&self, other: &SArc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }
    fn lt(&self, other: &SArc<T>) -> bool { *(*self) < *(*other) }
    fn le(&self, other: &SArc<T>) -> bool { *(*self) <= *(*other) }
    fn ge(&self, other: &SArc<T>) -> bool { *(*self) >= *(*other) }
    fn gt(&self, other: &SArc<T>) -> bool { *(*self) > *(*other) }
}
#[unstable = "waiting on Ord"]
impl<T: Ord> Ord for SArc<T> {
    fn cmp(&self, other: &SArc<T>) -> Ordering { (**self).cmp(&**other) }
}
#[unstable = "waiting on Eq"]
impl<T: Eq> Eq for SArc<T> {}

impl<T: fmt::Show> fmt::Show for SArc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[stable]
impl<T: Default + Sync + Send> Default for SArc<T> {
    #[stable]
    fn default() -> SArc<T> { SArc::new(Default::default()) }
}

#[cfg(test)]
#[allow(experimental)]
mod tests {
    use std::clone::Clone;
    use std::comm::channel;
    use std::mem::drop;
    use std::ops::Drop;
    use std::sync::atomic;
    use std::thread::Thread;
    use std::vec::Vec;
    use super::{SArc, strong_count};

    struct Canary(*mut atomic::AtomicUint);

    impl Drop for Canary
    {
        fn drop(&mut self) {
            unsafe {
                match *self {
                    Canary(c) => {
                        (*c).fetch_add(1, atomic::SeqCst);
                    }
                }
            }
        }
    }

    #[test]
    fn manually_share_arc() {
        let v = vec!(1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
        let arc_v = SArc::new(v);

        let (tx, rx) = channel();

        Thread::spawn(move || {
            let arc_v: SArc<Vec<int>> = rx.recv();
            assert_eq!((*arc_v)[3], 4);
        }).detach();

        tx.send(arc_v.clone());

        assert_eq!((*arc_v)[2], 3);
        assert_eq!((*arc_v)[4], 5);
    }

    #[test]
    fn test_cowarc_clone_make_unique() {
        let mut cow0 = SArc::new(75u);
        let mut cow1 = cow0.clone();
        let mut cow2 = cow1.clone();

        assert!(75 == *cow0.make_unique());
        assert!(75 == *cow1.make_unique());
        assert!(75 == *cow2.make_unique());

        *cow0.make_unique() += 1;
        *cow1.make_unique() += 2;
        *cow2.make_unique() += 3;

        assert!(76 == *cow0);
        assert!(77 == *cow1);
        assert!(78 == *cow2);

        // none should point to the same backing memory
        assert!(*cow0 != *cow1);
        assert!(*cow0 != *cow2);
        assert!(*cow1 != *cow2);
    }

    #[test]
    fn test_cowarc_clone_unique2() {
        let mut cow0 = SArc::new(75u);
        let cow1 = cow0.clone();
        let cow2 = cow1.clone();

        assert!(75 == *cow0);
        assert!(75 == *cow1);
        assert!(75 == *cow2);

        *cow0.make_unique() += 1;

        assert!(76 == *cow0);
        assert!(75 == *cow1);
        assert!(75 == *cow2);

        // cow1 and cow2 should share the same contents
        // cow0 should have a unique reference
        assert!(*cow0 != *cow1);
        assert!(*cow0 != *cow2);
        assert!(*cow1 == *cow2);
    }

    #[test]
    fn drop_arc() {
        let mut canary = atomic::AtomicUint::new(0);
        let x = SArc::new(Canary(&mut canary as *mut atomic::AtomicUint));
        drop(x);
        assert!(canary.load(atomic::Acquire) == 1);
    }

    #[test]
    fn test_strong_count() {
        let a = SArc::new(0u32);
        assert!(strong_count(&a) == 1);
        let b = a.clone();
        assert!(strong_count(&b) == 2);
        assert!(strong_count(&a) == 2);
        drop(a);
        assert!(strong_count(&b) == 1);
        let c = b.clone();
        assert!(strong_count(&b) == 2);
        assert!(strong_count(&c) == 2);
    }

    #[test]
    fn show_arc() {
        let a = SArc::new(5u32);
        assert!(format!("{}", a) == "5")
    }

    // Make sure deriving works with SArc<T>
    #[deriving(Eq, Ord, PartialEq, PartialOrd, Clone, Show, Default)]
    struct Foo { inner: SArc<int> }
}
