// Copyright 2013-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Slim task-local reference-counted boxes (the `SRc<T>` type).
//!
//! Compared to an `Rc<T>`, `SRc<T>` has half of the memory overhead.
//! This is done in the spirit of paying only for what you use. Most people don't
//! use the weak reference count, and it's silly to bloat all reference counts with
//! a rarely used feature.
//!
//! The `SRc<T>` type provides shared ownership of an immutable value. Destruction is deterministic,
//! and will occur as soon as the last owner is gone. It is marked as non-sendable because it
//! avoids the overhead of atomic reference counting.
//!
//! # Examples
//!
//! Consider a scenario where a set of `Gadget`s are owned by a given `Owner`.  We want to have our
//! `Gadget`s point to their `Owner`. We can't do this with unique ownership, because more than one
//! gadget may belong to the same `Owner`. `SRc<T>` allows us to share an `Owner` between multiple
//! `Gadget`s, and have the `Owner` remain allocated as long as any `Gadget` points at it.
//!
//! ```rust
//! use collect::SRc;
//!
//! struct Owner {
//!     name: String
//!     // ...other fields
//! }
//!
//! struct Gadget {
//!     id: int,
//!     owner: SRc<Owner>
//!     // ...other fields
//! }
//!
//! fn main() {
//!     // Create a reference counted Owner.
//!     let gadget_owner : SRc<Owner> = SRc::new(
//!             Owner { name: String::from_str("Gadget Man") }
//!     );
//!
//!     // Create Gadgets belonging to gadget_owner. To increment the reference
//!     // count we clone the `SRc<T>` object.
//!     let gadget1 = Gadget { id: 1, owner: gadget_owner.clone() };
//!     let gadget2 = Gadget { id: 2, owner: gadget_owner.clone() };
//!
//!     drop(gadget_owner);
//!
//!     // Despite dropping gadget_owner, we're still able to print out the name of
//!     // the Owner of the Gadgets. This is because we've only dropped the
//!     // reference count object, not the Owner it wraps. As long as there are
//!     // other `SRc<T>` objects pointing at the same Owner, it will remain allocated. Notice
//!     // that the `SRc<T>` wrapper around Gadget.owner gets automatically dereferenced
//!     // for us.
//!     println!("Gadget {} owned by {}", gadget1.id, gadget1.owner.name);
//!     println!("Gadget {} owned by {}", gadget2.id, gadget2.owner.name);
//!
//!     // At the end of the method, gadget1 and gadget2 get destroyed, and with
//!     // them the last counted references to our Owner. Gadget Man now gets
//!     // destroyed as well.
//! }
//! ```
use alloc::heap::deallocate;
use core::borrow::BorrowFrom;
use core::cell::Cell;
use core::clone::Clone;
use core::cmp::{PartialEq, PartialOrd, Eq, Ord, Ordering};
use core::default::Default;
use core::fmt;
use core::hash::{mod, Hash};
use core::kinds::marker;
use core::mem::{transmute, min_align_of, size_of, forget};
use core::ops::{Deref, Drop};
use core::option::Option;
use core::option::Option::{Some, None};
use core::ptr;
use core::ptr::RawPtr;
use core::result::Result;
use core::result::Result::{Ok, Err};


struct RcBox<T> {
    strong: Cell<uint>,
    value:  T,
}

/// An immutable reference-counted pointer type.
///
/// See the [module level documentation](../index.html) for more.
#[unsafe_no_drop_flag]
#[stable]
pub struct SRc<T> {
    // FIXME #12808: strange names to try to avoid interfering with
    // field accesses of the contained type via Deref
    _ptr: *mut RcBox<T>,
    _nosend: marker::NoSend,
    _noshare: marker::NoSync
}

impl<T> SRc<T> {
    /// Constructs a new `Rc<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    /// assert_eq!(five, SRc::new(5i));
    /// ```
    #[stable]
    pub fn new(value: T) -> SRc<T> {
        unsafe {
            SRc {
                _ptr: transmute(box RcBox {
                    strong: Cell::new(1),
                    value: value,
                }),
                _nosend: marker::NoSend,
                _noshare: marker::NoSync
            }
        }
    }
}

/// Get the number of strong references to this value.
#[inline]
#[experimental]
pub fn strong_count<T>(this: &SRc<T>) -> uint { this.strong() }

/// Returns true if there are no other `SRc<T>` values that share the same inner value.
///
/// # Examples
///
/// ```
/// use collect::src;
/// use collect::SRc;
///
/// let five = SRc::new(5i);
///
/// assert!(src::is_unique(&five));
/// ```
#[inline]
#[experimental]
pub fn is_unique<T>(rc: &SRc<T>) -> bool {
    strong_count(rc) == 1
}

/// Unwraps the contained value if the `SRc<T>` is unique.
///
/// If the `SRc<T>` is not unique, an `Err` is returned with the same `SRc<T>`.
///
/// # Example
///
/// ```
/// use collect::src::{mod, SRc};
///
/// let x = SRc::new(3u);
/// assert_eq!(src::try_unwrap(x), Ok(3u));
///
/// let x = SRc::new(4u);
/// let _y = x.clone();
/// assert_eq!(src::try_unwrap(x), Err(SRc::new(4u)));
/// ```
#[inline]
#[experimental]
pub fn try_unwrap<T>(rc: SRc<T>) -> Result<T, SRc<T>> {
    if is_unique(&rc) {
        unsafe {
            let val = ptr::read(&*rc); // copy the contained object
            // destruct the box and skip our Drop
            // we can ignore the refcounts because we know we're unique
            deallocate(rc._ptr as *mut u8, size_of::<RcBox<T>>(),
                        min_align_of::<RcBox<T>>());
            forget(rc);
            Ok(val)
        }
    } else {
        Err(rc)
    }
}

/// Returns a mutable reference to the contained value if the `SRc<T>` is unique.
///
/// Returns `None` if the `SRc<T>` is not unique.
///
/// # Example
///
/// ```
/// use collect::src::{mod, SRc};
///
/// let mut x = SRc::new(3u);
/// *src::get_mut(&mut x).unwrap() = 4u;
/// assert_eq!(*x, 4u);
///
/// let _y = x.clone();
/// assert!(src::get_mut(&mut x).is_none());
/// ```
#[inline]
#[experimental]
pub fn get_mut<'a, T>(rc: &'a mut SRc<T>) -> Option<&'a mut T> {
    if is_unique(rc) {
        let inner = unsafe { &mut *rc._ptr };
        Some(&mut inner.value)
    } else {
        None
    }
}

impl<T: Clone> SRc<T> {
    /// Make a mutable reference from the given `SRc<T>`.
    ///
    /// This is also referred to as a copy-on-write operation because the inner data is cloned if
    /// the reference count is greater than one.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let mut five = SRc::new(5i);
    ///
    /// let mut_five = five.make_unique();
    /// ```
    #[inline]
    #[experimental]
    pub fn make_unique(&mut self) -> &mut T {
        if !is_unique(self) {
            *self = SRc::new((**self).clone())
        }
        // This unsafety is ok because we're guaranteed that the pointer
        // returned is the *only* pointer that will ever be returned to T. Our
        // reference count is guaranteed to be 1 at this point, and we required
        // the `Rc<T>` itself to be `mut`, so we're returning the only possible
        // reference to the inner value.
        let inner = unsafe { &mut *self._ptr };
        &mut inner.value
    }
}

impl<T> BorrowFrom<SRc<T>> for T {
    fn borrow_from(owned: &SRc<T>) -> &T {
        &**owned
    }
}

#[experimental = "Deref is experimental."]
impl<T> Deref<T> for SRc<T> {
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.inner().value
    }
}

// kept out of line to guide inlining.
unsafe fn do_drop<T>(this: &mut SRc<T>) {
    ptr::read(&**this); // destroy the contained object
    deallocate(this._ptr as *mut u8, size_of::<RcBox<T>>(), min_align_of::<RcBox<T>>());
}

#[unsafe_destructor]
#[experimental = "Drop is experimental."]
impl<T> Drop for SRc<T> {
    /// Drops the `SRc<T>`.
    ///
    /// This will decrement the strong reference count. If the strong reference
    /// count becomes zero, `drop`s the inner value.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// {
    ///     let five = SRc::new(5i);
    ///
    ///     // stuff
    ///
    ///     drop(five); // explict drop
    /// }
    /// {
    ///     let five = SRc::new(5i);
    ///
    ///     // stuff
    ///
    /// } // implicit drop
    /// ```
    #[inline]
    fn drop(&mut self) {
        unsafe {
            if !self._ptr.is_null() {
                self.dec_strong();
                if self.strong() == 0 {
                    do_drop(self);
                }
            }
        }
    }
}

#[unstable = "Clone is unstable."]
impl<T> Clone for SRc<T> {
    /// Makes a clone of the `SRc<T>`.
    ///
    /// This increases the strong reference count.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five.clone();
    /// ```
    #[inline]
    fn clone(&self) -> SRc<T> {
        self.inc_strong();
        SRc { _ptr: self._ptr, _nosend: marker::NoSend, _noshare: marker::NoSync }
    }
}

#[stable]
impl<T: Default> Default for SRc<T> {
    /// Creates a new `SRc<T>`, with the `Default` value for `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    /// use std::default::Default;
    ///
    /// let x: SRc<int> = Default::default();
    /// ```
    #[inline]
    #[stable]
    fn default() -> SRc<T> {
        SRc::new(Default::default())
    }
}

#[unstable = "PartialEq is unstable."]
impl<T: PartialEq> PartialEq for SRc<T> {
    /// Equality for two `SRc<T>`s.
    ///
    /// Two `SRc<T>`s are equal if their inner value are equal.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five == SRc::new(5i);
    /// ```
    #[inline(always)]
    fn eq(&self, other: &SRc<T>) -> bool { **self == **other }

    /// Inequality for two `SRc<T>`s.
    ///
    /// Two `SRc<T>`s are unequal if their inner value are unequal.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five != SRc::new(5i);
    /// ```
    #[inline(always)]
    fn ne(&self, other: &SRc<T>) -> bool { **self != **other }
}

#[unstable = "Eq is unstable."]
impl<T: Eq> Eq for SRc<T> {}

#[unstable = "PartialOrd is unstable."]
impl<T: PartialOrd> PartialOrd for SRc<T> {
    /// Partial comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `partial_cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five.partial_cmp(&SRc::new(5i));
    /// ```
    #[inline(always)]
    fn partial_cmp(&self, other: &SRc<T>) -> Option<Ordering> {
        (**self).partial_cmp(&**other)
    }

    /// Less-than comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `<` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five < SRc::new(5i);
    /// ```
    #[inline(always)]
    fn lt(&self, other: &SRc<T>) -> bool { **self < **other }

    /// 'Less-than or equal to' comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `<=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five <= SRc::new(5i);
    /// ```
    #[inline(always)]
    fn le(&self, other: &SRc<T>) -> bool { **self <= **other }

    /// Greater-than comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `>` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five > SRc::new(5i);
    /// ```
    #[inline(always)]
    fn gt(&self, other: &SRc<T>) -> bool { **self > **other }

    /// 'Greater-than or equal to' comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `>=` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five >= SRc::new(5i);
    /// ```
    #[inline(always)]
    fn ge(&self, other: &SRc<T>) -> bool { **self >= **other }
}

#[unstable = "Ord is unstable."]
impl<T: Ord> Ord for SRc<T> {
    /// Comparison for two `SRc<T>`s.
    ///
    /// The two are compared by calling `cmp()` on their inner values.
    ///
    /// # Examples
    ///
    /// ```
    /// use collect::SRc;
    ///
    /// let five = SRc::new(5i);
    ///
    /// five.partial_cmp(&SRc::new(5i));
    /// ```
    #[inline]
    fn cmp(&self, other: &SRc<T>) -> Ordering { (**self).cmp(&**other) }
}

// FIXME (#18248) Make `T` `Sized?`
impl<S: hash::Writer, T: Hash<S>> Hash<S> for SRc<T> {
    #[inline]
    fn hash(&self, state: &mut S) {
        (**self).hash(state);
    }
}

#[experimental = "Show is experimental."]
impl<T: fmt::Show> fmt::Show for SRc<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        (**self).fmt(f)
    }
}

#[doc(hidden)]
trait RcBoxPtr<T> {
    fn inner(&self) -> &RcBox<T>;

    #[inline]
    fn strong(&self) -> uint { self.inner().strong.get() }

    #[inline]
    fn inc_strong(&self) { self.inner().strong.set(self.strong() + 1); }

    #[inline]
    fn dec_strong(&self) { self.inner().strong.set(self.strong() - 1); }
}

impl<T> RcBoxPtr<T> for SRc<T> {
    #[inline(always)]
    fn inner(&self) -> &RcBox<T> { unsafe { &(*self._ptr) } }
}

#[cfg(test)]
#[allow(experimental)]
mod tests {
    use super::{SRc, strong_count};
    use std::cell::RefCell;
    use std::result::Result::{Err, Ok};
    use std::mem::drop;
    use std::clone::Clone;

    #[test]
    fn test_clone() {
        let x = SRc::new(RefCell::new(5i));
        let y = x.clone();
        *x.borrow_mut() = 20;
        assert_eq!(*y.borrow(), 20);
    }

    #[test]
    fn test_simple() {
        let x = SRc::new(5i);
        assert_eq!(*x, 5);
    }

    #[test]
    fn test_simple_clone() {
        let x = SRc::new(5i);
        let y = x.clone();
        assert_eq!(*x, 5);
        assert_eq!(*y, 5);
    }

    #[test]
    fn test_destructor() {
        let x = SRc::new(box 5i);
        assert_eq!(**x, 5);
    }

    #[test]
    fn is_unique() {
        let x = SRc::new(3u);
        assert!(super::is_unique(&x));
        let y = x.clone();
        assert!(!super::is_unique(&x));
        drop(y);
        assert!(super::is_unique(&x));
    }

    #[test]
    fn test_strong_count() {
        let a = SRc::new(0u32);
        assert!(strong_count(&a) == 1);
        let b = a.clone();
        assert!(strong_count(&a) == 2);
        assert!(strong_count(&b) == 2);
        drop(a);
        assert!(strong_count(&b) == 1);
        let c = b.clone();
        assert!(strong_count(&b) == 2);
        assert!(strong_count(&c) == 2);
    }

    #[test]
    fn try_unwrap() {
        let x = SRc::new(3u);
        assert_eq!(super::try_unwrap(x), Ok(3u));
        let x = SRc::new(4u);
        let _y = x.clone();
        assert_eq!(super::try_unwrap(x), Err(SRc::new(4u)));
    }

    #[test]
    fn get_mut() {
        let mut x = SRc::new(3u);
        *super::get_mut(&mut x).unwrap() = 4u;
        assert_eq!(*x, 4u);
        let y = x.clone();
        assert!(super::get_mut(&mut x).is_none());
        drop(y);
        assert!(super::get_mut(&mut x).is_some());
    }

    #[test]
    fn test_cowrc_clone_make_unique() {
        let mut cow0 = SRc::new(75u);
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
    fn test_cowrc_clone_unique2() {
        let mut cow0 = SRc::new(75u);
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
}
