// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! A structure for holding a set of enum variants.
//!
//! This module defines a container which uses an efficient bit mask
//! representation to hold C-like enum variants.

use core::fmt;
use core::hash;
use core::marker::PhantomData;
use core::num::Int;
use core::u32;
use std::iter::{self, IntoIterator};
use std::ops;

// FIXME(conventions): implement union family of methods? (general design may be wrong here)

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord)]
/// A specialized set implementation to use enum types.
pub struct EnumSet<E> {
    // We must maintain the invariant that no bits are set
    // for which no variant exists
    bits: u32,
    phantom: PhantomData<*mut E>,
}

impl<E:CLike+fmt::Debug> fmt::Debug for EnumSet<E> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(fmt, "{{"));
        let mut first = true;
        for e in self.iter() {
            if !first {
                try!(write!(fmt, ", "));
            }
            try!(write!(fmt, "{:?}", e));
            first = false;
        }
        write!(fmt, "}}")
    }
}

impl<E: CLike> hash::Hash for EnumSet<E> {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.bits.hash(state);
    }
}

/// An interface for casting C-like enum to u32 and back. A typical
/// implementation can be seen below:
///
/// ```{rust}
/// # use collect::enum_set::CLike;
/// use std::mem;
///
/// #[derive(Copy)]
/// #[repr(u32)]
/// enum Foo {
///     A, B, C
/// }
///
/// impl CLike for Foo {
///     fn to_u32(&self) -> u32 {
///         *self as u32
///     }
///     unsafe fn from_u32(v: u32) -> Foo {
///         mem::transmute(v)
///     }
/// }
/// ```
pub trait CLike {
    /// Converts a C-like enum to a `u32`.
    fn to_u32(&self) -> u32;
    /// Converts a `u32` to a C-like enum. This method only needs to be safe
    /// for possible return values of `to_u32` of this trait.
    unsafe fn from_u32(u32) -> Self;
}

fn bit<E:CLike>(e: &E) -> u32 {
    let value = e.to_u32();
    assert!(value < u32::BITS as u32,
            "EnumSet only supports up to {} variants.", u32::BITS - 1);
    1 << value
}

impl<E:CLike> EnumSet<E> {
    /// Returns an empty `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn new() -> EnumSet<E> {
        EnumSet::new_with_bits(0)
    }

    fn new_with_bits(bits: u32) -> EnumSet<E> {
        EnumSet { bits: bits, phantom: PhantomData }
    }

    /// Returns the number of elements in the given `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn len(&self) -> usize {
        self.bits.count_ones() as usize
    }

    /// Returns true if the `EnumSet` is empty.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    pub fn clear(&mut self) {
        self.bits = 0;
    }

    /// Returns `false` if the `EnumSet` contains any enum of the given `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_disjoint(&self, other: &EnumSet<E>) -> bool {
        (self.bits & other.bits) == 0
    }

    /// Returns `true` if a given `EnumSet` is included in this `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_superset(&self, other: &EnumSet<E>) -> bool {
        (self.bits & other.bits) == other.bits
    }

    /// Returns `true` if this `EnumSet` is included in the given `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_subset(&self, other: &EnumSet<E>) -> bool {
        other.is_superset(self)
    }

    /// Returns the union of both `EnumSets`.
    pub fn union(&self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits | e.bits)
    }

    /// Returns the intersection of both `EnumSets`.
    pub fn intersection(&self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits & e.bits)
    }

    /// Adds an enum to the `EnumSet`, and returns `true` if it wasn't there before
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn insert(&mut self, e: E) -> bool {
        let result = !self.contains(&e);
        self.bits |= bit(&e);
        result
    }

    /// Removes an enum from the EnumSet
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn remove(&mut self, e: &E) -> bool {
        let result = self.contains(e);
        self.bits &= !bit(e);
        result
    }

    /// Returns `true` if an `EnumSet` contains a given enum.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn contains(&self, e: &E) -> bool {
        (self.bits & bit(e)) != 0
    }

    /// Returns an iterator over an `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn iter(&self) -> Iter<E> {
        Iter::new(self.bits)
    }
}

impl<E:CLike> ops::Sub for EnumSet<E> {
    type Output = EnumSet<E>;

    fn sub(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits & !e.bits)
    }
}

impl<E:CLike> ops::BitOr for EnumSet<E> {
    type Output = EnumSet<E>;

    fn bitor(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits | e.bits)
    }
}

impl<E:CLike> ops::BitAnd for EnumSet<E> {
    type Output = EnumSet<E>;

    fn bitand(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits & e.bits)
    }
}

impl<E:CLike> ops::BitXor for EnumSet<E> {
    type Output = EnumSet<E>;

    fn bitxor(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet::new_with_bits(self.bits ^ e.bits)
    }
}

/// An iterator over an EnumSet
pub struct Iter<E> {
    index: u32,
    bits: u32,
    phantom: PhantomData<*mut E>,
}

impl<E:CLike> Iter<E> {
    fn new(bits: u32) -> Iter<E> {
        Iter { index: 0, bits: bits, phantom: PhantomData }
    }
}

impl<E:CLike> Iterator for Iter<E> {
    type Item = E;
    fn next(&mut self) -> Option<E> {
        if self.bits == 0 {
            return None;
        }
        while (self.bits & 1) == 0 {
            self.index += 1;
            self.bits >>= 1;
        }
        // Safe because of the invariant that only valid bits are set (see
        // comment on the `bit` member of this struct).
        let elem = unsafe { CLike::from_u32(self.index) };
        self.index += 1;
        self.bits >>= 1;
        Some(elem)
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = self.bits.count_ones() as usize;
        (exact, Some(exact))
    }
}

impl<E:CLike> iter::FromIterator<E> for EnumSet<E> {
    fn from_iter<I: IntoIterator<Item=E>>(iterator: I) -> EnumSet<E> {
        let mut ret = EnumSet::new();
        ret.extend(iterator);
        ret
    }
}

impl<E:CLike> Extend<E> for EnumSet<E> {
    fn extend<I: IntoIterator<Item=E>>(&mut self, iter: I) {
        for element in iter {
            self.insert(element);
        }
    }
}

impl<'a, E:CLike> IntoIterator for &'a EnumSet<E> {
    type Item = E;
    type IntoIter = Iter<E>;
    fn into_iter(self) -> Iter<E> { self.iter() }
}

#[cfg(test)]
mod test {
    use self::Foo::*;
    use std::mem;

    use super::{EnumSet, CLike};

    #[derive(PartialEq, Debug)]
    #[repr(u32)]
    enum Foo {
        A, B, C
    }

    impl Copy for Foo {}

    impl CLike for Foo {
        fn to_u32(&self) -> u32 {
            *self as u32
        }

        fn from_u32(v: u32) -> Foo {
            unsafe { mem::transmute(v) }
        }
    }

    #[test]
    fn test_new() {
        let e: EnumSet<Foo> = EnumSet::new();
        assert!(e.is_empty());
    }

    #[test]
    fn test_debug() {
        let mut e = EnumSet::new();
        assert_eq!("{}", format!("{:?}", e));
        e.insert(A);
        assert_eq!("{A}", format!("{:?}", e));
        e.insert(C);
        assert_eq!("{A, C}", format!("{:?}", e));
    }

    #[test]
    fn test_len() {
        let mut e = EnumSet::new();
        assert_eq!(e.len(), 0);
        e.insert(A);
        e.insert(B);
        e.insert(C);
        assert_eq!(e.len(), 3);
        e.remove(&A);
        assert_eq!(e.len(), 2);
        e.clear();
        assert_eq!(e.len(), 0);
    }

    ///////////////////////////////////////////////////////////////////////////
    // intersect

    #[test]
    fn test_two_empties_do_not_intersect() {
        let e1: EnumSet<Foo> = EnumSet::new();
        let e2: EnumSet<Foo> = EnumSet::new();
        assert!(e1.is_disjoint(&e2));
    }

    #[test]
    fn test_empty_does_not_intersect_with_full() {
        let e1: EnumSet<Foo> = EnumSet::new();

        let mut e2: EnumSet<Foo> = EnumSet::new();
        e2.insert(A);
        e2.insert(B);
        e2.insert(C);

        assert!(e1.is_disjoint(&e2));
    }

    #[test]
    fn test_disjoint_intersects() {
        let mut e1: EnumSet<Foo> = EnumSet::new();
        e1.insert(A);

        let mut e2: EnumSet<Foo> = EnumSet::new();
        e2.insert(B);

        assert!(e1.is_disjoint(&e2));
    }

    #[test]
    fn test_overlapping_intersects() {
        let mut e1: EnumSet<Foo> = EnumSet::new();
        e1.insert(A);

        let mut e2: EnumSet<Foo> = EnumSet::new();
        e2.insert(A);
        e2.insert(B);

        assert!(!e1.is_disjoint(&e2));
    }

    ///////////////////////////////////////////////////////////////////////////
    // contains and contains_elem

    #[test]
    fn test_superset() {
        let mut e1: EnumSet<Foo> = EnumSet::new();
        e1.insert(A);

        let mut e2: EnumSet<Foo> = EnumSet::new();
        e2.insert(A);
        e2.insert(B);

        let mut e3: EnumSet<Foo> = EnumSet::new();
        e3.insert(C);

        assert!(e1.is_subset(&e2));
        assert!(e2.is_superset(&e1));
        assert!(!e3.is_superset(&e2));
        assert!(!e2.is_superset(&e3));
    }

    #[test]
    fn test_contains() {
        let mut e1: EnumSet<Foo> = EnumSet::new();
        e1.insert(A);
        assert!(e1.contains(&A));
        assert!(!e1.contains(&B));
        assert!(!e1.contains(&C));

        e1.insert(A);
        e1.insert(B);
        assert!(e1.contains(&A));
        assert!(e1.contains(&B));
        assert!(!e1.contains(&C));
    }

    ///////////////////////////////////////////////////////////////////////////
    // iter

    #[test]
    fn test_iterator() {
        let mut e1: EnumSet<Foo> = EnumSet::new();

        let elems: Vec<Foo> = e1.iter().collect();
        assert!(elems.is_empty());

        e1.insert(A);
        let elems: Vec<_> = e1.iter().collect();
        assert_eq!(vec![A], elems);

        e1.insert(C);
        let elems: Vec<_> = e1.iter().collect();
        assert_eq!(vec![A,C], elems);

        e1.insert(C);
        let elems: Vec<_> = e1.iter().collect();
        assert_eq!(vec![A,C], elems);

        e1.insert(B);
        let elems: Vec<_> = e1.iter().collect();
        assert_eq!(vec![A,B,C], elems);
    }

    ///////////////////////////////////////////////////////////////////////////
    // operators

    #[test]
    fn test_operators() {
        let mut e1: EnumSet<Foo> = EnumSet::new();
        e1.insert(A);
        e1.insert(C);

        let mut e2: EnumSet<Foo> = EnumSet::new();
        e2.insert(B);
        e2.insert(C);

        let e_union = e1 | e2;
        let elems: Vec<_> = e_union.iter().collect();
        assert_eq!(vec![A,B,C], elems);

        let e_intersection = e1 & e2;
        let elems: Vec<_> = e_intersection.iter().collect();
        assert_eq!(vec![C], elems);

        // Another way to express intersection
        let e_intersection = e1 - (e1 - e2);
        let elems: Vec<_> = e_intersection.iter().collect();
        assert_eq!(vec![C], elems);

        let e_subtract = e1 - e2;
        let elems: Vec<_> = e_subtract.iter().collect();
        assert_eq!(vec![A], elems);

        // Bitwise XOR of two sets, aka symmetric difference
        let e_symmetric_diff = e1 ^ e2;
        let elems: Vec<_> = e_symmetric_diff.iter().collect();
        assert_eq!(vec![A,B], elems);

        // Another way to express symmetric difference
        let e_symmetric_diff = (e1 - e2) | (e2 - e1);
        let elems: Vec<_> = e_symmetric_diff.iter().collect();
        assert_eq!(vec![A,B], elems);

        // Yet another way to express symmetric difference
        let e_symmetric_diff = (e1 | e2) - (e1 & e2);
        let elems: Vec<_> = e_symmetric_diff.iter().collect();
        assert_eq!(vec![A,B], elems);
    }

    #[test]
    #[should_panic]
    fn test_overflow() {
        #[allow(dead_code)]
        #[repr(u32)]
        enum Bar {
            V00, V01, V02, V03, V04, V05, V06, V07, V08, V09,
            V10, V11, V12, V13, V14, V15, V16, V17, V18, V19,
            V20, V21, V22, V23, V24, V25, V26, V27, V28, V29,
            V30, V31, V32, V33, V34, V35, V36, V37, V38, V39,
        }

        impl Copy for Bar {}

        impl CLike for Bar {
            fn to_u32(&self) -> u32 {
                *self as u32
            }
            unsafe fn from_u32(v: u32) -> Bar {
                mem::transmute(v)
            }
        }
        let mut set = EnumSet::new();
        set.insert(Bar::V32);
    }
}
