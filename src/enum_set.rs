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

use core::prelude::*;
use core::fmt;
use core::num::Int;

// FIXME(contentions): implement union family of methods? (general design may be wrong here)

#[deriving(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
/// A specialized set implementation to use enum types.
pub struct EnumSet<E> {
    // We must maintain the invariant that no bits are set
    // for which no variant exists
    bits: uint
}

impl<E> Copy for EnumSet<E> {}

impl<E:CLike+fmt::Show> fmt::Show for EnumSet<E> {
    fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(fmt, "{{"));
        let mut first = true;
        for e in self.iter() {
            if !first {
                try!(write!(fmt, ", "));
            }
            try!(write!(fmt, "{}", e));
            first = false;
        }
        write!(fmt, "}}")
    }
}

/// An interface for casting C-like enum to uint and back.
/// A typically implementation is as below.
///
/// ```{rust,ignore}
/// #[repr(uint)]
/// enum Foo {
///     A, B, C
/// }
///
/// impl CLike for Foo {
///     fn to_uint(&self) -> uint {
///         *self as uint
///     }
///
///     fn from_uint(v: uint) -> Foo {
///         unsafe { mem::transmute(v) }
///     }
/// }
/// ```
pub trait CLike {
    /// Converts a C-like enum to a `uint`.
    fn to_uint(&self) -> uint;
    /// Converts a `uint` to a C-like enum.
    fn from_uint(uint) -> Self;
}

fn bit<E:CLike>(e: &E) -> uint {
    use core::uint;
    let value = e.to_uint();
    assert!(value < uint::BITS,
            "EnumSet only supports up to {} variants.", uint::BITS - 1);
    1 << value
}

impl<E:CLike> EnumSet<E> {
    /// Deprecated: Renamed to `new`.
    #[deprecated = "Renamed to `new`"]
    pub fn empty() -> EnumSet<E> {
        EnumSet::new()
    }

    /// Returns an empty `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn new() -> EnumSet<E> {
        EnumSet {bits: 0}
    }

    /// Returns the number of elements in the given `EnumSet`.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn len(&self) -> uint {
        self.bits.count_ones()
    }

    /// Returns true if the `EnumSet` is empty.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_empty(&self) -> bool {
        self.bits == 0
    }

    pub fn clear(&mut self) {
        self.bits = 0;
    }

    /// Returns `true` if the `EnumSet` contains any enum of the given `EnumSet`.
    /// Deprecated: Use `is_disjoint`.
    #[deprecated = "Use `is_disjoint`"]
    pub fn intersects(&self, e: EnumSet<E>) -> bool {
        !self.is_disjoint(&e)
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
        EnumSet {bits: self.bits | e.bits}
    }

    /// Returns the intersection of both `EnumSets`.
    pub fn intersection(&self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits & e.bits}
    }

    /// Deprecated: Use `insert`.
    #[deprecated = "Use `insert`"]
    pub fn add(&mut self, e: E) {
        self.insert(e);
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

    /// Deprecated: use `contains`.
    #[deprecated = "use `contains"]
    pub fn contains_elem(&self, e: E) -> bool {
        self.contains(&e)
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

// NOTE(stage0): Remove impl after a snapshot
#[cfg(stage0)]
impl<E:CLike> Sub<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn sub(&self, e: &EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits & !e.bits}
    }
}

#[cfg(not(stage0))]  // NOTE(stage0): Remove cfg after a snapshot
impl<E:CLike> Sub<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn sub(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits & !e.bits}
    }
}

// NOTE(stage0): Remove impl after a snapshot
#[cfg(stage0)]
impl<E:CLike> BitOr<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitor(&self, e: &EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits | e.bits}
    }
}

#[cfg(not(stage0))]  // NOTE(stage0): Remove cfg after a snapshot
impl<E:CLike> BitOr<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitor(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits | e.bits}
    }
}

// NOTE(stage0): Remove impl after a snapshot
#[cfg(stage0)]
impl<E:CLike> BitAnd<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitand(&self, e: &EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits & e.bits}
    }
}

#[cfg(not(stage0))]  // NOTE(stage0): Remove cfg after a snapshot
impl<E:CLike> BitAnd<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitand(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits & e.bits}
    }
}

// NOTE(stage0): Remove impl after a snapshot
#[cfg(stage0)]
impl<E:CLike> BitXor<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitxor(&self, e: &EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits ^ e.bits}
    }
}

#[cfg(not(stage0))]  // NOTE(stage0): Remove cfg after a snapshot
impl<E:CLike> BitXor<EnumSet<E>, EnumSet<E>> for EnumSet<E> {
    fn bitxor(self, e: EnumSet<E>) -> EnumSet<E> {
        EnumSet {bits: self.bits ^ e.bits}
    }
}

/// An iterator over an EnumSet
pub struct Iter<E> {
    index: uint,
    bits: uint,
}

impl<E:CLike> Iter<E> {
    fn new(bits: uint) -> Iter<E> {
        Iter { index: 0, bits: bits }
    }
}

impl<E:CLike> Iterator<E> for Iter<E> {
    fn next(&mut self) -> Option<E> {
        if self.bits == 0 {
            return None;
        }

        while (self.bits & 1) == 0 {
            self.index += 1;
            self.bits >>= 1;
        }
        let elem = CLike::from_uint(self.index);
        self.index += 1;
        self.bits >>= 1;
        Some(elem)
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        let exact = self.bits.count_ones();
        (exact, Some(exact))
    }
}

impl<E:CLike> FromIterator<E> for EnumSet<E> {
    fn from_iter<I:Iterator<E>>(iterator: I) -> EnumSet<E> {
        let mut ret = EnumSet::new();
        ret.extend(iterator);
        ret
    }
}

impl<E:CLike> Extend<E> for EnumSet<E> {
    fn extend<I: Iterator<E>>(&mut self, mut iterator: I) {
        for element in iterator {
            self.insert(element);
        }
    }
}

#[cfg(test)]
mod test {
    use std::prelude::*;
    use self::Foo::*;
    use std::mem;

    use super::{EnumSet, CLike};

    #[deriving(PartialEq, Show)]
    #[repr(uint)]
    enum Foo {
        A, B, C
    }

    impl Copy for Foo {}

    impl CLike for Foo {
        fn to_uint(&self) -> uint {
            *self as uint
        }

        fn from_uint(v: uint) -> Foo {
            unsafe { mem::transmute(v) }
        }
    }

    #[test]
    fn test_new() {
        let e: EnumSet<Foo> = EnumSet::new();
        assert!(e.is_empty());
    }

    #[test]
    fn test_show() {
        let mut e = EnumSet::new();
        assert_eq!("{}", e.to_string());
        e.insert(A);
        assert_eq!("{A}", e.to_string());
        e.insert(C);
        assert_eq!("{A, C}", e.to_string());
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
    #[should_fail]
    fn test_overflow() {
        #[allow(dead_code)]
        #[repr(uint)]
        enum Bar {
            V00, V01, V02, V03, V04, V05, V06, V07, V08, V09,
            V10, V11, V12, V13, V14, V15, V16, V17, V18, V19,
            V20, V21, V22, V23, V24, V25, V26, V27, V28, V29,
            V30, V31, V32, V33, V34, V35, V36, V37, V38, V39,
            V40, V41, V42, V43, V44, V45, V46, V47, V48, V49,
            V50, V51, V52, V53, V54, V55, V56, V57, V58, V59,
            V60, V61, V62, V63, V64, V65, V66, V67, V68, V69,
        }

        impl Copy for Bar {}

        impl CLike for Bar {
            fn to_uint(&self) -> uint {
                *self as uint
            }

            fn from_uint(v: uint) -> Bar {
                unsafe { mem::transmute(v) }
            }
        }
        let mut set = EnumSet::new();
        set.insert(Bar::V64);
    }
}
