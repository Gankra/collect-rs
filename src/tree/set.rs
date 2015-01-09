// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::cmp::Ordering::{self, Less, Equal, Greater};
use std::default::Default;
use std::fmt;
use std::fmt::Show;
use std::iter::Peekable;
use std::iter;
use std::hash::{Hash, Hasher, Writer};
use std::ops;

use compare::{Compare, Natural};
use tree_map::{self, TreeMap};

// FIXME(conventions): implement bounded iterators
// FIXME(conventions): replace rev_iter(_mut) by making iter(_mut) DoubleEnded

/// An implementation of a set on top of the `TreeMap` container.
///
/// # Examples
///
/// ```{rust}
/// use collect::TreeSet;
///
/// let mut set = TreeSet::new();
///
/// set.insert(2);
/// set.insert(1);
/// set.insert(3);
///
/// for i in set.iter() {
///    println!("{}", i) // prints 1, then 2, then 3
/// }
///
/// set.remove(&3);
///
/// if !set.contains(&3) {
///     println!("set does not contain a 3 anymore");
/// }
/// ```
///
/// A `TreeSet` can also be used with a custom ordering:
///
/// ```rust
/// use collect::TreeSet;
///
/// struct Troll<'a> {
///     name: &'a str,
///     level: usize,
/// }
///
/// let mut trolls = TreeSet::with_comparator(|&: l: &Troll, r: &Troll| l.level.cmp(&r.level));
///
/// trolls.insert(Troll { name: "Orgarr", level: 2 });
/// trolls.insert(Troll { name: "Blargarr", level: 3 });
/// trolls.insert(Troll { name: "Kron the Smelly One", level: 4 });
/// trolls.insert(Troll { name: "Wartilda", level: 1 });
///
/// println!("You are facing {} trolls!", trolls.len());
///
/// // Print the trolls, ordered by level with smallest level first
/// for x in trolls.iter() {
///     println!("level {}: {}!", x.level, x.name);
/// }
///
/// // Kill all trolls
/// trolls.clear();
/// assert_eq!(trolls.len(), 0);
/// ```
#[derive(Clone)]
pub struct TreeSet<T, C: Compare<T> = Natural<T>> {
    map: TreeMap<T, (), C>
}

// FIXME: determine what `PartialEq` means for comparator-based `TreeSet`s
impl<T: PartialEq + Ord> PartialEq for TreeSet<T> {
    #[inline]
    fn eq(&self, other: &TreeSet<T>) -> bool { self.map == other.map }
}

// FIXME: determine what `Eq` means for comparator-based `TreeSet`s
impl<T: Eq + Ord> Eq for TreeSet<T> {}

// FIXME: determine what `PartialOrd` means for comparator-based `TreeSet`s
impl<T: Ord> PartialOrd for TreeSet<T> {
    #[inline]
    fn partial_cmp(&self, other: &TreeSet<T>) -> Option<Ordering> {
        self.map.partial_cmp(&other.map)
    }
}

// FIXME: determine what `Ord` means for comparator-based `TreeSet`s
impl<T: Ord> Ord for TreeSet<T> {
    #[inline]
    fn cmp(&self, other: &TreeSet<T>) -> Ordering {
        iter::order::cmp(self.iter(), other.iter())
    }
}

impl<T: Show, C> Show for TreeSet<T, C> where C: Compare<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, x) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}", *x));
        }

        write!(f, "}}")
    }
}

impl<T, C> Default for TreeSet<T, C> where C: Compare<T> + Default {
    #[inline]
    fn default() -> TreeSet<T, C> { TreeSet::with_comparator(Default::default()) }
}

impl<T: Ord> TreeSet<T> {
    /// Creates an empty `TreeSet` ordered according to the natural order of its values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let mut set: TreeSet<isize> = TreeSet::new();
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn new() -> TreeSet<T> { TreeSet::with_comparator(Natural) }
}

impl<T, C> TreeSet<T, C> where C: Compare<T> {
    /// Creates an empty `TreeSet` ordered according to the given comparator.
    pub fn with_comparator(cmp: C) -> TreeSet<T, C> {
        TreeSet { map: TreeMap::with_comparator(cmp) }
    }

    /// Returns the comparator according to which the `TreeSet` is ordered.
    pub fn comparator(&self) -> &C { self.map.comparator() }

    /// Gets a lazy iterator over the values in the set, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let set: TreeSet<isize> = [1, 4, 3, 5, 2].iter().map(|&x| x).collect();
    ///
    /// // Will print in ascending order.
    /// for x in set.iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn iter<'a>(&'a self) -> Iter<'a, T> {
        Iter { iter: self.map.iter() }
    }

    /// Gets a lazy iterator over the values in the set, in descending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let set: TreeSet<isize> = [1, 4, 3, 5, 2].iter().map(|&x| x).collect();
    ///
    /// // Will print in descending order.
    /// for x in set.rev_iter() {
    ///     println!("{}", x);
    /// }
    /// ```
    #[inline]
    pub fn rev_iter<'a>(&'a self) -> RevIter<'a, T> {
        RevIter { iter: self.map.rev_iter() }
    }

    /// Creates a consuming iterator, that is, one that moves each value out of the
    /// set in ascending order. The set cannot be used after calling this.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let set: TreeSet<isize> = [1, 4, 3, 5, 2].iter().map(|&x| x).collect();
    ///
    /// // Not possible with a regular `.iter()`
    /// let v: Vec<isize> = set.into_iter().collect();
    /// assert_eq!(v, vec![1, 2, 3, 4, 5]);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn into_iter(self) -> IntoIter<T> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((T, ())) -> T = first; // coerce to fn pointer

        IntoIter(self.map.into_iter().map(first))
    }

    /// Gets a lazy iterator pointing to the first value not less than `v` (greater or equal).
    /// If all elements in the set are less than `v` empty iterator is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let set: TreeSet<isize> = [2, 4, 6, 8].iter().map(|&x| x).collect();
    ///
    /// assert_eq!(set.lower_bound(&4).next(), Some(&4));
    /// assert_eq!(set.lower_bound(&5).next(), Some(&6));
    /// assert_eq!(set.lower_bound(&10).next(), None);
    /// ```
    #[inline]
    pub fn lower_bound<'a>(&'a self, v: &T) -> Iter<'a, T> {
        Iter { iter: self.map.lower_bound(v) }
    }

    /// Gets a lazy iterator pointing to the first value greater than `v`.
    /// If all elements in the set are less than or equal to `v` an
    /// empty iterator is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    /// let set: TreeSet<isize> = [2, 4, 6, 8].iter().map(|&x| x).collect();
    ///
    /// assert_eq!(set.upper_bound(&4).next(), Some(&6));
    /// assert_eq!(set.upper_bound(&5).next(), Some(&6));
    /// assert_eq!(set.upper_bound(&10).next(), None);
    /// ```
    #[inline]
    pub fn upper_bound<'a>(&'a self, v: &T) -> Iter<'a, T> {
        Iter { iter: self.map.upper_bound(v) }
    }

    /// Visits the values representing the difference, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let b: TreeSet<isize> = [3, 4, 5].iter().map(|&x| x).collect();
    ///
    /// // Can be seen as `a - b`.
    /// for x in a.difference(&b) {
    ///     println!("{}", x); // Print 1 then 2
    /// }
    ///
    /// let diff: TreeSet<isize> = a.difference(&b).map(|&x| x).collect();
    /// assert_eq!(diff, [1, 2].iter().map(|&x| x).collect());
    ///
    /// // Note that difference is not symmetric,
    /// // and `b - a` means something else:
    /// let diff: TreeSet<isize> = b.difference(&a).map(|&x| x).collect();
    /// assert_eq!(diff, [4, 5].iter().map(|&x| x).collect());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn difference<'a>(&'a self, other: &'a TreeSet<T, C>)
        -> Difference<'a, T, C> where C: Eq {
        assert!(self.comparator() == other.comparator());
        Difference {
            a: self.iter().peekable(),
            b: other.iter().peekable(),
            cmp: self.comparator(),
        }
    }

    /// Visits the values representing the symmetric difference, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let b: TreeSet<isize> = [3, 4, 5].iter().map(|&x| x).collect();
    ///
    /// // Print 1, 2, 4, 5 in ascending order.
    /// for x in a.symmetric_difference(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let diff1: TreeSet<isize> = a.symmetric_difference(&b).map(|&x| x).collect();
    /// let diff2: TreeSet<isize> = b.symmetric_difference(&a).map(|&x| x).collect();
    ///
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, [1, 2, 4, 5].iter().map(|&x| x).collect());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn symmetric_difference<'a>(&'a self, other: &'a TreeSet<T, C>)
        -> SymmetricDifference<'a, T, C> where C: Eq {
        assert!(self.comparator() == other.comparator());
        SymmetricDifference {
            a: self.iter().peekable(),
            b: other.iter().peekable(),
            cmp: self.comparator(),
        }
    }

    /// Visits the values representing the intersection, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let b: TreeSet<isize> = [2, 3, 4].iter().map(|&x| x).collect();
    ///
    /// // Print 2, 3 in ascending order.
    /// for x in a.intersection(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let diff: TreeSet<isize> = a.intersection(&b).map(|&x| x).collect();
    /// assert_eq!(diff, [2, 3].iter().map(|&x| x).collect());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn intersection<'a>(&'a self, other: &'a TreeSet<T, C>)
        -> Intersection<'a, T, C> where C: Eq {
        assert!(self.comparator() == other.comparator());
        Intersection {
            a: self.iter().peekable(),
            b: other.iter().peekable(),
            cmp: self.comparator(),
        }
    }

    /// Visits the values representing the union, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let b: TreeSet<isize> = [3, 4, 5].iter().map(|&x| x).collect();
    ///
    /// // Print 1, 2, 3, 4, 5 in ascending order.
    /// for x in a.union(&b) {
    ///     println!("{}", x);
    /// }
    ///
    /// let diff: TreeSet<isize> = a.union(&b).map(|&x| x).collect();
    /// assert_eq!(diff, [1, 2, 3, 4, 5].iter().map(|&x| x).collect());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn union<'a>(&'a self, other: &'a TreeSet<T, C>) -> Union<'a, T, C>
        where C: Eq {
        assert!(self.comparator() == other.comparator());
        Union {
            a: self.iter().peekable(),
            b: other.iter().peekable(),
            cmp: self.comparator(),
        }
    }

    /// Return the number of elements in the set
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let mut v = TreeSet::new();
    /// assert_eq!(v.len(), 0);
    /// v.insert(1);
    /// assert_eq!(v.len(), 1);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn len(&self) -> usize { self.map.len() }

    /// Returns true if the set contains no elements
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let mut v = TreeSet::new();
    /// assert!(v.is_empty());
    /// v.insert(1);
    /// assert!(!v.is_empty());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clears the set, removing all values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let mut v = TreeSet::new();
    /// v.insert(1);
    /// v.clear();
    /// assert!(v.is_empty());
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn clear(&mut self) { self.map.clear() }

    /// Returns `true` if the set contains a value.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let set: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// assert_eq!(set.contains(&1), true);
    /// assert_eq!(set.contains(&4), false);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
        where C: Compare<Q, T>
    {
        self.map.contains_key(value)
    }

    /// Returns `true` if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let mut b: TreeSet<isize> = TreeSet::new();
    ///
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(4);
    /// assert_eq!(a.is_disjoint(&b), true);
    /// b.insert(1);
    /// assert_eq!(a.is_disjoint(&b), false);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_disjoint(&self, other: &TreeSet<T, C>) -> bool where C: Eq {
        self.intersection(other).next().is_none()
    }

    /// Returns `true` if the set is a subset of another.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let sup: TreeSet<isize> = [1, 2, 3].iter().map(|&x| x).collect();
    /// let mut set: TreeSet<isize> = TreeSet::new();
    ///
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(2);
    /// assert_eq!(set.is_subset(&sup), true);
    /// set.insert(4);
    /// assert_eq!(set.is_subset(&sup), false);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_subset(&self, other: &TreeSet<T, C>) -> bool where C: Eq {
        assert!(self.comparator() == other.comparator());
        let mut x = self.iter();
        let mut y = other.iter();
        let mut a = x.next();
        let mut b = y.next();
        while a.is_some() {
            if b.is_none() {
                return false;
            }

            let a1 = a.unwrap();
            let b1 = b.unwrap();

            match self.comparator().compare(b1, a1) {
                Less => (),
                Greater => return false,
                Equal  => a = x.next(),
            }

            b = y.next();
        }
        true
    }

    /// Returns `true` if the set is a superset of another.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let sub: TreeSet<isize> = [1, 2].iter().map(|&x| x).collect();
    /// let mut set: TreeSet<isize> = TreeSet::new();
    ///
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(0);
    /// set.insert(1);
    /// assert_eq!(set.is_superset(&sub), false);
    ///
    /// set.insert(2);
    /// assert_eq!(set.is_superset(&sub), true);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_superset(&self, other: &TreeSet<T, C>) -> bool where C: Eq {
        other.is_subset(self)
    }

    /// Adds a value to the set. Returns `true` if the value was not already
    /// present in the set.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let mut set = TreeSet::new();
    ///
    /// assert_eq!(set.insert(2), true);
    /// assert_eq!(set.insert(2), false);
    /// assert_eq!(set.len(), 1);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn insert(&mut self, value: T) -> bool { self.map.insert(value, ()).is_none() }

    /// Removes a value from the set. Returns `true` if the value was
    /// present in the set.
    ///
    /// The value may be any borrowed form of the set's value type,
    /// but the ordering on the borrowed form *must* match the
    /// ordering on the value type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let mut set = TreeSet::new();
    ///
    /// set.insert(2);
    /// assert_eq!(set.remove(&2), true);
    /// assert_eq!(set.remove(&2), false);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn remove<Q: ?Sized>(&mut self, value: &Q) -> bool
        where C: Compare<Q, T>
    {
        self.map.remove(value).is_some()
    }
}

/// A lazy forward iterator over a set.
pub struct Iter<'a, T:'a> {
    iter: tree_map::Iter<'a, T, ()>
}

/// A lazy backward iterator over a set.
pub struct RevIter<'a, T:'a> {
    iter: tree_map::RevIter<'a, T, ()>
}

/// A lazy forward iterator over a set that consumes the set while iterating.
pub struct IntoIter<T>(iter::Map<(T, ()), T, tree_map::IntoIter<T, ()>, fn((T, ())) -> T>);

/// A lazy iterator producing elements in the set difference (in-order).
pub struct Difference<'a, T:'a, C:'a> {
    a: Peekable<&'a T, Iter<'a, T>>,
    b: Peekable<&'a T, Iter<'a, T>>,
    cmp: &'a C,
}

/// A lazy iterator producing elements in the set symmetric difference (in-order).
pub struct SymmetricDifference<'a, T:'a, C:'a> {
    a: Peekable<&'a T, Iter<'a, T>>,
    b: Peekable<&'a T, Iter<'a, T>>,
    cmp: &'a C,
}

/// A lazy iterator producing elements in the set intersection (in-order).
pub struct Intersection<'a, T:'a, C:'a> {
    a: Peekable<&'a T, Iter<'a, T>>,
    b: Peekable<&'a T, Iter<'a, T>>,
    cmp: &'a C,
}

/// A lazy iterator producing elements in the set union (in-order).
pub struct Union<'a, T:'a, C:'a> {
    a: Peekable<&'a T, Iter<'a, T>>,
    b: Peekable<&'a T, Iter<'a, T>>,
    cmp: &'a C,
}

/// Compare `x` and `y`, but return `short` if x is None and `long` if y is None
fn cmp_opt<T, C: Compare<T>>(x: Option<& &T>, y: Option<& &T>,
                        short: Ordering, long: Ordering, cmp: &C) -> Ordering {
    match (x, y) {
        (None    , _       ) => short,
        (_       , None    ) => long,
        (Some(x1), Some(y1)) => cmp.compare(*x1, *y1),
    }
}


impl<'a, T> Iterator for Iter<'a, T> {
    type Item = &'a T;
    #[inline] fn next(&mut self) -> Option<&'a T> { self.iter.next().map(|(value, _)| value) }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a, T> Iterator for RevIter<'a, T> {
    type Item = &'a T;
    #[inline] fn next(&mut self) -> Option<&'a T> { self.iter.next().map(|(value, _)| value) }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;
    #[inline] fn next(&mut self) -> Option<T> { self.0.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, T, C> Iterator for Difference<'a, T, C> where C: Compare<T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Less, Less, self.cmp) {
                Less    => return self.a.next(),
                Equal   => { self.a.next(); self.b.next(); }
                Greater => { self.b.next(); }
            }
        }
    }
}

impl<'a, T, C> Iterator for SymmetricDifference<'a, T, C> where C: Compare<T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Greater, Less, self.cmp) {
                Less    => return self.a.next(),
                Equal   => { self.a.next(); self.b.next(); }
                Greater => return self.b.next(),
            }
        }
    }
}

impl<'a, T, C> Iterator for Intersection<'a, T, C> where C: Compare<T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        loop {
            let o_cmp = match (self.a.peek(), self.b.peek()) {
                (None    , _       ) => None,
                (_       , None    ) => None,
                (Some(a1), Some(b1)) => Some(self.cmp.compare(*a1, *b1)),
            };
            match o_cmp {
                None          => return None,
                Some(Less)    => { self.a.next(); }
                Some(Equal)   => { self.b.next(); return self.a.next() }
                Some(Greater) => { self.b.next(); }
            }
        }
    }
}

impl<'a, T, C> Iterator for Union<'a, T, C> where C: Compare<T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<&'a T> {
        loop {
            match cmp_opt(self.a.peek(), self.b.peek(), Greater, Less, self.cmp) {
                Less    => return self.a.next(),
                Equal   => { self.b.next(); return self.a.next() }
                Greater => return self.b.next(),
            }
        }
    }
}

#[unstable = "matches collection reform specification, waiting for dust to settle"]
impl<'a, 'b, T, C> ops::BitOr<&'b TreeSet<T, C>> for &'a TreeSet<T, C>
    where T: Clone, C: Compare<T> + Eq + Clone {

    type Output = TreeSet<T, C>;

    /// Returns the union of `self` and `rhs` as a new `TreeSet<T, C>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = vec![1, 2, 3].into_iter().collect();
    /// let b: TreeSet<isize> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set: TreeSet<isize> = &a | &b;
    /// let v: Vec<isize> = set.into_iter().collect();
    /// assert_eq!(v, vec![1, 2, 3, 4, 5]);
    /// ```
    fn bitor(self, rhs: &TreeSet<T, C>) -> TreeSet<T, C> {
        let it = self.union(rhs).cloned();
        let mut set = TreeSet::with_comparator(self.comparator().clone());
        set.extend(it);
        set
    }
}

#[unstable = "matches collection reform specification, waiting for dust to settle"]
impl<'a, 'b, T, C> ops::BitAnd<&'b TreeSet<T, C>> for &'a TreeSet<T, C>
    where T: Clone, C: Compare<T> + Eq + Clone {

    type Output = TreeSet<T, C>;

    /// Returns the intersection of `self` and `rhs` as a new `TreeSet<T, C>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = vec![1, 2, 3].into_iter().collect();
    /// let b: TreeSet<isize> = vec![2, 3, 4].into_iter().collect();
    ///
    /// let set: TreeSet<isize> = &a & &b;
    /// let v: Vec<isize> = set.into_iter().collect();
    /// assert_eq!(v, vec![2, 3]);
    /// ```
    fn bitand(self, rhs: &TreeSet<T, C>) -> TreeSet<T, C> {
        let it = self.intersection(rhs).cloned();
        let mut set = TreeSet::with_comparator(self.comparator().clone());
        set.extend(it);
        set
    }
}

#[unstable = "matches collection reform specification, waiting for dust to settle"]
impl<'a, 'b, T, C> ops::BitXor<&'b TreeSet<T, C>> for &'a TreeSet<T, C>
    where T: Clone, C: Compare<T> + Eq + Clone {

    type Output = TreeSet<T, C>;

    /// Returns the symmetric difference of `self` and `rhs` as a new `TreeSet<T, C>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = vec![1, 2, 3].into_iter().collect();
    /// let b: TreeSet<isize> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set: TreeSet<isize> = &a ^ &b;
    /// let v: Vec<isize> = set.into_iter().collect();
    /// assert_eq!(v, vec![1, 2, 4, 5]);
    /// ```
    fn bitxor(self, rhs: &TreeSet<T, C>) -> TreeSet<T, C> {
        let it = self.symmetric_difference(rhs).cloned();
        let mut set = TreeSet::with_comparator(self.comparator().clone());
        set.extend(it);
        set
    }
}

#[unstable = "matches collection reform specification, waiting for dust to settle"]
impl<'a, 'b, T, C> ops::Sub<&'b TreeSet<T, C>> for &'a TreeSet<T, C>
    where T: Clone, C: Compare<T> + Eq + Clone {

    type Output = TreeSet<T, C>;

    /// Returns the difference of `self` and `rhs` as a new `TreeSet<T, C>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeSet;
    ///
    /// let a: TreeSet<isize> = vec![1, 2, 3].into_iter().collect();
    /// let b: TreeSet<isize> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let set: TreeSet<isize> = &a - &b;
    /// let v: Vec<isize> = set.into_iter().collect();
    /// assert_eq!(v, vec![1, 2]);
    /// ```
    fn sub(self, rhs: &TreeSet<T, C>) -> TreeSet<T, C> {
        let it = self.difference(rhs).cloned();
        let mut set = TreeSet::with_comparator(self.comparator().clone());
        set.extend(it);
        set
    }
}

impl<T, C> iter::FromIterator<T> for TreeSet<T, C> where C: Compare<T> + Default {
    fn from_iter<Iter: Iterator<Item=T>>(iter: Iter) -> TreeSet<T, C> {
        let mut set: TreeSet<T, C> = Default::default();
        set.extend(iter);
        set
    }
}

impl<T, C> Extend<T> for TreeSet<T, C> where C: Compare<T> {
    #[inline]
    fn extend<Iter: Iterator<Item=T>>(&mut self, mut iter: Iter) {
        for elem in iter {
            self.insert(elem);
        }
    }
}

impl<S: Hasher+Writer, T: Hash<S>, C> Hash<S> for TreeSet<T, C> where C: Compare<T> {
    fn hash(&self, state: &mut S) {
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}

#[cfg(test)]
mod test {
    use std::hash;

    use super::TreeSet;

    #[test]
    fn test_clear() {
        let mut s = TreeSet::new();
        s.clear();
        assert!(s.insert(5is));
        assert!(s.insert(12));
        assert!(s.insert(19));
        s.clear();
        assert!(!s.contains(&5));
        assert!(!s.contains(&12));
        assert!(!s.contains(&19));
        assert!(s.is_empty());
    }

    #[test]
    fn test_disjoint() {
        let mut xs = TreeSet::new();
        let mut ys = TreeSet::new();
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(5is));
        assert!(ys.insert(11is));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(xs.insert(7));
        assert!(xs.insert(19));
        assert!(xs.insert(4));
        assert!(ys.insert(2));
        assert!(ys.insert(-11));
        assert!(xs.is_disjoint(&ys));
        assert!(ys.is_disjoint(&xs));
        assert!(ys.insert(7));
        assert!(!xs.is_disjoint(&ys));
        assert!(!ys.is_disjoint(&xs));
    }

    #[test]
    fn test_subset_and_superset() {
        let mut a = TreeSet::new();
        assert!(a.insert(0is));
        assert!(a.insert(5));
        assert!(a.insert(11));
        assert!(a.insert(7));

        let mut b = TreeSet::new();
        assert!(b.insert(0is));
        assert!(b.insert(7));
        assert!(b.insert(19));
        assert!(b.insert(250));
        assert!(b.insert(11));
        assert!(b.insert(200));

        assert!(!a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(!b.is_superset(&a));

        assert!(b.insert(5));

        assert!(a.is_subset(&b));
        assert!(!a.is_superset(&b));
        assert!(!b.is_subset(&a));
        assert!(b.is_superset(&a));
    }

    #[test]
    fn test_iterator() {
        let mut m = TreeSet::new();

        assert!(m.insert(3is));
        assert!(m.insert(0));
        assert!(m.insert(4));
        assert!(m.insert(2));
        assert!(m.insert(1));

        let mut n = 0;
        for x in m.iter() {
            assert_eq!(*x, n);
            n += 1
        }
    }

    #[test]
    fn test_rev_iter() {
        let mut m = TreeSet::new();

        assert!(m.insert(3is));
        assert!(m.insert(0));
        assert!(m.insert(4));
        assert!(m.insert(2));
        assert!(m.insert(1));

        let mut n = 4;
        for x in m.rev_iter() {
            assert_eq!(*x, n);
            n -= 1;
        }
    }

    #[test]
    fn test_move_iter() {
        let s: TreeSet<isize> = range(0is, 5).collect();

        let mut n = 0;
        for x in s.into_iter() {
            assert_eq!(x, n);
            n += 1;
        }
    }

    #[test]
    fn test_move_iter_size_hint() {
        let s: TreeSet<isize> = vec!(0is, 1).into_iter().collect();

        let mut it = s.into_iter();

        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next() != None);

        assert_eq!(it.size_hint(), (1, Some(1)));
        assert!(it.next() != None);

        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_clone_eq() {
      let mut m = TreeSet::new();

      m.insert(1is);
      m.insert(2);

      assert!(m.clone() == m);
    }

    #[test]
    fn test_hash() {
      let mut x = TreeSet::new();
      let mut y = TreeSet::new();

      x.insert(1is);
      x.insert(2);
      x.insert(3);

      y.insert(3is);
      y.insert(2);
      y.insert(1);

      assert!(hash::hash::<_, hash::SipHasher>(&x) == hash::hash::<_, hash::SipHasher>(&y));
    }

    struct Counter<'a, 'b> {
        i: &'a mut usize,
        expected: &'b [isize],
    }

    impl<'a, 'b, 'c> FnMut(&'c isize) -> bool for Counter<'a, 'b> {
        extern "rust-call" fn call_mut(&mut self, (&x,): (&'c isize,)) -> bool {
            assert_eq!(x, self.expected[*self.i]);
            *self.i += 1;
            true
        }
    }

    fn check<F>(a: &[isize], b: &[isize], expected: &[isize], f: F) where
        // FIXME Replace `Counter` with `Box<FnMut(&isize) -> bool>`
        F: FnOnce(&TreeSet<isize>, &TreeSet<isize>, Counter) -> bool,
    {
        let mut set_a = TreeSet::new();
        let mut set_b = TreeSet::new();

        for x in a.iter() { assert!(set_a.insert(*x)) }
        for y in b.iter() { assert!(set_b.insert(*y)) }

        let mut i = 0;
        f(&set_a, &set_b, Counter { i: &mut i, expected: expected });
        assert_eq!(i, expected.len());
    }

    #[test]
    fn test_intersection() {
        fn check_intersection(a: &[isize], b: &[isize], expected: &[isize]) {
            check(a, b, expected, |x, y, f| x.intersection(y).all(f))
        }

        check_intersection(&[], &[], &[]);
        check_intersection(&[1, 2, 3], &[], &[]);
        check_intersection(&[], &[1, 2, 3], &[]);
        check_intersection(&[2], &[1, 2, 3], &[2]);
        check_intersection(&[1, 2, 3], &[2], &[2]);
        check_intersection(&[11, 1, 3, 77, 103, 5, -5],
                           &[2, 11, 77, -9, -42, 5, 3],
                           &[3, 5, 11, 77]);
    }

    #[test]
    fn test_difference() {
        fn check_difference(a: &[isize], b: &[isize], expected: &[isize]) {
            check(a, b, expected, |x, y, f| x.difference(y).all(f))
        }

        check_difference(&[], &[], &[]);
        check_difference(&[1, 12], &[], &[1, 12]);
        check_difference(&[], &[1, 2, 3, 9], &[]);
        check_difference(&[1, 3, 5, 9, 11],
                         &[3, 9],
                         &[1, 5, 11]);
        check_difference(&[-5, 11, 22, 33, 40, 42],
                         &[-12, -5, 14, 23, 34, 38, 39, 50],
                         &[11, 22, 33, 40, 42]);
    }

    #[test]
    fn test_symmetric_difference() {
        fn check_symmetric_difference(a: &[isize], b: &[isize],
                                      expected: &[isize]) {
            check(a, b, expected, |x, y, f| x.symmetric_difference(y).all(f))
        }

        check_symmetric_difference(&[], &[], &[]);
        check_symmetric_difference(&[1, 2, 3], &[2], &[1, 3]);
        check_symmetric_difference(&[2], &[1, 2, 3], &[1, 3]);
        check_symmetric_difference(&[1, 3, 5, 9, 11],
                                   &[-2, 3, 9, 14, 22],
                                   &[-2, 1, 5, 11, 14, 22]);
    }

    #[test]
    fn test_union() {
        fn check_union(a: &[isize], b: &[isize],
                                      expected: &[isize]) {
            check(a, b, expected, |x, y, f| x.union(y).all(f))
        }

        check_union(&[], &[], &[]);
        check_union(&[1, 2, 3], &[2], &[1, 2, 3]);
        check_union(&[2], &[1, 2, 3], &[1, 2, 3]);
        check_union(&[1, 3, 5, 9, 11, 16, 19, 24],
                    &[-2, 1, 5, 9, 13, 19],
                    &[-2, 1, 3, 5, 9, 11, 13, 16, 19, 24]);
    }

    #[test]
    fn test_bit_or() {
        let a: TreeSet<isize> = vec![1, 3, 5, 9, 11, 16, 19, 24].into_iter().collect();
        let b: TreeSet<isize> = vec![-2, 1, 5, 9, 13, 19].into_iter().collect();

        let set: TreeSet<isize> = &a | &b;
        let v: Vec<isize> = set.into_iter().collect();
        assert_eq!(v, vec![-2, 1, 3, 5, 9, 11, 13, 16, 19, 24]);
    }

    #[test]
    fn test_bit_and() {
        let a: TreeSet<isize> = vec![11, 1, 3, 77, 103, 5, -5].into_iter().collect();
        let b: TreeSet<isize> = vec![2, 11, 77, -9, -42, 5, 3].into_iter().collect();

        let set: TreeSet<isize> = &a & &b;
        let v: Vec<isize> = set.into_iter().collect();
        assert_eq!(v, vec![3, 5, 11, 77]);
    }

    #[test]
    fn test_bit_xor() {
        let a: TreeSet<isize> = vec![1, 3, 5, 9, 11].into_iter().collect();
        let b: TreeSet<isize> = vec![-2, 3, 9, 14, 22].into_iter().collect();

        let set: TreeSet<isize> = &a ^ &b;
        let v: Vec<isize> = set.into_iter().collect();
        assert_eq!(v, vec![-2, 1, 5, 11, 14, 22]);
    }

    #[test]
    fn test_sub() {
        let a: TreeSet<isize> = vec![-5, 11, 22, 33, 40, 42].into_iter().collect();
        let b: TreeSet<isize> = vec![-12, -5, 14, 23, 34, 38, 39, 50].into_iter().collect();

        let set: TreeSet<isize> = &a - &b;
        let v: Vec<isize> = set.into_iter().collect();
        assert_eq!(v, vec![11, 22, 33, 40, 42]);
    }

    #[test]
    fn test_zip() {
        let mut x = TreeSet::new();
        x.insert(5us);
        x.insert(12us);
        x.insert(11us);

        let mut y = TreeSet::new();
        y.insert("foo");
        y.insert("bar");

        let x = x;
        let y = y;
        let mut z = x.iter().zip(y.iter());

        // FIXME: #5801: this needs a type hint to compile...
        let result: Option<(&usize, & &'static str)> = z.next();
        assert_eq!(result.unwrap(), (&5us, &("bar")));

        let result: Option<(&usize, & &'static str)> = z.next();
        assert_eq!(result.unwrap(), (&11us, &("foo")));

        let result: Option<(&usize, & &'static str)> = z.next();
        assert!(result.is_none());
    }

    #[test]
    fn test_from_iter() {
        let xs = [1is, 2, 3, 4, 5, 6, 7, 8, 9];

        let set: TreeSet<isize> = xs.iter().map(|&x| x).collect();

        for x in xs.iter() {
            assert!(set.contains(x));
        }
    }

    #[test]
    fn test_show() {
        let mut set = TreeSet::new();
        let empty: TreeSet<i32> = TreeSet::new();

        set.insert(1);
        set.insert(2);

        assert_eq!(format!("{:?}", set), "{1i32, 2i32}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

    #[test]
    fn test_comparator_iterator() {
        use compare::{CompareExt, Natural};

        let mut m = TreeSet::with_comparator(Natural.rev());

        assert!(m.insert(3is));
        assert!(m.insert(0));
        assert!(m.insert(4));
        assert!(m.insert(2));
        assert!(m.insert(1));

        let mut n = 5;
        for &t in m.iter() {
            n -= 1;
            assert_eq!(t, n);
        }
        assert_eq!(n, 0);
    }

    #[test]
    fn test_comparator_borrowed() {
        use compare::{CompareExt, Natural};

        let mut m = TreeSet::with_comparator(Natural::<str>.borrow());

        assert!(m.insert("a".to_string()));

        assert!(m.contains("a"));
        assert!(m.contains(&"a"));
        assert!(m.contains(&"a".to_string()));

        assert!(m.remove("a"));
        assert!(!m.remove(&"a"));
        assert!(!m.remove(&"a".to_string()));
    }
}
