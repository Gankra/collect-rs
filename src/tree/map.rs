// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::default::Default;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::iter::{self, IntoIterator};
use std::mem::transmute;
use std::ops;
use std::hash::{Hash, Hasher};

use compare::{Compare, Natural, natural};
use super::node::{self, Forward, Node, Reverse};

// FIXME(conventions): implement bounded iterators
// FIXME(conventions): replace rev_iter(_mut) by making iter(_mut) DoubleEnded

/// This is implemented as an AA tree, which is a simplified variation of
/// a red-black tree where red (horizontal) nodes can only be added
/// as a right child. The time complexity is the same, and re-balancing
/// operations are more frequent but also cheaper.
///
/// # Examples
///
/// ```rust
/// use collect::TreeMap;
///
/// let mut map = TreeMap::new();
///
/// map.insert(2, "bar");
/// map.insert(1, "foo");
/// map.insert(3, "quux");
///
/// // In ascending order by keys
/// for (key, value) in map.iter() {
///     println!("{}: {}", key, value);
/// }
///
/// // Prints 1, 2, 3
/// for key in map.keys() {
///     println!("{}", key);
/// }
///
/// // Prints `foo`, `bar`, `quux`
/// for value in map.values() {
///     println!("{}", value);
/// }
///
/// map.remove(&1);
/// assert_eq!(map.len(), 2);
///
/// if !map.contains_key(&1) {
///     println!("1 is no more");
/// }
///
/// for key in range(0, 4) {
///     match map.get(&key) {
///         Some(value) => println!("{} has a value: {}", key, value),
///         None => println!("{} not in map", key),
///     }
/// }
///
/// map.clear();
/// assert!(map.is_empty());
/// ```
///
/// A `TreeMap` can also be used with a custom ordering:
///
/// ```rust
/// use collect::TreeMap;
///
/// struct Troll<'a> {
///     name: &'a str,
///     level: u32,
/// }
///
/// // Use a map to store trolls, sorted by level, and track a list of
/// // heroes slain.
/// let mut trolls = TreeMap::with_comparator(|&: l: &Troll, r: &Troll| l.level.cmp(&r.level));
///
/// trolls.insert(Troll { name: "Orgarr", level: 2 },
///               vec!["King Karl"]);
/// trolls.insert(Troll { name: "Blargarr", level: 3 },
///               vec!["Odd"]);
/// trolls.insert(Troll { name: "Kron the Smelly One", level: 4 },
///               vec!["Omar the Brave", "Peter: Slayer of Trolls"]);
/// trolls.insert(Troll { name: "Wartilda", level: 1 },
///               vec![]);
///
/// println!("You are facing {} trolls!", trolls.len());
///
/// // Print the trolls, ordered by level with smallest level first
/// for (troll, heroes) in trolls.iter() {
///     let what = if heroes.len() == 1 { "hero" }
///                else { "heroes" };
///
///     println!("level {}: '{}' has slain {} {}",
///              troll.level, troll.name, heroes.len(), what);
/// }
///
/// // Kill all trolls
/// trolls.clear();
/// assert_eq!(trolls.len(), 0);
/// ```

// Future improvements:

// range search - O(log n) retrieval of an iterator from some key

// (possibly) implement the overloads Python does for sets:
//   * intersection: &
//   * difference: -
//   * symmetric difference: ^
//   * union: |
// These would be convenient since the methods work like `each`

#[derive(Clone)]
pub struct TreeMap<K, V, C: Compare<K> = Natural<K>> {
    root: Option<Box<node::Node<K, V>>>,
    len: usize,
    cmp: C,
}

// FIXME: determine what `PartialEq` means for comparator-based `TreeMap`s
impl<K: PartialEq + Ord, V: PartialEq> PartialEq for TreeMap<K, V> {
    fn eq(&self, other: &TreeMap<K, V>) -> bool {
        self.len() == other.len() &&
            self.iter().zip(other.iter()).all(|(a, b)| a == b)
    }
}

// FIXME: determine what `Eq` means for comparator-based `TreeMap`s
impl<K: Eq + Ord, V: Eq> Eq for TreeMap<K, V> {}

// FIXME: determine what `PartialOrd` means for comparator-based `TreeMap`s
impl<K: Ord, V: PartialOrd> PartialOrd for TreeMap<K, V> {
    #[inline]
    fn partial_cmp(&self, other: &TreeMap<K, V>) -> Option<Ordering> {
        iter::order::partial_cmp(self.iter(), other.iter())
    }
}

// FIXME: determine what `Ord` means for comparator-based `TreeMap`s
impl<K: Ord, V: Ord> Ord for TreeMap<K, V> {
    #[inline]
    fn cmp(&self, other: &TreeMap<K, V>) -> Ordering {
        iter::order::cmp(self.iter(), other.iter())
    }
}

impl<K: Debug, V: Debug, C> Debug for TreeMap<K, V, C> where C: Compare<K> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}: {:?}", *k, *v));
        }

        write!(f, "}}")
    }
}

impl<K, V, C> Default for TreeMap<K, V, C> where C: Compare<K> + Default {
    #[inline]
    fn default() -> TreeMap<K, V, C> { TreeMap::with_comparator(Default::default()) }
}

impl<K, V, C, Q: ?Sized> ops::Index<Q> for TreeMap<K, V, C> where C: Compare<K> + Compare<Q, K> {
    type Output = V;
    #[inline]
    fn index(&self, i: &Q) -> &V {
        self.get(i).expect("no entry found for key")
    }
}

impl<K, V, C, Q: ?Sized> ops::IndexMut<Q> for TreeMap<K, V, C> where C: Compare<K> + Compare<Q, K> {
    #[inline]
    fn index_mut(&mut self, i: &Q) -> &mut V {
        self.get_mut(i).expect("no entry found for key")
    }
}

impl<K: Ord, V> TreeMap<K, V> {
    /// Creates an empty `TreeMap` ordered according to the natural order of its keys.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map: TreeMap<&str, i32> = TreeMap::new();
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn new() -> TreeMap<K, V> { TreeMap::with_comparator(natural()) }
}

impl<K, V, C> TreeMap<K, V, C> where C: Compare<K> {
    /// Creates an empty `TreeMap` ordered according to the given comparator.
    pub fn with_comparator(cmp: C) -> TreeMap<K, V, C> {
        TreeMap { root: None, len: 0, cmp: cmp }
    }

    /// Returns the comparator according to which the `TreeMap` is ordered.
    pub fn comparator(&self) -> &C { &self.cmp }

    /// Gets a lazy iterator over the keys in the map, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Print "a", "b", "c" in order.
    /// for x in map.keys() {
    ///     println!("{}", x);
    /// }
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((&'a K, &'a V)) -> &'a K = first; // coerce to fn pointer

        Keys(self.iter().map(first))
    }

    /// Gets a lazy iterator over the values in the map, in ascending order
    /// with respect to the corresponding keys.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Print 1, 2, 3 ordered by keys.
    /// for x in map.values() {
    ///     println!("{}", x);
    /// }
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a K, &'a V)) -> &'a V = second; // coerce to fn pointer

        Values(self.iter().map(second))
    }

    /// Gets a lazy iterator over the key-value pairs in the map, in ascending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Print contents in ascending order
    /// for (key, value) in map.iter() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn iter(&self) -> Iter<K, V> {
        Iter { iter: node::Iter::new(node::as_ref(&self.root), self.len) }
    }

    /// Gets a lazy reverse iterator over the key-value pairs in the map, in descending order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Print contents in descending order
    /// for (key, value) in map.rev_iter() {
    ///     println!("{}: {}", key, value);
    /// }
    /// ```
    pub fn rev_iter(&self) -> RevIter<K, V> {
        RevIter { iter: node::Iter::new(node::as_ref(&self.root), self.len) }
    }

    /// Gets a lazy forward iterator over the key-value pairs in the
    /// map, with the values being mutable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Add 10 until we find "b"
    /// for (key, value) in map.iter_mut() {
    ///     *value += 10;
    ///     if key == &"b" { break }
    /// }
    ///
    /// assert_eq!(map.get(&"a"), Some(&11));
    /// assert_eq!(map.get(&"b"), Some(&12));
    /// assert_eq!(map.get(&"c"), Some(&3));
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut { iter: node::Iter::new(node::as_ref(&self.root), self.len) }
    }

    /// Gets a lazy reverse iterator over the key-value pairs in the
    /// map, with the values being mutable.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Add 10 until we find "b"
    /// for (key, value) in map.rev_iter_mut() {
    ///     *value += 10;
    ///     if key == &"b" { break }
    /// }
    ///
    /// assert_eq!(map.get(&"a"), Some(&1));
    /// assert_eq!(map.get(&"b"), Some(&12));
    /// assert_eq!(map.get(&"c"), Some(&13));
    /// ```
    pub fn rev_iter_mut(&mut self) -> RevIterMut<K, V> {
        RevIterMut { iter: node::Iter::new(node::as_ref(&self.root), self.len) }
    }

    /// Gets a lazy iterator that consumes the treemap.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    /// let mut map = TreeMap::new();
    /// map.insert("a", 1);
    /// map.insert("c", 3);
    /// map.insert("b", 2);
    ///
    /// // Not possible with a regular `.iter()`
    /// let vec: Vec<(&str, i32)> = map.into_iter().collect();
    /// assert_eq!(vec, vec![("a", 1), ("b", 2), ("c", 3)]);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn into_iter(mut self) -> IntoIter<K, V> {
        IntoIter { iter: node::Iter::new(self.root.take(), self.len) }
    }

    /// Return the number of elements in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut a = TreeMap::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert(1, "a");
    /// assert_eq!(a.len(), 1);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn len(&self) -> usize { self.len }

    /// Return true if the map contains no elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut a = TreeMap::new();
    /// assert!(a.is_empty());
    /// a.insert(1, "a");
    /// assert!(!a.is_empty());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    #[inline]
    pub fn is_empty(&self) -> bool { self.root.is_none() }

    /// Clears the map, removing all values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut a = TreeMap::new();
    /// a.insert(1, "a");
    /// a.clear();
    /// assert!(a.is_empty());
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn clear(&mut self) {
        self.root = None;
        self.len = 0;
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), None);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V> where C: Compare<Q, K> {
        self.find_with(|node_key| Compare::compare(&self.cmp, key, node_key))
    }

    /// Returns true if the map contains a value for the specified key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.contains_key(&1), true);
    /// assert_eq!(map.contains_key(&2), false);
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn contains_key<Q: ?Sized>(&self, key: &Q) -> bool where C: Compare<Q, K> {
        self.get(key).is_some()
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(1, "a");
    /// match map.get_mut(&1) {
    ///     Some(x) => *x = "b",
    ///     None => (),
    /// }
    /// assert_eq!(map[1], "b");
    /// ```
    #[inline]
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
        where C: Compare<Q, K> {

        let cmp = &self.cmp;
        node::traverse_mut(&mut self.root, |node| Compare::compare(cmp, key, node.key()))
            .as_mut().map(|node| node.value_mut())
    }

    /// Inserts a key-value pair from the map. If the key already had a value
    /// present in the map, that value is returned. Otherwise, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// assert_eq!(map.insert(37, "a"), None);
    /// assert_eq!(map.is_empty(), false);
    ///
    /// map.insert(37, "b");
    /// assert_eq!(map.insert(37, "c"), Some("b"));
    /// assert_eq!(map[37], "c");
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        let old_value = node::insert(&mut self.root, key, value, &self.cmp);
        if old_value.is_none() { self.len += 1; }
        old_value
    }

    /// Removes a key from the map, returning the value at the key if the key
    /// was previously in the map.
    ///
    /// The key may be any borrowed form of the map's key type, but the ordering
    /// on the borrowed form *must* match the ordering on the key type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(1, "a");
    /// assert_eq!(map.remove(&1), Some("a"));
    /// assert_eq!(map.remove(&1), None);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn remove<Q: ?Sized>(&mut self, key: &Q) -> Option<V> where C: Compare<Q, K> {
        let value = node::remove(&mut self.root, key, &self.cmp);
        if value.is_some() { self.len -= 1; }
        value
    }

    /// Returns the value for which `f(key)` returns `Equal`. `f` is invoked
    /// with current key and guides tree navigation. That means `f` should
    /// be aware of natural ordering of the tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::tree_map::TreeMap;
    ///
    /// fn get_headers() -> TreeMap<&'static str, &'static str> {
    ///     let mut result = TreeMap::new();
    ///     result.insert("Content-Type", "application/xml");
    ///     result.insert("User-Agent", "Curl-Rust/0.1");
    ///     result
    /// }
    ///
    /// let headers = get_headers();
    /// let ua_key = "User-Agent";
    /// let ua = headers.find_with(|&k| {
    ///    ua_key.cmp(k)
    /// });
    ///
    /// assert_eq!(*ua.unwrap(), "Curl-Rust/0.1");
    /// ```
    #[inline]
    pub fn find_with<F>(&self, mut f: F) -> Option<&V> where F: FnMut(&K) -> Ordering {
        node::traverse(&self.root, |node| f(node.key()))
            .as_ref().map(|node| node.value())
    }

    /// Returns the value for which `f(key)` returns `Equal`. `f` is invoked
    /// with current key and guides tree navigation. That means `f` should
    /// be aware of natural ordering of the tree.
    ///
    /// # Examples
    ///
    /// ```rust
    /// let mut t = collect::tree_map::TreeMap::new();
    /// t.insert("Content-Type", "application/xml");
    /// t.insert("User-Agent", "Curl-Rust/0.1");
    ///
    /// let new_ua = "Safari/156.0";
    /// match t.find_with_mut(|&k| "User-Agent".cmp(k)) {
    ///    Some(x) => *x = new_ua,
    ///    None => panic!(),
    /// }
    ///
    /// assert_eq!(t.get(&"User-Agent"), Some(&new_ua));
    /// ```
    #[inline]
    pub fn find_with_mut<F>(&mut self, mut f: F) -> Option<&mut V>
        where F: FnMut(&K) -> Ordering {

        node::traverse_mut(&mut self.root, |node| f(node.key()))
            .as_mut().map(|node| node.value_mut())
    }
}

impl<K, V, C> TreeMap<K, V, C> where C: Compare<K> {
    /// Returns a lazy iterator to the first key-value pair whose key is not less than `k`
    /// If all keys in map are less than `k` an empty iterator is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(2, "a");
    /// map.insert(4, "b");
    /// map.insert(6, "c");
    /// map.insert(8, "d");
    ///
    /// assert_eq!(map.lower_bound(&4).next(), Some((&4, &"b")));
    /// assert_eq!(map.lower_bound(&5).next(), Some((&6, &"c")));
    /// assert_eq!(map.lower_bound(&10).next(), None);
    /// ```
    pub fn lower_bound<Q: ?Sized>(&self, key: &Q) -> BoundIter<K, V>
        where C: Compare<Q, K> {

        BoundIter {
            iter: node::Iter::bounded(&self.root, &self.cmp, key, true, self.len)
        }
    }

    /// Returns a lazy value iterator to the first key-value pair (with
    /// the value being mutable) whose key is not less than `k`.
    ///
    /// If all keys in map are less than `k` an empty iterator is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(2, "a");
    /// map.insert(4, "b");
    /// map.insert(6, "c");
    /// map.insert(8, "d");
    ///
    /// assert_eq!(map.lower_bound_mut(&4).next(), Some((&4, &mut "b")));
    /// assert_eq!(map.lower_bound_mut(&5).next(), Some((&6, &mut "c")));
    /// assert_eq!(map.lower_bound_mut(&10).next(), None);
    ///
    /// for (key, value) in map.lower_bound_mut(&4) {
    ///     *value = "changed";
    /// }
    ///
    /// assert_eq!(map.get(&2), Some(&"a"));
    /// assert_eq!(map.get(&4), Some(&"changed"));
    /// assert_eq!(map.get(&6), Some(&"changed"));
    /// assert_eq!(map.get(&8), Some(&"changed"));
    /// ```
    pub fn lower_bound_mut<Q: ?Sized>(&mut self, key: &Q) -> BoundIterMut<K, V>
        where C: Compare<Q, K> {

        BoundIterMut {
            iter: node::Iter::bounded(&self.root, &self.cmp, key, true, self.len)
        }
    }

    /// Returns a lazy iterator to the first key-value pair whose key is greater than `k`
    /// If all keys in map are less than or equal to `k` an empty iterator is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(2, "a");
    /// map.insert(4, "b");
    /// map.insert(6, "c");
    /// map.insert(8, "d");
    ///
    /// assert_eq!(map.upper_bound(&4).next(), Some((&6, &"c")));
    /// assert_eq!(map.upper_bound(&5).next(), Some((&6, &"c")));
    /// assert_eq!(map.upper_bound(&10).next(), None);
    /// ```
    pub fn upper_bound<Q: ?Sized>(&self, key: &Q) -> BoundIter<K, V>
        where C: Compare<Q, K> {

        BoundIter{
            iter: node::Iter::bounded(&self.root, &self.cmp, key, false, self.len)
        }
    }

    /// Returns a lazy iterator to the first key-value pair (with the
    /// value being mutable) whose key is greater than `k`.
    ///
    /// If all keys in map are less than or equal to `k` an empty iterator
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::TreeMap;
    ///
    /// let mut map = TreeMap::new();
    /// map.insert(2, "a");
    /// map.insert(4, "b");
    /// map.insert(6, "c");
    /// map.insert(8, "d");
    ///
    /// assert_eq!(map.upper_bound_mut(&4).next(), Some((&6, &mut "c")));
    /// assert_eq!(map.upper_bound_mut(&5).next(), Some((&6, &mut "c")));
    /// assert_eq!(map.upper_bound_mut(&10).next(), None);
    ///
    /// for (key, value) in map.upper_bound_mut(&4) {
    ///     *value = "changed";
    /// }
    ///
    /// assert_eq!(map.get(&2), Some(&"a"));
    /// assert_eq!(map.get(&4), Some(&"b"));
    /// assert_eq!(map.get(&6), Some(&"changed"));
    /// assert_eq!(map.get(&8), Some(&"changed"));
    /// ```
    pub fn upper_bound_mut<Q: ?Sized>(&mut self, key: &Q) -> BoundIterMut<K, V>
        where C: Compare<Q, K> {

        BoundIterMut {
            iter: node::Iter::bounded(&self.root, &self.cmp, key, false, self.len)
        }
    }
}

/// Lazy forward iterator over a map
pub struct Iter<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, usize, Forward>,
}

impl<'a, K, V> Clone for Iter<'a, K, V> {
    fn clone(&self) -> Iter<'a, K, V> { Iter { iter: self.iter.clone() } }
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

/// Lazy forward iterator over a map that allows for the mutation of
/// the values.
pub struct IterMut<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, usize, Forward>,
}

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        let next = self.iter.next();
        unsafe { transmute(next) }
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

/// Lazy backward iterator over a map
pub struct RevIter<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, usize, Reverse>,
}

impl<'a, K, V> Clone for RevIter<'a, K, V> {
    fn clone(&self) -> RevIter<'a, K, V> { RevIter { iter: self.iter.clone() } }
}

impl<'a, K, V> Iterator for RevIter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<'a, K, V> ExactSizeIterator for RevIter<'a, K, V> {}

/// Lazy backward iterator over a map
pub struct RevIterMut<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, usize, Reverse>,
}

impl<'a, K, V> Iterator for RevIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        let next = self.iter.next();
        unsafe { transmute(next) }
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

pub struct IntoIter<K, V> {
    iter: node::Iter<Box<Node<K, V>>, usize, Forward>,
}

impl<K, V> Iterator for IntoIter<K, V> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

impl<K, V> ExactSizeIterator for IntoIter<K, V> {}

pub struct BoundIter<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, (usize, usize), Forward>,
}

impl<'a, K, V> Clone for BoundIter<'a, K, V> {
    fn clone(&self) -> BoundIter<'a, K, V> { BoundIter { iter: self.iter.clone() } }
}

impl<'a, K, V> Iterator for BoundIter<'a, K, V> {
    type Item = (&'a K, &'a V);
    fn next(&mut self) -> Option<(&'a K, &'a V)> { self.iter.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

pub struct BoundIterMut<'a, K: 'a, V: 'a> {
    iter: node::Iter<&'a Node<K, V>, (usize, usize), Forward>,
}

impl<'a, K, V> Iterator for BoundIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);
    fn next(&mut self) -> Option<(&'a K, &'a mut V)> {
        let next = self.iter.next();
        unsafe { transmute(next) }
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.iter.size_hint() }
}

/// TreeMap keys iterator.
pub struct Keys<'a, K: 'a, V: 'a>
    (iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>);

/// TreeMap values iterator.
pub struct Values<'a, K: 'a, V: 'a>
    (iter::Map<Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>);

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;
    #[inline] fn next(&mut self) -> Option<&'a K> { self.0.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;
    #[inline] fn next(&mut self) -> Option<&'a V> { self.0.next() }
    #[inline] fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<K, V, C> iter::FromIterator<(K, V)> for TreeMap<K, V, C> where C: Compare<K> + Default {
    fn from_iter<T: IntoIterator<Item=(K, V)>>(iter: T) -> TreeMap<K, V, C> {
        let mut map: TreeMap<K, V, C> = Default::default();
        map.extend(iter);
        map
    }
}

impl<K, V, C> Extend<(K, V)> for TreeMap<K, V, C> where C: Compare<K> {
    #[inline]
    fn extend<T: IntoIterator<Item=(K, V)>>(&mut self, iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

impl<K: Hash, V: Hash, C> Hash for TreeMap<K, V, C> where C: Compare<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}

impl<'a, K, V, C> IntoIterator for &'a TreeMap<K, V, C> where C: Compare<K> {
    type Item = (&'a K, &'a V);
    type IntoIter = Iter<'a, K, V>;
    fn into_iter(self) -> Iter<'a, K, V> { self.iter() }
}

impl<'a, K, V, C> IntoIterator for &'a mut TreeMap<K, V, C> where C: Compare<K> {
    type Item = (&'a K, &'a mut V);
    type IntoIter = IterMut<'a, K, V>;
    fn into_iter(self) -> IterMut<'a, K, V> { self.iter_mut() }
}

impl<K, V, C> IntoIterator for TreeMap<K, V, C> where C: Compare<K> {
    type Item = (K, V);
    type IntoIter = IntoIter<K, V>;
    fn into_iter(self) -> IntoIter<K, V> { self.into_iter() }
}

#[cfg(test)]
mod test {
    use rand::{self, Rng};

    use super::TreeMap;

    #[test]
    fn find_empty() {
        let m: TreeMap<i32,i32> = TreeMap::new();
        assert!(m.get(&5) == None);
    }

    #[test]
    fn find_not_found() {
        let mut m = TreeMap::new();
        assert!(m.insert(1, 2).is_none());
        assert!(m.insert(5, 3).is_none());
        assert!(m.insert(9, 3).is_none());
        assert_eq!(m.get(&2), None);
    }

    #[test]
    fn find_with_empty() {
        let m: TreeMap<&'static str,i32> = TreeMap::new();
        assert!(m.find_with(|&k| "test".cmp(k)) == None);
    }

    #[test]
    fn find_with_not_found() {
        let mut m = TreeMap::new();
        assert!(m.insert("test1", 2).is_none());
        assert!(m.insert("test2", 3).is_none());
        assert!(m.insert("test3", 3).is_none());
        assert_eq!(m.find_with(|&k| "test4".cmp(k)), None);
    }

    #[test]
    fn find_with_found() {
        let mut m = TreeMap::new();
        assert!(m.insert("test1", 2).is_none());
        assert!(m.insert("test2", 3).is_none());
        assert!(m.insert("test3", 4).is_none());
        assert_eq!(m.find_with(|&k| "test2".cmp(k)), Some(&3));
    }

    #[test]
    fn test_find_mut() {
        let mut m = TreeMap::new();
        assert!(m.insert(1, 12).is_none());
        assert!(m.insert(2, 8).is_none());
        assert!(m.insert(5, 14).is_none());
        let new = 100;
        match m.get_mut(&5) {
          None => panic!(), Some(x) => *x = new
        }
        assert_eq!(m.get(&5), Some(&new));
    }

    #[test]
    fn test_find_with_mut() {
        let mut m = TreeMap::new();
        assert!(m.insert("t1", 12).is_none());
        assert!(m.insert("t2", 8).is_none());
        assert!(m.insert("t5", 14).is_none());
        let new = 100;

        match m.find_with_mut(|&k| "t5".cmp(k)) {
          None => panic!(), Some(x) => *x = new
        }
        assert_eq!(m.find_with(|&k| "t5".cmp(k)), Some(&new));
    }

    #[test]
    fn insert_replace() {
        let mut m = TreeMap::new();
        assert!(m.insert(5, 2).is_none());
        assert!(m.insert(2, 9).is_none());
        assert!(!m.insert(2, 11).is_none());
        assert_eq!(m.get(&2).unwrap(), &11);
    }

    #[test]
    fn test_clear() {
        let mut m = TreeMap::new();
        m.clear();
        assert!(m.insert(5, 11).is_none());
        assert!(m.insert(12, -3).is_none());
        assert!(m.insert(19, 2).is_none());
        m.clear();
        assert!(m.get(&5).is_none());
        assert!(m.get(&12).is_none());
        assert!(m.get(&19).is_none());
        assert!(m.is_empty());
    }

    #[test]
    fn u8_map() {
        let mut m = TreeMap::new();

        let k1 = "foo".as_bytes();
        let k2 = "bar".as_bytes();
        let v1 = "baz".as_bytes();
        let v2 = "foobar".as_bytes();

        m.insert(k1.clone(), v1.clone());
        m.insert(k2.clone(), v2.clone());

        assert_eq!(m.get(&k2), Some(&v2));
        assert_eq!(m.get(&k1), Some(&v1));
    }

    fn check_equal<K: PartialEq + Ord, V: PartialEq>(ctrl: &[(K, V)],
                                            map: &TreeMap<K, V>) {
        assert_eq!(ctrl.is_empty(), map.is_empty());
        for x in ctrl.iter() {
            let &(ref k, ref v) = x;
            assert!(map.get(k).unwrap() == v)
        }
        for (map_k, map_v) in map.iter() {
            let mut found = false;
            for x in ctrl.iter() {
                let &(ref ctrl_k, ref ctrl_v) = x;
                if *map_k == *ctrl_k {
                    assert!(*map_v == *ctrl_v);
                    found = true;
                    break;
                }
            }
            assert!(found);
        }
    }

    fn check_structure<K: Ord, V>(map: &TreeMap<K, V>) {
        if let Some(ref r) = map.root {
            r.check_left();
            r.check_right(false);
        }
    }

    #[test]
    fn test_rand_int() {
        let mut map: TreeMap<i32,i32> = TreeMap::new();
        let mut ctrl = vec![];

        check_equal(ctrl.as_slice(), &map);
        assert!(map.get(&5).is_none());

        let seed: &[_] = &[42];
        let mut rng: rand::IsaacRng = rand::SeedableRng::from_seed(seed);

        for _ in range(0, 3) {
            for _ in range(0, 90) {
                let k = rng.gen();
                let v = rng.gen();
                if !ctrl.iter().any(|x| x == &(k, v)) {
                    assert!(map.insert(k, v).is_none());
                    ctrl.push((k, v));
                    check_structure(&map);
                    check_equal(ctrl.as_slice(), &map);
                }
            }

            for _ in range(0, 30) {
                let r = rng.gen_range(0, ctrl.len());
                let (key, _) = ctrl.remove(r);
                assert!(map.remove(&key).is_some());
                check_structure(&map);
                check_equal(ctrl.as_slice(), &map);
            }
        }
    }

    #[test]
    fn test_len() {
        let mut m = TreeMap::new();
        assert!(m.insert(3, 6).is_none());
        assert_eq!(m.len(), 1);
        assert!(m.insert(0, 0).is_none());
        assert_eq!(m.len(), 2);
        assert!(m.insert(4, 8).is_none());
        assert_eq!(m.len(), 3);
        assert!(m.remove(&3).is_some());
        assert_eq!(m.len(), 2);
        assert!(!m.remove(&5).is_some());
        assert_eq!(m.len(), 2);
        assert!(m.insert(2, 4).is_none());
        assert_eq!(m.len(), 3);
        assert!(m.insert(1, 2).is_none());
        assert_eq!(m.len(), 4);
    }

    #[test]
    fn test_iterator() {
        let mut m = TreeMap::new();

        assert!(m.insert(3, 6).is_none());
        assert!(m.insert(0, 0).is_none());
        assert!(m.insert(4, 8).is_none());
        assert!(m.insert(2, 4).is_none());
        assert!(m.insert(1, 2).is_none());

        let mut n = 0;
        for (k, v) in m.iter() {
            assert_eq!(*k, n);
            assert_eq!(*v, n * 2);
            n += 1;
        }
        assert_eq!(n, 5);
    }

    #[test]
    fn test_interval_iteration() {
        let mut m = TreeMap::new();
        for i in range(1, 100) {
            assert!(m.insert(i * 2, i * 4).is_none());
        }

        for i in range(1, 198) {
            let mut lb_it = m.lower_bound(&i);
            let (&k, &v) = lb_it.next().unwrap();
            let lb = i + i % 2;
            assert_eq!(lb, k);
            assert_eq!(lb * 2, v);

            let mut ub_it = m.upper_bound(&i);
            let (&k, &v) = ub_it.next().unwrap();
            let ub = i + 2 - i % 2;
            assert_eq!(ub, k);
            assert_eq!(ub * 2, v);
        }
        let mut end_it = m.lower_bound(&199);
        assert_eq!(end_it.next(), None);
    }

    #[test]
    fn test_rev_iter() {
        let mut m = TreeMap::new();

        assert!(m.insert(3, 6).is_none());
        assert!(m.insert(0, 0).is_none());
        assert!(m.insert(4, 8).is_none());
        assert!(m.insert(2, 4).is_none());
        assert!(m.insert(1, 2).is_none());

        let mut n = 4;
        for (k, v) in m.rev_iter() {
            assert_eq!(*k, n);
            assert_eq!(*v, n * 2);
            n -= 1;
        }
    }

    #[test]
    fn test_mut_iter() {
        let mut m = TreeMap::new();
        for i in range(0, 10) {
            assert!(m.insert(i, 100 * i).is_none());
        }

        for (i, (&k, v)) in m.iter_mut().enumerate() {
            *v += k * 10 + i; // 000 + 00 + 0, 100 + 10 + 1, ...
        }

        for (&k, &v) in m.iter() {
            assert_eq!(v, 111 * k);
        }
    }
    #[test]
    fn test_mut_rev_iter() {
        let mut m = TreeMap::new();
        for i in range(0, 10) {
            assert!(m.insert(i, 100 * i).is_none());
        }

        for (i, (&k, v)) in m.rev_iter_mut().enumerate() {
            *v += k * 10 + (9 - i); // 900 + 90 + (9 - 0), 800 + 80 + (9 - 1), ...
        }

        for (&k, &v) in m.iter() {
            assert_eq!(v, 111 * k);
        }
    }

    #[test]
    fn test_mut_interval_iter() {
        let mut m_lower = TreeMap::new();
        let mut m_upper = TreeMap::new();
        for i in range(1, 100) {
            assert!(m_lower.insert(i * 2, i * 4).is_none());
            assert!(m_upper.insert(i * 2, i * 4).is_none());
        }

        for i in range(1, 199) {
            let mut lb_it = m_lower.lower_bound_mut(&i);
            let (&k, v) = lb_it.next().unwrap();
            let lb = i + i % 2;
            assert_eq!(lb, k);
            *v -= k;
        }
        for i in range(0, 198) {
            let mut ub_it = m_upper.upper_bound_mut(&i);
            let (&k, v) = ub_it.next().unwrap();
            let ub = i + 2 - i % 2;
            assert_eq!(ub, k);
            *v -= k;
        }

        assert!(m_lower.lower_bound_mut(&199).next().is_none());

        assert!(m_upper.upper_bound_mut(&198).next().is_none());

        assert!(m_lower.iter().all(|(_, &x)| x == 0));
        assert!(m_upper.iter().all(|(_, &x)| x == 0));
    }

    #[test]
    fn test_keys() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map: TreeMap<i32, char> = vec.into_iter().collect();
        let keys: Vec<i32> = map.keys().map(|&k| k).collect();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains(&1));
        assert!(keys.contains(&2));
        assert!(keys.contains(&3));
    }

    #[test]
    fn test_values() {
        let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
        let map = vec.into_iter().collect::<TreeMap<i32, char>>();
        let values = map.values().map(|&v| v).collect::<Vec<char>>();
        assert_eq!(values.len(), 3);
        assert!(values.contains(&'a'));
        assert!(values.contains(&'b'));
        assert!(values.contains(&'c'));
    }

    #[test]
    fn test_eq() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert!(a == b);
        assert!(a.insert(0, 5).is_none());
        assert!(a != b);
        assert!(b.insert(0, 4).is_none());
        assert!(a != b);
        assert!(a.insert(5, 19).is_none());
        assert!(a != b);
        assert!(!b.insert(0, 5).is_none());
        assert!(a != b);
        assert!(b.insert(5, 19).is_none());
        assert!(a == b);
    }

    #[test]
    fn test_lt() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert!(!(a < b) && !(b < a));
        assert!(b.insert(0, 5).is_none());
        assert!(a < b);
        assert!(a.insert(0, 7).is_none());
        assert!(!(a < b) && b < a);
        assert!(b.insert(-2, 0).is_none());
        assert!(b < a);
        assert!(a.insert(-5, 2).is_none());
        assert!(a < b);
        assert!(a.insert(6, 2).is_none());
        assert!(a < b && !(b < a));
    }

    #[test]
    fn test_ord() {
        let mut a = TreeMap::new();
        let mut b = TreeMap::new();

        assert!(a <= b && a >= b);
        assert!(a.insert(1, 1).is_none());
        assert!(a > b && a >= b);
        assert!(b < a && b <= a);
        assert!(b.insert(2, 2).is_none());
        assert!(b > a && b >= a);
        assert!(a < b && a <= b);
    }

    #[test]
    fn test_debug() {
        let mut map = TreeMap::new();
        let empty: TreeMap<i32, i32> = TreeMap::new();

        map.insert(1, 2);
        map.insert(3, 4);

        assert_eq!(format!("{:?}", map), "{1: 2, 3: 4}");
        assert_eq!(format!("{:?}", empty), "{}");
    }

    #[test]
    fn test_lazy_iterator() {
        let mut m = TreeMap::new();
        let (x1, y1) = (2, 5);
        let (x2, y2) = (9, 12);
        let (x3, y3) = (20, -3);
        let (x4, y4) = (29, 5);
        let (x5, y5) = (103, 3);

        assert!(m.insert(x1, y1).is_none());
        assert!(m.insert(x2, y2).is_none());
        assert!(m.insert(x3, y3).is_none());
        assert!(m.insert(x4, y4).is_none());
        assert!(m.insert(x5, y5).is_none());

        let m = m;
        let mut a = m.iter();

        assert_eq!(a.next().unwrap(), (&x1, &y1));
        assert_eq!(a.next().unwrap(), (&x2, &y2));
        assert_eq!(a.next().unwrap(), (&x3, &y3));
        assert_eq!(a.next().unwrap(), (&x4, &y4));
        assert_eq!(a.next().unwrap(), (&x5, &y5));

        assert!(a.next().is_none());

        let mut b = m.iter();

        let expected = [(&x1, &y1), (&x2, &y2), (&x3, &y3), (&x4, &y4),
                        (&x5, &y5)];
        let mut i = 0;

        for x in b.by_ref() {
            assert_eq!(expected[i], x);
            i += 1;

            if i == 2 {
                break
            }
        }

        for x in b {
            assert_eq!(expected[i], x);
            i += 1;
        }
    }

    #[test]
    fn test_from_iter() {
        let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

        let map: TreeMap<i32, i32> = xs.iter().map(|&x| x).collect();

        for &(k, v) in xs.iter() {
            assert_eq!(map.get(&k), Some(&v));
        }
    }

    #[test]
    fn test_index() {
        let mut map: TreeMap<i32, i32> = TreeMap::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        assert_eq!(map[2], 1);
    }

    #[test]
    #[should_fail]
    fn test_index_nonexistent() {
        let mut map: TreeMap<i32, i32> = TreeMap::new();

        map.insert(1, 2);
        map.insert(2, 1);
        map.insert(3, 4);

        map[4];
    }

    #[test]
    fn test_swap() {
        let mut m = TreeMap::new();
        assert_eq!(m.insert(1, 2), None);
        assert_eq!(m.insert(1, 3), Some(2));
        assert_eq!(m.insert(1, 4), Some(3));
    }

    #[test]
    fn test_pop() {
        let mut m = TreeMap::new();
        m.insert(1, 2);
        assert_eq!(m.remove(&1), Some(2));
        assert_eq!(m.remove(&1), None);
    }

    #[test]
    fn test_comparator_iterator() {
        use compare::{CompareExt, natural};

        let mut m = TreeMap::with_comparator(natural().rev());

        assert!(m.insert(3, 6).is_none());
        assert!(m.insert(0, 0).is_none());
        assert!(m.insert(4, 8).is_none());
        assert!(m.insert(2, 4).is_none());
        assert!(m.insert(1, 2).is_none());

        let mut n = 5;
        for (k, v) in m.iter() {
            n -= 1;
            assert_eq!(*k, n);
            assert_eq!(*v, n * 2);
        }
        assert_eq!(n, 0);
    }

    #[test]
    fn test_comparator_borrowed() {
        use compare::{CompareExt, natural};

        let mut m = TreeMap::with_comparator(natural::<str>().borrow());

        assert!(m.insert("a".to_string(), 1).is_none());

        assert!(m.contains_key("a"));
        assert!(m.contains_key(&"a"));
        assert!(m.contains_key(&"a".to_string()));

        assert_eq!(m.get("a"), Some(&1));
        assert_eq!(m.get(&"a"), Some(&1));
        assert_eq!(m.get(&"a".to_string()), Some(&1));

        m["a"] = 2;

        assert_eq!(m["a"], 2);
        assert_eq!(m["a".to_string()], 2);

        m["a".to_string()] = 3;

        assert_eq!(m.remove("a"), Some(3));
        assert!(m.remove(&"a").is_none());
        assert!(m.remove(&"a".to_string()).is_none());
    }
}

#[cfg(test)]
mod bench {
    use rand::{weak_rng, Rng};
    use test::{Bencher, black_box};

    use super::TreeMap;
    use bench::{insert_rand_n, insert_seq_n, find_rand_n, find_seq_n};

    #[bench]
    pub fn insert_rand_100(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        insert_rand_n(100, &mut m, b,
                      |m, i| { m.insert(i, 1); },
                      |m, i| { m.remove(&i); });
    }

    #[bench]
    pub fn insert_rand_10_000(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        insert_rand_n(10_000, &mut m, b,
                      |m, i| { m.insert(i, 1); },
                      |m, i| { m.remove(&i); });
    }

    // Insert seq
    #[bench]
    pub fn insert_seq_100(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        insert_seq_n(100, &mut m, b,
                     |m, i| { m.insert(i, 1); },
                     |m, i| { m.remove(&i); });
    }

    #[bench]
    pub fn insert_seq_10_000(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        insert_seq_n(10_000, &mut m, b,
                     |m, i| { m.insert(i, 1); },
                     |m, i| { m.remove(&i); });
    }

    // Find rand
    #[bench]
    pub fn find_rand_100(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        find_rand_n(100, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn find_rand_10_000(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        find_rand_n(10_000, &mut m, b,
                    |m, i| { m.insert(i, 1); },
                    |m, i| { m.get(&i); });
    }

    // Find seq
    #[bench]
    pub fn find_seq_100(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        find_seq_n(100, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    #[bench]
    pub fn find_seq_10_000(b: &mut Bencher) {
        let mut m: TreeMap<u32,u32> = TreeMap::new();
        find_seq_n(10_000, &mut m, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| { m.get(&i); });
    }

    fn bench_iter(b: &mut Bencher, size: usize) {
        let mut map = TreeMap::<u32, u32>::new();
        let mut rng = weak_rng();

        for _ in range(0, size) {
            map.insert(rng.gen(), rng.gen());
        }

        b.iter(|| {
            for entry in map.iter() {
                black_box(entry);
            }
        });
    }

    #[bench]
    pub fn iter_20(b: &mut Bencher) {
        bench_iter(b, 20);
    }

    #[bench]
    pub fn iter_1000(b: &mut Bencher) {
        bench_iter(b, 1000);
    }

    #[bench]
    pub fn iter_100000(b: &mut Bencher) {
        bench_iter(b, 100000);
    }

    fn bench_lower_bound(b: &mut Bencher, size: u32) {
        let mut map = TreeMap::<u32, u32>::new();
        find_seq_n(size, &mut map, b,
                   |m, i| { m.insert(i, 1); },
                   |m, i| for entry in m.lower_bound(&i) {
                       black_box(entry);
                   });
    }

    #[bench]
    pub fn lower_bound_20(b: &mut Bencher) {
        bench_lower_bound(b, 20);
    }

    #[bench]
    pub fn lower_bound_1000(b: &mut Bencher) {
        bench_lower_bound(b, 1000);
    }

    #[bench]
    pub fn lower_bound_100000(b: &mut Bencher) {
        bench_lower_bound(b, 100000);
    }
}
