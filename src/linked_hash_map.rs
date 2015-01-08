// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


//! A HashMap wrapper that holds key-value pairs in insertion order.
//!
//! # Examples
//!
//! ```rust
//! use collect::LinkedHashMap;
//!
//! let mut map = LinkedHashMap::new();
//! map.insert(2i, 20i);
//! map.insert(1, 10);
//! map.insert(3, 30);
//! assert_eq!(*map.get(&1).unwrap(), 10);
//! assert_eq!(*map.get(&2).unwrap(), 20);
//! assert_eq!(*map.get(&3).unwrap(), 30);
//!
//! let items: Vec<(int, int)> = map.iter().map(|t| (*t.0, *t.1)).collect();
//! assert_eq!(vec![(2, 20), (1, 10), (3, 30)], items);
//! ```

use std::cmp::{PartialEq, Eq};
use std::collections::HashMap;
use std::iter;
use std::kinds::marker;
use std::fmt;
use std::hash::Hash;
use std::iter::{Iterator, Extend};
use std::mem;
use std::ptr;

// FIXME(conventions): implement indexing?

struct KeyRef<K> { k: *const K }

struct LinkedHashMapEntry<K, V> {
    next: *mut LinkedHashMapEntry<K, V>,
    prev: *mut LinkedHashMapEntry<K, V>,
    key: K,
    value: V,
}

/// A linked hash map.
pub struct LinkedHashMap<K, V> {
    map: HashMap<KeyRef<K>, Box<LinkedHashMapEntry<K, V>>>,
    head: *mut LinkedHashMapEntry<K, V>,
}

impl<S, K: Hash<S>> Hash<S> for KeyRef<K> {
    fn hash(&self, state: &mut S) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &KeyRef<K>) -> bool {
        unsafe{ (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

impl<K, V> LinkedHashMapEntry<K, V> {
    fn new(k: K, v: V) -> LinkedHashMapEntry<K, V> {
        LinkedHashMapEntry {
            key: k,
            value: v,
            next: ptr::null_mut(),
            prev: ptr::null_mut(),
        }
    }
}

impl<K: Hash + Eq, V> LinkedHashMap<K, V> {
    /// Creates a linked hash map.
    pub fn new() -> LinkedHashMap<K, V> {
        let map = LinkedHashMap {
            map: HashMap::new(),
            head: unsafe{ mem::transmute(box mem::uninitialized::<LinkedHashMapEntry<K, V>>()) },
        };
        unsafe {
            (*map.head).next = map.head;
            (*map.head).prev = map.head;
        }
        return map;
    }

    /// Inserts a key-value pair into the map. If the key already existed, the old value is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1i, "a");
    /// map.insert(2, "b");
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"b"));
    /// ```
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let (node_ptr, node_opt, old_val) = match self.map.get_mut(&KeyRef{k: &k}) {
            Some(node) => {
                let old_val = mem::replace(&mut node.value, v);
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (node_ptr, None, Some(old_val))
            }
            None => {
                let mut node = box LinkedHashMapEntry::new(k, v);
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut *node;
                (node_ptr, Some(node), None)
            }
        };
        match node_opt {
            None => {
                // Existing node, just update LRU position
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
            Some(node) => {
                let keyref = unsafe { &(*node_ptr).key };
                self.map.insert(KeyRef{k: keyref}, node);
                self.attach(node_ptr);
            }
        }
        old_val
    }

    /// Returns the value corresponding to the key in the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1i, "a");
    /// map.insert(2, "b");
    /// map.insert(2, "c");
    /// map.insert(3, "d");
    ///
    /// assert_eq!(map.get(&1), Some(&"a"));
    /// assert_eq!(map.get(&2), Some(&"c"));
    /// ```
    pub fn get(&self, k: &K) -> Option<&V> {
        self.map.get(&KeyRef{k: k}).map(|e| &e.value)
    }

    /// Returns the value corresponding to the key in the map.
    ///
    /// If value is found, it is moved to the end of the list.
    /// This operation can be used in implemenation of LRU cache.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(1i, "a");
    /// map.insert(2, "b");
    /// map.insert(3, "d");
    ///
    /// assert_eq!(map.get_refresh(&2), Some(&"b"));
    ///
    /// assert_eq!((&2, &"b"), map.iter().rev().next().unwrap());
    /// ```
    pub fn get_refresh(&mut self, k: &K) -> Option<&V> {
        let (value, node_ptr_opt) = match self.map.get_mut(&KeyRef{k: k}) {
            None => (None, None),
            Some(node) => {
                let node_ptr: *mut LinkedHashMapEntry<K, V> = &mut **node;
                (Some(unsafe { &(*node_ptr).value }), Some(node_ptr))
            }
        };
        match node_ptr_opt {
            None => (),
            Some(node_ptr) => {
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
        }
        return value;
    }

    /// Removes and returns the value corresponding to the key from the map.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    ///
    /// map.insert(2i, "a");
    ///
    /// assert_eq!(map.remove(&1), None);
    /// assert_eq!(map.remove(&2), Some("a"));
    /// assert_eq!(map.remove(&2), None);
    /// assert_eq!(map.len(), 0);
    /// ```
    pub fn remove(&mut self, k: &K) -> Option<V> {
        let removed = self.map.remove(&KeyRef{k: k});
        removed.map(|mut node| {
            let node_ptr: *mut LinkedHashMapEntry<K,V> = &mut *node;
            self.detach(node_ptr);
            node.value
        })
    }

    /// Returns the maximum number of key-value pairs the map can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map: LinkedHashMap<int, &str> = LinkedHashMap::new();
    /// let capacity = map.capacity();
    /// ```
    pub fn capacity(&self) -> uint {
        self.map.capacity()
    }

    /// Removes the first entry.
    ///
    /// Can be used in implementation of LRU cache.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::LinkedHashMap;
    /// let mut map = LinkedHashMap::new();
    /// map.insert(1i, 10i);
    /// map.insert(2, 20);
    /// map.pop_front();
    /// assert_eq!(map.get(&1), None);
    /// assert_eq!(map.get(&2), Some(&20));
    /// ```
    #[inline]
    pub fn pop_front(&mut self) {
        if self.len() > 0 {
            let lru = unsafe { (*self.head).prev };
            self.detach(lru);
            self.map.remove(&KeyRef{k: unsafe { &(*lru).key }});
        }
    }

    /// Returns the number of key-value pairs in the map.
    pub fn len(&self) -> uint { self.map.len() }

    /// Returns whether the map is currently empty.
    pub fn is_empty(&self) -> bool { self.len() == 0 }

    /// Clear the map of all key-value pairs.
    pub fn clear(&mut self) {
        self.map.clear();
        unsafe {
            (*self.head).prev = self.head;
            (*self.head).next = self.head;
        }
    }

    /// A double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a V)`
    ///
    /// # Examples
    /// ```rust
    /// use collect::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert("a", 10);
    /// map.insert("c", 30);
    /// map.insert("b", 20);
    ///
    /// let mut iter = map.iter();
    /// assert_eq!((&"a", &10), iter.next().unwrap());
    /// assert_eq!((&"c", &30), iter.next().unwrap());
    /// assert_eq!((&"b", &20), iter.next().unwrap());
    /// assert_eq!(None, iter.next());
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            head: unsafe { (*self.head).prev },
            tail: self.head,
            remaining: self.len(),
            marker: marker::ContravariantLifetime,
        }
    }

    /// A double-ended iterator visiting all key in order of insertion.
    ///
    /// # Examples
    /// ```rust
    /// use collect::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert('a', 10i);
    /// map.insert('c', 30);
    /// map.insert('b', 20);
    ///
    /// let mut keys = map.keys();
    /// assert_eq!(&'a', keys.next().unwrap());
    /// assert_eq!(&'c', keys.next().unwrap());
    /// assert_eq!(&'b', keys.next().unwrap());
    /// assert_eq!(None, keys.next());
    /// ```
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        fn first<A, B>((a, _): (A, B)) -> A { a }
        let first: fn((&'a K, &'a V)) -> &'a K = first; // coerce to fn ptr

        Keys { inner: self.iter().map(first) }
    }

    /// A double-ended iterator visiting all values in order of insertion.
    ///
    /// # Examples
    /// ```rust
    /// use collect::LinkedHashMap;
    ///
    /// let mut map = LinkedHashMap::new();
    /// map.insert('a', 10i);
    /// map.insert('c', 30);
    /// map.insert('b', 20);
    ///
    /// let mut values = map.values();
    /// assert_eq!(&10, values.next().unwrap());
    /// assert_eq!(&30, values.next().unwrap());
    /// assert_eq!(&20, values.next().unwrap());
    /// assert_eq!(None, values.next());
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        fn second<A, B>((_, b): (A, B)) -> B { b }
        let second: fn((&'a K, &'a V)) -> &'a V = second; // coerce to fn ptr

        Values { inner: self.iter().map(second) }
    }
}

impl<K: Hash + Eq, V> LinkedHashMap<K, V> {
    #[inline]
    fn detach(&mut self, node: *mut LinkedHashMapEntry<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    #[inline]
    fn attach(&mut self, node: *mut LinkedHashMapEntry<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }
}


impl<K: Hash + Eq, V> Extend<(K, V)> for LinkedHashMap<K, V> {
    fn extend<T: Iterator<Item=(K, V)>>(&mut self, mut iter: T) {
        for (k, v) in iter{
            self.insert(k, v);
        }
    }
}

impl<A: fmt::Show + Hash + Eq, B: fmt::Show> fmt::Show for LinkedHashMap<A, B> {
    /// Returns a string that lists the key-value pairs in insertion order.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{}: {}", *k, *v));
        }

        write!(f, "}}")
    }
}

unsafe impl<K: Send, V: Send> Send for LinkedHashMap<K, V> {}

unsafe impl<K: Sync, V: Sync> Sync for LinkedHashMap<K, V> {}

#[unsafe_destructor]
impl<K, V> Drop for LinkedHashMap<K, V> {
    fn drop(&mut self) {
        unsafe {
            let node: Box<LinkedHashMapEntry<K, V>> = mem::transmute(self.head);
            // Prevent compiler from trying to drop the un-initialized field in the sigil node.
            let box internal_node = node;
            let LinkedHashMapEntry { next: _, prev: _, key: k, value: v } = internal_node;
            mem::forget(k);
            mem::forget(v);
        }
    }
}

pub struct Iter<'a, K: 'a, V: 'a> {
    head: *const LinkedHashMapEntry<K, V>,
    tail: *const LinkedHashMapEntry<K, V>,
    remaining: uint,
    marker: marker::ContravariantLifetime<'a>,
}

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                let r = Some((&(*self.head).key, &(*self.head).value));
                self.head = (*self.head).prev;
                r
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        (self.remaining, Some(self.remaining))
    }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> {
        if self.head == self.tail {
            None
        } else {
            self.remaining -= 1;
            unsafe {
                self.tail = (*self.tail).next;
                let r = Some((&(*self.tail).key, &(*self.tail).value));
                r
            }
        }
    }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}


pub struct Keys<'a, K: 'a, V: 'a> {
    inner: iter::Map<(&'a K, &'a V), &'a K, Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>
}

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    #[inline] fn next(&mut self) -> Option<(&'a K)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (uint, Option<uint>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a K)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {}


pub struct Values<'a, K: 'a, V: 'a> {
    inner: iter::Map<(&'a K, &'a V), &'a V, Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>
}

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    #[inline] fn next(&mut self) -> Option<(&'a V)> { self.inner.next() }
    #[inline] fn size_hint(&self) -> (uint, Option<uint>) { self.inner.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    #[inline] fn next_back(&mut self) -> Option<(&'a V)> { self.inner.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {}


#[cfg(test)]
mod tests {
    use super::LinkedHashMap;

    fn assert_opt_eq<V: PartialEq>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert!(opt.unwrap() == &v);
    }

    #[test]
    fn test_insert_and_get() {
        let mut map = LinkedHashMap::new();
        map.insert(1i, 10i);
        map.insert(2, 20);
        assert_opt_eq(map.get(&1), 10);
        assert_opt_eq(map.get(&2), 20);
        assert_eq!(map.len(), 2);
    }

    #[test]
    fn test_insert_update() {
        let mut map = LinkedHashMap::new();
        map.insert("1".to_string(), vec![10i, 10]);
        map.insert("1".to_string(), vec![10, 19]);
        assert_opt_eq(map.get(&"1".to_string()), vec![10, 19]);
        assert_eq!(map.len(), 1);
    }

    #[test]
    fn test_to_string() {
        let mut map = LinkedHashMap::new();
        assert_eq!(map.to_string(), "{}");
        map.insert(1i, 10i);
        map.insert(2, 20);
        map.insert(3, 30);
        assert_eq!(map.to_string(), "{1: 10, 2: 20, 3: 30}");
        map.insert(2, 22);
        assert_eq!(map.to_string(), "{1: 10, 3: 30, 2: 22}");
        map.get(&3);
        assert_eq!(map.to_string(), "{1: 10, 3: 30, 2: 22}");
        map.get_refresh(&3);
        assert_eq!(map.to_string(), "{1: 10, 2: 22, 3: 30}");
        map.clear();
        assert_eq!(map.to_string(), "{}");
    }

    #[test]
    fn test_remove() {
        let mut map = LinkedHashMap::new();
        map.insert(1i, 10i);
        map.insert(2, 20);
        map.insert(3, 30);
        map.insert(4, 40);
        map.insert(5, 50);
        map.remove(&3);
        map.remove(&4);
        assert!(map.get(&3).is_none());
        assert!(map.get(&4).is_none());
        map.insert(6, 60);
        map.insert(7, 70);
        map.insert(8, 80);
        assert_opt_eq(map.get(&6), 60);
        assert_opt_eq(map.get(&7), 70);
        assert_opt_eq(map.get(&8), 80);
    }

    #[test]
    fn test_clear() {
        let mut map = LinkedHashMap::new();
        map.insert(1i, 10i);
        map.insert(2, 20);
        map.clear();
        assert!(map.get(&1).is_none());
        assert!(map.get(&2).is_none());
        assert_eq!(map.to_string(), "{}");
    }

    #[test]
    fn test_iter() {
        let mut map = LinkedHashMap::new();

        // empty iter
        assert_eq!(None, map.iter().next());

        map.insert("a", 10);
        map.insert("b", 20);
        map.insert("c", 30);

        // regular iter
        let mut iter = map.iter();
        assert_eq!((&"a", &10), iter.next().unwrap());
        assert_eq!((&"b", &20), iter.next().unwrap());
        assert_eq!((&"c", &30), iter.next().unwrap());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());

        // reversed iter
        let mut rev_iter = map.iter().rev();
        assert_eq!((&"c", &30), rev_iter.next().unwrap());
        assert_eq!((&"b", &20), rev_iter.next().unwrap());
        assert_eq!((&"a", &10), rev_iter.next().unwrap());
        assert_eq!(None, rev_iter.next());
        assert_eq!(None, rev_iter.next());

        // mixed
        let mut mixed_iter = map.iter();
        assert_eq!((&"a", &10), mixed_iter.next().unwrap());
        assert_eq!((&"c", &30), mixed_iter.next_back().unwrap());
        assert_eq!((&"b", &20), mixed_iter.next().unwrap());
        assert_eq!(None, mixed_iter.next());
        assert_eq!(None, mixed_iter.next_back());
    }
}
