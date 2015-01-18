// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.


//! A cache that holds a limited number of key-value pairs. When the
//! capacity of the cache is exceeded, the least-recently-used
//! (where "used" means a look-up or putting the pair into the cache)
//! pair is automatically removed.
//!
//! # Example
//!
//! ```rust
//! use collect::LruCache;
//!
//! let mut cache = LruCache::new(2);
//! cache.insert(1, 10);
//! cache.insert(2, 20);
//! cache.insert(3, 30);
//! assert!(cache.get(&1).is_none());
//! assert_eq!(*cache.get(&2).unwrap(), 20);
//! assert_eq!(*cache.get(&3).unwrap(), 30);
//!
//! cache.insert(2, 22);
//! assert_eq!(*cache.get(&2).unwrap(), 22);
//!
//! cache.insert(6, 60);
//! assert!(cache.get(&3).is_none());
//!
//! cache.set_capacity(1);
//! assert!(cache.get(&2).is_none());
//! ```

use std::fmt;
use std::hash::Hash;
use std::collections::hash_map::Hasher as HmHasher;
use std::iter::{range, Iterator, Extend};

use linked_hash_map::{self, LinkedHashMap};

// FIXME(conventions): implement indexing?

/// An LRU Cache.
pub struct LruCache<K, V> {
    map: LinkedHashMap<K, V>,
    max_size: usize,
}

impl<K: Hash<HmHasher> + Eq, V> LruCache<K, V> {
    /// Create an LRU Cache that holds at most `capacity` items.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache: LruCache<i32, &str> = LruCache::new(10);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn new(capacity: usize) -> LruCache<K, V> {
        LruCache {
            map: LinkedHashMap::new(),
            max_size: capacity,
        }
    }

    /// Inserts a key-value pair into the cache. If the key already existed, the old value is
    /// returned.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn insert(&mut self, k: K, v: V) -> Option<V> {
        let old_val = self.map.insert(k, v);
        if self.len() > self.capacity() {
            self.remove_lru();
        }
        old_val
    }

    /// Return a value corresponding to the key in the cache.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(2, "c");
    /// cache.insert(3, "d");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn get(&mut self, k: &K) -> Option<&V> {
        self.map.get_refresh(k)
    }

    /// Remove and return a value corresponding to the key from the cache.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(2, "a");
    ///
    /// assert_eq!(cache.remove(&1), None);
    /// assert_eq!(cache.remove(&2), Some("a"));
    /// assert_eq!(cache.remove(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn remove(&mut self, k: &K) -> Option<V> {
        self.map.remove(k)
    }

    /// Return the maximum number of key-value pairs the cache can hold.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache: LruCache<i32, &str> = LruCache::new(2);
    /// assert_eq!(cache.capacity(), 2);
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn capacity(&self) -> usize {
        self.max_size
    }

    /// Change the number of key-value pairs the cache can hold. Remove
    /// least-recently-used key-value pairs if necessary.
    ///
    /// # Example
    ///
    /// ```rust
    /// use collect::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    /// cache.insert(3, "c");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(3);
    /// cache.insert(1, "a");
    /// cache.insert(2, "b");
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    ///
    /// cache.set_capacity(1);
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), None);
    /// assert_eq!(cache.get(&3), Some(&"c"));
    /// ```
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn set_capacity(&mut self, capacity: usize) {
        for _ in range(capacity, self.len()) {
            self.remove_lru();
        }
        self.max_size = capacity;
    }

    #[inline]
    fn remove_lru(&mut self) {
        self.map.pop_front()
    }

    /// Return the number of key-value pairs in the cache.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn len(&self) -> usize { self.map.len() }

    /// Returns whether the cache is currently empty.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn is_empty(&self) -> bool { self.map.is_empty() }

    /// Clear the cache of all key-value pairs.
    #[unstable = "matches collection reform specification, waiting for dust to settle"]
    pub fn clear(&mut self) { self.map.clear(); }

    /// A double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a mut V)`
    ///
    /// # Examples
    /// ```
    /// use collect::LruCache;
    ///
    /// let mut cache = LruCache::new(3);
    /// cache.insert("a", 10);
    /// cache.insert("c", 30);
    /// cache.insert("b", 20);
    ///
    /// let mut iter = cache.iter();
    /// assert_eq!((&"a", &10), iter.next().unwrap());
    /// assert_eq!((&"c", &30), iter.next().unwrap());
    /// assert_eq!((&"b", &20), iter.next().unwrap());
    /// ```
    pub fn iter(&self) -> Iter<K, V> {
        Iter(self.map.iter())
    }

    /// A double-ended iterator visiting all key-value pairs in order of insertion.
    /// Iterator element type is `(&'a K, &'a V)`
    ///
    /// # Examples
    /// ```
    /// use collect::LruCache;
    ///
    /// let mut cache = LruCache::new(3);
    /// cache.insert("a", 10);
    /// cache.insert("c", 30);
    /// cache.insert("b", 20);
    ///
    /// {
    ///     let mut iter = cache.iter_mut();
    ///     let mut entry = iter.next().unwrap();
    ///     assert_eq!(&"a", entry.0);
    ///     *entry.1 = 17;
    /// }
    ///
    /// assert_eq!(&17, cache.get(&"a").unwrap());
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<K, V> {
        IterMut(self.map.iter_mut())
    }

    /// A double-ended iterator visiting all keys in order of insertion.
    ///
    /// # Examples
    /// ```
    /// use collect::LruCache;
    ///
    /// let mut cache = LruCache::new(3);
    /// cache.insert('a', 10);
    /// cache.insert('c', 30);
    /// cache.insert('b', 20);
    ///
    /// let mut keys = cache.keys();
    /// assert_eq!(&'a', keys.next().unwrap());
    /// assert_eq!(&'c', keys.next().unwrap());
    /// assert_eq!(&'b', keys.next().unwrap());
    /// assert_eq!(None, keys.next());
    /// ```
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        Keys(self.map.keys())
    }

    /// A double-ended iterator visiting all values in order of insertion.
    ///
    /// # Examples
    /// ```
    /// use collect::LruCache;
    ///
    /// let mut cache = LruCache::new(3);
    /// cache.insert('a', 10);
    /// cache.insert('c', 30);
    /// cache.insert('b', 20);
    ///
    /// let mut values = cache.values();
    /// assert_eq!(&10, values.next().unwrap());
    /// assert_eq!(&30, values.next().unwrap());
    /// assert_eq!(&20, values.next().unwrap());
    /// assert_eq!(None, values.next());
    /// ```
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        Values(self.map.values())
    }
}

impl<K: Hash<HmHasher> + Eq, V> Extend<(K, V)> for LruCache<K, V> {
    fn extend<T: Iterator<Item=(K, V)>>(&mut self, mut iter: T) {
        for (k, v) in iter{
            self.insert(k, v);
        }
    }
}

impl<A: fmt::Show + Hash<HmHasher> + Eq, B: fmt::Show> fmt::Show for LruCache<A, B> {
    /// Return a string that lists the key-value pairs from most-recently
    /// used to least-recently used.
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "{{"));

        for (i, (k, v)) in self.map.iter().rev().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{:?}: {:?}", *k, *v));
        }

        write!(f, "}}")
    }
}

unsafe impl<K: Send, V: Send> Send for LruCache<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for LruCache<K, V> {}

pub struct Iter<'a, K: 'a, V: 'a>(linked_hash_map::Iter<'a, K, V>);

impl<'a, K, V> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<(&'a K, &'a V)> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a V)> { self.0.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Iter<'a, K, V> {}

pub struct IterMut<'a, K: 'a, V: 'a>(linked_hash_map::IterMut<'a, K, V>);

impl<'a, K, V> Iterator for IterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<(&'a K, &'a mut V)> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for IterMut<'a, K, V> {
    fn next_back(&mut self) -> Option<(&'a K, &'a mut V)> { self.0.next_back() }
}

impl<'a, K, V> ExactSizeIterator for IterMut<'a, K, V> {}

pub struct Keys<'a, K: 'a, V: 'a>(linked_hash_map::Keys<'a, K, V>);

impl<'a, K, V> Iterator for Keys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Keys<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a K> { self.0.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Keys<'a, K, V> {}

pub struct Values<'a, K: 'a, V: 'a>(linked_hash_map::Values<'a, K, V>);

impl<'a, K, V> Iterator for Values<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<&'a V> { self.0.next() }
    fn size_hint(&self) -> (usize, Option<usize>) { self.0.size_hint() }
}

impl<'a, K, V> DoubleEndedIterator for Values<'a, K, V> {
    fn next_back(&mut self) -> Option<&'a V> { self.0.next_back() }
}

impl<'a, K, V> ExactSizeIterator for Values<'a, K, V> {}


#[cfg(test)]
mod tests {
    use super::LruCache;

    fn assert_opt_eq<V: PartialEq>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert!(opt.unwrap() == &v);
    }

    #[test]
    fn test_put_and_get() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        assert_opt_eq(cache.get(&1), 10);
        assert_opt_eq(cache.get(&2), 20);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_put_update() {
        let mut cache: LruCache<String, Vec<u8>> = LruCache::new(1);
        cache.insert("1".to_string(), vec![10, 10]);
        cache.insert("1".to_string(), vec![10, 19]);
        assert_opt_eq(cache.get(&"1".to_string()), vec![10, 19]);
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_expire_lru() {
        let mut cache: LruCache<String, String> = LruCache::new(2);
        cache.insert("foo1".to_string(), "bar1".to_string());
        cache.insert("foo2".to_string(), "bar2".to_string());
        cache.insert("foo3".to_string(), "bar3".to_string());
        assert!(cache.get(&"foo1".to_string()).is_none());
        cache.insert("foo2".to_string(), "bar2update".to_string());
        cache.insert("foo4".to_string(), "bar4".to_string());
        assert!(cache.get(&"foo3".to_string()).is_none());
    }

    #[test]
    fn test_pop() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        assert_eq!(cache.len(), 2);
        let opt1 = cache.remove(&1);
        assert!(opt1.is_some());
        assert_eq!(opt1.unwrap(), 10);
        assert!(cache.get(&1).is_none());
        assert_eq!(cache.len(), 1);
    }

    #[test]
    fn test_change_capacity() {
        let mut cache = LruCache::new(2);
        assert_eq!(cache.capacity(), 2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.set_capacity(1);
        assert!(cache.get(&1).is_none());
        assert_eq!(cache.capacity(), 1);
    }

    #[test]
    fn test_show() {
        let mut cache: LruCache<i32, i32> = LruCache::new(3);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        assert_eq!(format!("{:?}", cache), "{3i32: 30i32, 2i32: 20i32, 1i32: 10i32}");
        cache.insert(2, 22);
        assert_eq!(format!("{:?}", cache), "{2i32: 22i32, 3i32: 30i32, 1i32: 10i32}");
        cache.insert(6, 60);
        assert_eq!(format!("{:?}", cache), "{6i32: 60i32, 2i32: 22i32, 3i32: 30i32}");
        cache.get(&3);
        assert_eq!(format!("{:?}", cache), "{3i32: 30i32, 6i32: 60i32, 2i32: 22i32}");
        cache.set_capacity(2);
        assert_eq!(format!("{:?}", cache), "{3i32: 30i32, 6i32: 60i32}");
    }

    #[test]
    fn test_remove() {
        let mut cache = LruCache::new(3);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.insert(3, 30);
        cache.insert(4, 40);
        cache.insert(5, 50);
        cache.remove(&3);
        cache.remove(&4);
        assert!(cache.get(&3).is_none());
        assert!(cache.get(&4).is_none());
        cache.insert(6, 60);
        cache.insert(7, 70);
        cache.insert(8, 80);
        assert!(cache.get(&5).is_none());
        assert_opt_eq(cache.get(&6), 60);
        assert_opt_eq(cache.get(&7), 70);
        assert_opt_eq(cache.get(&8), 80);
    }

    #[test]
    fn test_clear() {
        let mut cache = LruCache::new(2);
        cache.insert(1, 10);
        cache.insert(2, 20);
        cache.clear();
        assert!(cache.get(&1).is_none());
        assert!(cache.get(&2).is_none());
        assert_eq!(format!("{:?}", cache), "{}");
    }

    #[test]
    fn test_iter() {
        let mut cache = LruCache::new(3);

        // empty iter
        assert_eq!(None, cache.iter().next());

        cache.insert("a", 10);
        cache.insert("b", 20);
        cache.insert("c", 30);

        // regular iter
        let mut iter = cache.iter();
        assert_eq!((&"a", &10), iter.next().unwrap());
        assert_eq!((&"b", &20), iter.next().unwrap());
        assert_eq!((&"c", &30), iter.next().unwrap());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next());

        // reversed iter
        let mut rev_iter = cache.iter().rev();
        assert_eq!((&"c", &30), rev_iter.next().unwrap());
        assert_eq!((&"b", &20), rev_iter.next().unwrap());
        assert_eq!((&"a", &10), rev_iter.next().unwrap());
        assert_eq!(None, rev_iter.next());
        assert_eq!(None, rev_iter.next());

        // mixed
        let mut mixed_iter = cache.iter();
        assert_eq!((&"a", &10), mixed_iter.next().unwrap());
        assert_eq!((&"c", &30), mixed_iter.next_back().unwrap());
        assert_eq!((&"b", &20), mixed_iter.next().unwrap());
        assert_eq!(None, mixed_iter.next());
        assert_eq!(None, mixed_iter.next_back());
    }

    #[test]
    fn test_iter_mut() {
        let mut cache = LruCache::new(3);
        cache.insert("a", 10);
        cache.insert("c", 30);
        cache.insert("b", 20);

        {
            let mut iter = cache.iter_mut();
            let entry = iter.next().unwrap();
            assert_eq!(&"a", entry.0);
            *entry.1 = 17;

            // reverse iterator
            let mut iter = iter.rev();
            let entry = iter.next().unwrap();
            assert_eq!(&"b", entry.0);
            *entry.1 = 23;

            let entry = iter.next().unwrap();
            assert_eq!(&"c", entry.0);
            assert_eq!(None, iter.next());
            assert_eq!(None, iter.next());
        }

        assert_eq!(&17, cache.get(&"a").unwrap());
        assert_eq!(&23, cache.get(&"b").unwrap());
    }
}
