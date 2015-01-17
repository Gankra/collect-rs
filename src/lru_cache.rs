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

use linked_hash_map::LinkedHashMap;

// FIXME(conventions): implement iterators?
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
}
