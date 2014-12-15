use std::default::Default;
use std::borrow::BorrowFrom;

use super::map::{mod, SplayMap};

#[deriving(Clone)]
pub struct SplaySet<T> {
    map: SplayMap<T, ()>
}

pub struct IntoIter<T> {
    inner: map::IntoIter<T, ()>,
}

impl<T: Ord> SplaySet<T> {
    /// Creates a new empty set
    pub fn new() -> SplaySet<T> { SplaySet { map: SplayMap::new() } }

    /// Moves all values out of this set, transferring ownership to the given
    /// iterator.
    pub fn into_iter(self) -> IntoIter<T> {
        IntoIter { inner: self.map.into_iter() }
    }

    pub fn len(&self) -> uint { self.map.len() }
    pub fn is_empty(&self) -> bool { self.len() == 0 }
    pub fn clear(&mut self) { self.map.clear() }

    /// Return true if the set contains a value
    pub fn contains<Sized? Q>(&self, item: &Q) -> bool
                              where Q: BorrowFrom<T> + Ord {
        self.map.contains_key(item)
    }

    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    pub fn insert(&mut self, t: T) -> bool {
        self.map.insert(t, ()).is_none()
    }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    pub fn remove<Sized? Q>(&mut self, item: &Q) -> bool
                            where Q: BorrowFrom<T> + Ord {
        self.map.remove(item).is_some()
    }
}

impl<T> Iterator<T> for IntoIter<T> {
    fn next(&mut self) -> Option<T> { self.inner.next().map(|p| p.val0()) }
    fn size_hint(&self) -> (uint, Option<uint>) { self.inner.size_hint() }
}

impl<T> DoubleEndedIterator<T> for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        self.inner.next_back().map(|(k, _)| k)
    }
}

impl<T> ExactSizeIterator<T> for IntoIter<T> {}

impl<T: Ord> Default for SplaySet<T> {
    fn default() -> SplaySet<T> { SplaySet::new() }
}

impl<T: Ord> FromIterator<T> for SplaySet<T> {
    fn from_iter<I: Iterator<T>>(iterator: I) -> SplaySet<T> {
        let mut set = SplaySet::new();
        set.extend(iterator);
        set
    }
}

impl<T: Ord> Extend<T> for SplaySet<T> {
    fn extend<I: Iterator<T>>(&mut self, mut i: I) {
        for t in i { self.insert(t); }
    }
}
