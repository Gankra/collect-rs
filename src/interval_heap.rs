//! A double-ended priority queue implemented with an interval heap.

use std::slice;
use std::default::Default;

use compare::{Compare, Natural};

// An interval heap is a binary tree structure with the following properties:
//
// (1) Each node (except possibly the last leaf) contains two values
//     where the first one is less than or equal to the second one.
// (2) Each node represents a closed interval.
// (3) A child node's interval is completely contained in the parent node's
//     interval.
//
// This implies that the min and max elements are always in the root node.
//
// This interval heap implementation stores its nodes in a linear array
// using a Vec. Here's an example of the layout of a tree with 13 items
// (7 nodes) where the numbers represent the *offsets* in the array:
//
//          (0 1)
//         /     \
//    (2 3)       (4 5)
//    /   \       /    \
//  (6 7)(8 9)(10 11)(12 --)
//
// Even indices are used for the "left" element of a node while odd indices
// are used for the "right" element of a node. Note: the last node may not
// have a "right" element.

// FIXME: There may be a better algorithm for turning a vector into an
// interval heap. Right now, this takes O(n log n) time, I think.


fn is_root(x: uint) -> bool { x < 2 }

/// Set LSB to zero for the "left" item index of a node.
fn left(x: uint) -> uint { x & !1u }

/// Returns index of "left" item of parent node.
fn parent_left(x: uint) -> uint {
    debug_assert!(!is_root(x));
    left((x - 2) / 2)
}

/// The first `v.len() - 1` elements are considered a valid interval heap
/// and the last element is to be inserted.
fn interval_heap_push<T, C: Compare<T>>(v: &mut [T], cmp: &C) {
    debug_assert!(v.len() > 0);
    // Start with the last new/modified node and work our way to
    // the root if necessary...
    let mut node_max = v.len() - 1;
    let mut node_min = left(node_max);
    // The reason for using two variables instead of one is to
    // get around the special case of the last node only containing
    // one element (node_min == node_max).
    if cmp.compares_gt(&v[node_min], &v[node_max]) { v.swap(node_min, node_max); }
    while !is_root(node_min) {
        let par_min = parent_left(node_min);
        let par_max = par_min + 1;
        if cmp.compares_lt(&v[node_min], &v[par_min]) {
            v.swap(par_min, node_min);
        } else if cmp.compares_lt(&v[par_max], &v[node_max]) {
            v.swap(par_max, node_max);
        } else {
            return; // nothing to do anymore
        }
        debug_assert!(cmp.compares_le(&v[node_min], &v[node_max]));
        node_min = par_min;
        node_max = par_max;
    }
}

/// The min element in the root node of an otherwise valid interval heap
/// has been been replaced with some other value without violating rule (1)
/// for the root node. This function restores the interval heap properties.
fn update_min<T, C: Compare<T>>(v: &mut [T], cmp: &C) {
    // Starting at the root, we go down the tree...
    debug_assert!(cmp.compares_le(&v[0], &v[1]));
    let mut left = 0;
    loop {
        let c1 = left * 2 + 2; // index of 1st child's left element
        let c2 = left * 2 + 4; // index of 2nd child's left element
        if v.len() <= c1 { return; } // No children. We're done.
        // Pick child with lowest min
        let ch = if v.len() <= c2 || cmp.compares_lt(&v[c1], &v[c2]) { c1 }
                 else { c2 };
        if cmp.compares_lt(&v[ch], &v[left]) {
            v.swap(ch, left);
            left = ch;
            let right = left + 1;
            if right < v.len() {
                if cmp.compares_gt(&v[left], &v[right]) { v.swap(left, right); }
            }
        } else {
            break;
        }
    }
}

/// The max element in the root node of an otherwise valid interval heap
/// has been been replaced with some other value without violating rule (1)
/// for the root node. This function restores the interval heap properties.
fn update_max<T, C: Compare<T>>(v: &mut [T], cmp: &C) {
    debug_assert!(cmp.compares_le(&v[0], &v[1]));
    // Starting at the root, we go down the tree...
    let mut right = 1;
    loop {
        let c1 = right * 2 + 1; // index of 1st child's right element
        let c2 = right * 2 + 3; // index of 2nd child's right element
        if v.len() <= c1 { return; } // No children. We're done.
        // Pick child with greatest max
        let ch = if v.len() <= c2 || cmp.compares_gt(&v[c1], &v[c2]) { c1 }
                 else { c2 };
        if cmp.compares_gt(&v[ch], &v[right]) {
            v.swap(ch, right);
            right = ch;
            let left = right - 1; // always exists
            if cmp.compares_gt(&v[left], &v[right]) { v.swap(left, right); }
        } else {
            break;
        }
    }
}

/// An `IntervalHeap` is an implementation of a double-ended priority queue.
/// As such, it supports the following operations: `push`, `get_min`,
/// `get_max`, `pop_min`, `pop_max` where insertion takes amortized O(log n)
/// time, removal takes O(log n) time and accessing minimum and maximum can
/// be done in constant time. Also, other convenient functions are provided
/// that handle conversion from and into vectors and allow iteration etc.
#[derive(Clone)]
pub struct IntervalHeap<T, C: Compare<T> = Natural<T>> {
    data: Vec<T>,
    cmp: C,
}

impl<T, C: Compare<T> + Default> Default for IntervalHeap<T, C> {
    /// Returns an empty heap ordered according to a default comparator.
    #[inline]
    fn default() -> IntervalHeap<T, C> {
        IntervalHeap::with_comparator(Default::default())
    }
}

/// `IntervalHeap` iterator.
pub struct Iter<'a, T: 'a>(slice::Iter<'a, T>);

impl<T: Ord> IntervalHeap<T> {
    /// Returns an empty heap ordered according to the natural order of its elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::IntervalHeap;
    ///
    /// let heap = IntervalHeap::<u32>::new();
    /// assert!(heap.is_empty());
    /// ```
    pub fn new() -> IntervalHeap<T> { IntervalHeap::with_comparator(Natural) }

    /// Returns an empty heap with the given capacity and ordered according to the
    /// natural order of its elements.
    ///
    /// The heap will be able to hold exactly `capacity` elements without reallocating.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::IntervalHeap;
    ///
    /// let heap = IntervalHeap::<u32>::with_capacity(5);
    /// assert!(heap.is_empty());
    /// assert!(heap.capacity() >= 5);
    /// ```
    pub fn with_capacity(capacity: uint) -> IntervalHeap<T> {
        IntervalHeap::with_capacity_and_comparator(capacity, Natural)
    }

    /// Returns a heap containing all the elements of the given vector and ordered
    /// according to the natural order of its elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::IntervalHeap;
    ///
    /// let heap = IntervalHeap::from_vec(vec![5u32, 1, 6, 4]);
    /// assert_eq!(heap.len(), 4);
    /// assert_eq!(heap.get_min_max(), Some((&1, &6)));
    /// ```
    pub fn from_vec(vec: Vec<T>) -> IntervalHeap<T> {
        IntervalHeap::from_vec_and_comparator(vec, Natural)
    }
}

impl<T, C: Compare<T>> IntervalHeap<T, C> {
    /// Returns an empty heap ordered according to the given comparator.
    pub fn with_comparator(cmp: C) -> IntervalHeap<T, C> {
        IntervalHeap { data: vec![], cmp: cmp }
    }

    /// Returns an empty heap with the given capacity and ordered according to the given
    /// comparator.
    pub fn with_capacity_and_comparator(capacity: uint, cmp: C) -> IntervalHeap<T, C> {
        IntervalHeap { data: Vec::with_capacity(capacity), cmp: cmp }
    }

    /// Returns a heap containing all the elements of the given vector and ordered
    /// according to the given comparator.
    pub fn from_vec_and_comparator(mut vec: Vec<T>, cmp: C) -> IntervalHeap<T, C> {
        for to in 2 .. vec.len() + 1 {
            interval_heap_push(vec.slice_to_mut(to), &cmp);
        }
        IntervalHeap { data: vec, cmp: cmp }
    }

    /// An iterator visiting all values in underlying vector,
    /// in arbitrary order.
    pub fn iter(&self) -> Iter<T> {
        Iter(self.data.iter())
    }

    /// Returns a reference to the smallest item or None (if empty).
    pub fn get_min(&self) -> Option<&T> {
        match self.data.len() {
            0 => None,
            _ => Some(&self.data[0])
        }
    }

    /// Returns a reference to the greatest item or None (if empty).
    pub fn get_max(&self) -> Option<&T> {
        match self.data.len() {
            0 => None,
            1 => Some(&self.data[0]),
            _ => Some(&self.data[1])
        }
    }

    /// Returns references to the smallest and greatest item or None (if empty).
    pub fn get_min_max(&self) -> Option<(&T, &T)> {
        match self.data.len() {
            0 => None,
            1 => Some((&self.data[0],&self.data[0])),
            _ => Some((&self.data[0],&self.data[1]))
        }
    }

    /// Returns the number of items the interval heap could hold
    /// without reallocation.
    pub fn capacity(&self) -> uint {
        self.data.capacity()
    }

    /// Reserves the minimum capacity for exactly `additional` more elements
    /// to be inserted in the given `IntervalHeap`. Does nothing if the capacity
    /// is already sufficient.
    ///
    /// Note that the allocator may give the collection more space than it
    /// requests. Therefore capacity can not be relied upon to be precisely
    /// minimal. Prefer `reserve` if future insertions are expected.
    pub fn reserve_exact(&mut self, additional: uint) {
        self.data.reserve_exact(additional);
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `IntervalHeap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    pub fn reserve(&mut self, additional: uint) {
        self.data.reserve(additional);
    }

    /// Discards as much additional capacity as possible.
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit()
    }

    /// Removes the smallest item and returns it, or None if is empty.
    pub fn pop_min(&mut self) -> Option<T> {
        match self.data.len() {
            0 => None,
            1...2 => Some(self.data.swap_remove(0)),
            _ => {
                let res = self.data.swap_remove(0);
                update_min(self.data.as_mut_slice(), &self.cmp);
                Some(res)
            }
        }
    }

    /// Removes the greatest item and returns it, or None if is empty.
    pub fn pop_max(&mut self) -> Option<T> {
        match self.data.len() {
            0...2 => self.data.pop(),
            _ => {
                let res = self.data.swap_remove(1);
                update_max(self.data.as_mut_slice(), &self.cmp);
                Some(res)
            }
        }
    }

    /// Pushes an item onto the queue.
    pub fn push(&mut self, x: T) {
        self.data.push(x);
        interval_heap_push(self.data.as_mut_slice(), &self.cmp);
    }

    /// Consumes the `IntervalHeap` and returns the underlying vector
    /// in arbitrary order.
    pub fn into_vec(self) -> Vec<T> { self.data }

    /// Consumes the `IntervalHeap` and returns a vector in sorted
    /// (ascending) order.
    pub fn into_sorted_vec(self) -> Vec<T> {
        let mut vec = self.data;
        for hsize in range(2, vec.len()).rev() {
            vec.swap(1, hsize);
            update_max(vec.slice_to_mut(hsize), &self.cmp);
        }
        vec
    }

    /// Returns the number of items in the interval heap
    pub fn len(&self) -> uint {
        self.data.len()
    }

    /// Returns true if the queue contains no items.
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// Drops all items from the queue.
    pub fn clear(&mut self) {
        self.data.clear();
    }
}

impl<T, C: Compare<T> + Default> FromIterator<T> for IntervalHeap<T, C> {
    /// Creates an interval heap with all the items from an iterator
    fn from_iter<Iter: Iterator<T>>(iter: Iter) -> IntervalHeap<T, C> {
        IntervalHeap::from_vec_and_comparator(iter.collect(), Default::default())
    }
}

impl<T, C: Compare<T>> Extend<T> for IntervalHeap<T, C> {
    /// Extends the interval heap by a new chunk of items given by
    /// an iterator.
    fn extend<Iter: Iterator<T>>(&mut self, mut iter: Iter) {
        let (lower, _) = iter.size_hint();
        self.reserve(lower);
        for elem in iter {
            self.push(elem);
        }
    }
}

impl<'a, T> Iterator<&'a T> for Iter<'a, T> {
    #[inline] fn next(&mut self) -> Option<&'a T> { self.0.next() }
    #[inline] fn size_hint(&self) -> (uint, Option<uint>) { self.0.size_hint() }
}

#[cfg(test)]
pub fn as_slice<T, C: Compare<T>>(x: &IntervalHeap<T, C>) -> &[T] {
    x.data.as_slice()
}

#[cfg(test)]
mod test {
    use std::rand::{ thread_rng, Rng };
    use super::{ IntervalHeap, as_slice };

    fn is_interval_heap<T: Ord>(x: &[T]) -> bool {
        if x.len() < 2 { return true; }
        if x[1] < x[0] { return false; }
        let mut ofs = 2;
        while ofs < x.len() {
            let ofz = ofs + (ofs + 1 < x.len()) as uint;
            if x[ofz] < x[ofs] { return false; }
            let parent = (ofs / 2 - 1) & !1u;
            if x[ofs] < x[parent] { return false; }
            if x[parent+1] < x[ofz] { return false; }
            ofs += 2;
        }
        true
    }

    #[test]
    fn fuzz_push_into_sorted_vec() {
        let mut rng = thread_rng();
        let mut tmp = Vec::with_capacity(100);
        for _ in range(0, 100u) {
            tmp.clear();
            let mut ih = IntervalHeap::from_vec(tmp);
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
                assert!(is_interval_heap(as_slice(&ih)));
            }
            tmp = ih.into_sorted_vec();
            for pair in tmp.windows(2) {
                assert!(pair[0] <= pair[1]);
            }
        }
    }

    #[test]
    fn fuzz_pop_min() {
        let mut rng = thread_rng();
        let mut tmp = Vec::with_capacity(100);
        for _ in range(0, 100u) {
            tmp.clear();
            let mut ih = IntervalHeap::from_vec(tmp);
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
            }
            let mut tmpx: Option<u32> = None;
            loop {
                let tmpy = ih.pop_min();
                assert!(is_interval_heap(as_slice(&ih)));
                match (tmpx, tmpy) {
                    (_, None) => break,
                    (Some(x), Some(y)) => assert!(x <= y),
                    _ => ()
                }
                tmpx = tmpy;
            }
            tmp = ih.into_vec();
        }
    }

    #[test]
    fn fuzz_pop_max() {
        let mut rng = thread_rng();
        let mut tmp = Vec::with_capacity(100);
        for _ in range(0, 100u) {
            tmp.clear();
            let mut ih = IntervalHeap::from_vec(tmp);
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
            }
            let mut tmpx: Option<u32> = None;
            loop {
                let tmpy = ih.pop_max();
                assert!(is_interval_heap(as_slice(&ih)));
                match (tmpx, tmpy) {
                    (_, None) => break,
                    (Some(x), Some(y)) => assert!(x >= y),
                    _ => ()
                }
                tmpx = tmpy;
            }
            tmp = ih.into_vec();
        }
    }

    #[test]
    fn test_from_vec() {
        let heap = IntervalHeap::<u32>::from_vec(vec![]);
        assert_eq!(heap.get_min_max(), None);

        let heap = IntervalHeap::<u32>::from_vec(vec![2]);
        assert_eq!(heap.get_min_max(), Some((&2, &2)));

        let heap = IntervalHeap::<u32>::from_vec(vec![2, 1]);
        assert_eq!(heap.get_min_max(), Some((&1, &2)));

        let heap = IntervalHeap::<u32>::from_vec(vec![2, 1, 3]);
        assert_eq!(heap.get_min_max(), Some((&1, &3)));
    }
} // mod test

