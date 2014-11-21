//! This module contains the implementation of an interval heap data structure.

use std::mem;
use std::vec;

// Interval Heap:
// --------------
// (1) each node (except possibly the last leaf) contains two values
//     where the first one is less than or equal to the second one
// (2) each node represents a closed interval
// (3) a child node's interval is completely contained in the parent node's
//     interval


// item indices...
//
//          (0 1)
//         /     \
//    (2 3)       (4 5)
//    /   \       /    \
//  (6 7)(8 9)(10 11)(12 13)
//  ........................


// v[x] for x in [0,len-1) is considered a valid interval heap.
// The last item in v is to be added.
fn inteval_heap_push<T: Ord>(v: &mut [T]) {
    debug_assert!(v.len() > 0);
    let mut node_r = v.len() - 1;
    let mut node_l = node_r & !1u;
    if v[node_l] > v[node_r] { v.swap(node_l, node_r); }
    while node_l > 0 {
        let parent_l = (node_l / 2 - 1) & !1u;
        let parent_r = parent_l + 1;
        if v[node_l] < v[parent_l] {
            v.swap(parent_l, node_l);
        } else if v[parent_r] < v[node_r] {
            v.swap(parent_r, node_r);
        } else {
            return; // nothing to do anymore
        }
        debug_assert!(!(v[node_r] < v[node_l]));
        node_l = parent_l;
        node_r = parent_r;
    }
}

// pushes item v[index] down the tree as needed
// to restore interval heap properties
fn down_min<T: Ord>(v: &mut [T], mut index: uint) {
    debug_assert!(index & 1 == 0);
    loop {
        let c1 = index * 2 + 2;
        let c2 = index * 2 + 4;
        if v.len() <= c1 { return; }
        // which path to go down in the tree?
        let ch = if v.len() <= c2 {
                     c1 // c1 is the only child
                 } else {
                     if v[c1] < v[c2] { c1 } else { c2 }
                 };
        if v[ch] < v[index] {
            v.swap(ch, index);
            index = ch;
            let right = index + 1;
            if right < v.len() {
                if v[index] > v[right] { v.swap(index, right); }
            }
        } else {
            break;
        }
    }
}

// pushes item v[index] down the tree as needed
// to restore interval heap properties
fn down_max<T: Ord>(v: &mut [T], mut index: uint) {
    debug_assert!(index & 1 == 1);
    loop {
        let c1 = index * 2 + 1;
        let c2 = index * 2 + 3;
        if v.len() <= c1 { return; }
        // which path to go down in the tree?
        let ch = if v.len() <= c2 {
                     c1 // c1 is the only child
                 } else {
                     if v[c1] > v[c2] { c1 } else { c2 }
                 };
        if v[ch] > v[index] {
            v.swap(ch, index);
            index = ch;
            let left = index - 1;
            if v[left] > v[index] { v.swap(left, index); }
        } else {
            break;
        }
    }
}

// replaces and element and propagates the new one down the tree
fn replace_and_down<T: Ord>(v: &mut [T], index: uint, x: T) -> T {
    let res = mem::replace(&mut v[index], x);
    if index & 1 == 0 { down_min(v, index); }
    else { down_max(v, index); }
    res
}

/// An `IntervalHeap` is an implementation of a double-ended priority queue.
/// As such, it supports the following operations: `push`, `get_min`,
/// `get_max`, `pop_min`, `pop_max` where insertion takes amortized O(log n)
/// time, removal takes O(log n) time and accessing minimum and maximum can
/// be done in constant time. Also, other convenient functions are provided
/// that handle conversion from and into vectors and allow iteration etc.
#[deriving(Clone)]
pub struct IntervalHeap<T> {
    data: Vec<T>
}

pub type MoveItems<T> = vec::MoveItems<T>;

impl<T> IntervalHeap<T> {
    /// creates empty interval heap
    pub fn new() -> IntervalHeap<T> {
        IntervalHeap { data: Vec::new() }
    }
    /// creates empty interval heap with a user-defined initial capacity
    /// which causes insertions not to reallocate memory if the capacity
    /// is sufficient to hold the new items.
    pub fn with_capacity(c: uint) -> IntervalHeap<T> {
        IntervalHeap { data: Vec::with_capacity(c) }
    }
    /// returns true if the queue contains no items
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }
    /// drops all items from the queue
    pub fn clear(&mut self) {
        self.data.clear();
    }
    /// converts the interval heap into a vector (constant time complexity)
    pub fn into_vec(self) -> Vec<T> {
        self.data
    }
    /// converts the interval heap into an iterator
    pub fn into_iter(self) -> MoveItems<T> {
        self.data.into_iter()
    }
    /// returns the number of items in the interval heap
    pub fn len(&self) -> uint {
        self.data.len()
    }
    /// returns the number of items the interval heap could hold
    /// without any memory reallocation
    pub fn capacity(&self) -> uint {
        self.data.capacity()
    }
    /// reserves capacity for at least `additional` more elements to be
    /// inserted in the `IntervalHeap`. The collection may reserve more
    /// space to avoid frequent reallocations.
    pub fn reserve(&mut self, additional: uint) {
        self.data.reserve(additional);
    }
    /// discards as much additional capacity as possible.
    pub fn shrink_to_fit(&mut self) {
        self.data.shrink_to_fit()
    }
    /// provides read-access to all the items.
    pub fn as_slice(&self) -> &[T] {
        self.data.as_slice()
    }
    /// returns a reference to the minimal item or None (if empty)
    pub fn get_min<'a>(&'a self) -> Option<&'a T> {
        match self.data.len() {
            0 => None,
            _ => Some(&self.data[0])
        }
    }
    /// returns a reference to the maximum item or None (if empty)
    pub fn get_max<'a>(&'a self) -> Option<&'a T> {
        match self.data.len() {
            0 => None,
            1 => Some(&self.data[0]),
            _ => Some(&self.data[1])
        }
    }
    /// returns a reference to the minimal and maximum item or None (if empty)
    pub fn get_min_max<'a>(&'a self) -> Option<(&'a T, &'a T)> {
        match self.data.len() {
            0 => None,
            1 => Some((&self.data[0],&self.data[0])),
            _ => Some((&self.data[0],&self.data[1]))
        }
    }
}

impl<T: Ord> IntervalHeap<T> {
    /// converts a vector into an interval heap in-place. No memory
    /// allocation will be done. The time complexity is O(n log n) and
    /// O(n) in case the vector already represents an interval heap.
    pub fn from_vec(mut v: Vec<T>) -> IntervalHeap<T> {
        for to in range(2, v.len()) {
            inteval_heap_push(v.slice_to_mut(to));
        }
        IntervalHeap { data: v }
    }
    /// inserts a new item into the queue, takes amortized
    /// logarithmic time in the size of the heap
    pub fn push(&mut self, x: T) {
        self.data.push(x);
        inteval_heap_push(self.data.as_mut_slice());
    }
    /// pushes a new element into the interval heap and immediately
    /// pops the minimum (possibly returning the new element).
    /// This is expected to be a little more efficient than separate
    /// calls to `push` and `pop_min`. So, no matter
    /// what, the size of the heap will not change.
    pub fn push_and_pop_min(&mut self, x: T) -> T {
        match self.data.len() {
            0 => x,
            _ => if self.data[0] >= x { x }
                 else { replace_and_down(self.data.as_mut_slice(), 0, x) }
        }
    }
    /// pushes a new element into the interval heap and immediately
    /// pops the maximum (possibly returning the new element).
    /// This is expected to be a little more efficient than separate
    /// calls to `push` and `pop_max`. So, no matter
    /// what, the size of the heap will not change.
    pub fn push_and_pop_max(&mut self, x: T) -> T {
        match self.data.len() {
            0 => x,
            l => {
                let index = if l==1 { 0u } else { 1u };
                replace_and_down(self.data.as_mut_slice(), index, x)
            }
        }
    }
    /// replaces the minimum item with the given `x`. If the heap is
    /// empty, this function will return `Err(x)`. If the heap is
    /// not empty, the function returns `Ok(old_min)`. So, no matter
    /// what, the size of the heap will not change.
    pub fn replace_min(&mut self, x: T) -> Result<T,T> {
        match self.data.len() {
            0 => Err(x),
            _ => Ok(replace_and_down(self.data.as_mut_slice(), 0, x))
        }
    }
    /// replaces the maximum item with the given `x`. If the heap is
    /// empty, this function will return `Err(x)`. If the heap is
    /// not empty, the function returns `Ok(old_min)`. So, no matter
    /// what, the size of the heap will not change.
    pub fn replace_max(&mut self, x: T) -> Result<T,T> {
        match self.data.len() {
            0 => Err(x),
            1 => Ok(mem::replace(&mut self.data[0], x)),
            _ => Ok(replace_and_down(self.data.as_mut_slice(), 1, x))
        }
    }
    /// removes the minimum item and returns it (or None if empty),
    /// takes logarithmic time in the size of the heap
    pub fn pop_min(&mut self) -> Option<T> {
        match self.data.len() {
            0 => None,
            1...2 => self.data.swap_remove(0),
            _ => { // length 3 or higher
                let res = self.data.swap_remove(0);
                down_min(self.data.as_mut_slice(), 0);
                res
            }
        }
    }
    /// removes the maximum item and returns it (or None if empty),
    /// takes logarithmic time in the size of the heap
    pub fn pop_max(&mut self) -> Option<T> {
        match self.data.len() {
            0 => None,
            1...2 => self.data.pop(),
            _ => { // length 3 or higher
                let res = self.data.swap_remove(1);
                down_max(self.data.as_mut_slice(), 1);
                res
            }
        }
    }
}

impl<T> Deref<[T]> for IntervalHeap<T> {
    /// allows all the immutable slice methods on the interval heap
    fn deref(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T: Ord> FromIterator<T> for IntervalHeap<T> {
    /// creates an interval heap with all the items from an iterator
    fn from_iter<Iter: Iterator<T>>(mut iter: Iter) -> IntervalHeap<T> {
        let vec: Vec<T> = iter.collect();
        IntervalHeap::from_vec(vec)
    }
}

impl<T: Ord> Extend<T> for IntervalHeap<T> {
    /// extends the interval heap by a new chunk of items given by
    /// an iterator.
    fn extend<Iter: Iterator<T>>(&mut self, mut iter: Iter) {
        let (lower, _) = iter.size_hint();
        self.reserve(lower);
        for elem in iter {
            self.push(elem);
        }
    }
}

#[cfg(test)]
mod ih_test {
    use std::rand::{task_rng, Rng};
    use super::IntervalHeap;

    // TODO: more testing (push_and_pop_xxx, replace_xxx)

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
    fn random_check_push() {
        let mut rng = task_rng();
        for _ in range(0, 1000u) {
            let mut ih: IntervalHeap<u32> = IntervalHeap::new();
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
                assert!(is_interval_heap(ih.as_slice()));
            }
        }
    }

    #[test]
    fn random_check_pop_min() {
        let mut rng = task_rng();
        for _ in range(0, 1000u) {
            let mut ih: IntervalHeap<u32> = IntervalHeap::new();
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
            }
            let mut tmpx: Option<u32> = None;
            loop {
                let tmpy = ih.pop_min();
                assert!(is_interval_heap(ih.as_slice()));
                match (tmpx, tmpy) {
                    (_, None) => break,
                    (Some(x), Some(y)) => assert!(x <= y),
                    _ => ()
                }
                tmpx = tmpy;
            }
        }
    }

    #[test]
    fn random_check_pop_max() {
        let mut rng = task_rng();
        for _ in range(0, 1000u) {
            let mut ih: IntervalHeap<u32> = IntervalHeap::new();
            for _ in range(0, 100u) {
                ih.push(rng.next_u32());
            }
            let mut tmpx: Option<u32> = None;
            loop {
                let tmpy = ih.pop_max();
                assert!(is_interval_heap(ih.as_slice()));
                match (tmpx, tmpy) {
                    (_, None) => break,
                    (Some(x), Some(y)) => assert!(x >= y),
                    _ => ()
                }
                tmpx = tmpy;
            }
        }
    }

} // mod test

