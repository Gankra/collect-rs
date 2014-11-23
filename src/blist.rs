use std::collections::{dlist, ring_buf, DList, RingBuf};
use std::iter;
use std::fmt;
use std::hash::{Hash, Writer};

#[deriving(Clone)]
/// A BList is a hybrid between an array and a doubly-linked-list. It consists of arrays in a
/// doubly-linked-list. In this way we get many of the nice properties of a DList, but with
/// improved cache properties and less allocations.
///
/// A BList's B-factor is analgous to the same factor in a BTree. It guarantees that all nodes
/// contain B-1 and B+1 elements (except the ends). Once a position has been identified to
/// perform an insertion or deletion, it will take amortized O(B) time to perform, with a
/// worst-case cost of O(B^2). Insertion and deletion on either end will always take
/// O(1) time, though (assuming it takes O(1) time to allocate an array of size B).
pub struct BList<T> {
    list: DList<RingBuf<T>>,
    b: uint,
    len: uint,
}

// Constructors
impl<T> BList<T> {
    /// Creates a new BList with a reasonable choice for B.
    pub fn new() -> BList<T> {
        BList::with_b(7)
    }

    /// Creates a new BList with the specified B.
    pub fn with_b(b: uint) -> BList<T> {
        assert!(b > 1, "B must be > 1");
        BList {
            list: DList::new(),
            b: b,
            len: 0,
        }
    }
}

// Methods
impl<T> BList<T> {
    /// Inserts the element at the back of the list.
    pub fn push_back(&mut self, elem: T) {
        self.len += 1;

        let max = self.block_max();
        if let Some(block) = self.list.back_mut() {
            if block.len() < max {
                block.push_back(elem);
                return;
            }
        }

        // Couldn't insert, gotta make a new back
        let mut new_block = self.make_block();
        new_block.push_back(elem);
        self.list.push_back(new_block);
    }

    /// Inserts the element at the front of the list.
    pub fn push_front(&mut self, elem: T) {
        self.len += 1;

        let max = self.block_max();
        if let Some(block) = self.list.front_mut() {
            if block.len() < max {
                block.push_front(elem);
                return;
            }
        }

        // Couldn't insert, gotta make a new front
        let mut new_block = self.make_block();
        new_block.push_front(elem);
        self.list.push_front(new_block);
    }

    /// Removes and returns an element off the back of the list. Returns None if empty.
    pub fn pop_back(&mut self) -> Option<T> {
        let (result, should_pop) = match self.list.back_mut() {
            None => (None, false),
            Some(block) => (block.pop_back(), block.is_empty()),
        };

        if should_pop {
            self.list.pop_back();
        }

        if result.is_some() {
            self.len -= 1;
        }

        result
    }

    /// Removes and returns an element off the front of the list. Returns None if empty.
    pub fn pop_front(&mut self) -> Option<T> {
        let (result, should_pop) = match self.list.front_mut() {
            None => (None, false),
            Some(block) => (block.pop_front(), block.is_empty()),
        };

        if should_pop {
            self.list.pop_front();
        }

        if result.is_some() {
            self.len -= 1;
        }

        result
    }

    /// Gets an immutable reference to the first element in the list.
    pub fn front(&self) -> Option<&T> {
        self.list.front().and_then(|block| block.front())
    }

    /// Gets an immutable reference to the last element in the list.
    pub fn back(&self) -> Option<&T> {
        self.list.back().and_then(|block| block.back())
    }

    /// Gets a mutable reference to the first element in the list.
    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.list.front_mut().and_then(|block| block.front_mut())
    }

    /// Gets a mutable reference to the last element in the list.
    pub fn back_mut(&mut self) -> Option<&mut T> {
        self.list.back_mut().and_then(|block| block.back_mut())
    }

    /// Gets the number of elements in the list.
    pub fn len(&self) -> uint {
        self.len
    }

    /// Returns `true` if the list contains no elements, or `false` otherwise.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Gets a by-reference iterator over the elements in the list.
    pub fn iter(&self) -> Items<T> {
        let len = self.len();
        AbsItems {
            list_iter: self.list.iter(),
            right_block_iter: None,
            left_block_iter: None,
            len: len,
        }
    }

    /// Gets a by-mutable-reference iterator over the elements in the list.
    pub fn iter_mut(&mut self) -> MutItems<T> {
        let len = self.len();
        AbsItems {
            list_iter: self.list.iter_mut(),
            right_block_iter: None,
            left_block_iter: None,
            len: len,
        }
    }

    /* FIXME: uncomment into_iter stuff when RingBuf gets into_iter
    /// Gets a by-value iterator over the elements in the list.
    pub fn into_iter(self) -> MoveItems<T> {
        let len = self.len();
        AbsItems {
            list_iter: self.list.into_iter(),
            right_block_iter: None,
            left_block_iter: None,
            len: len,
        }
    }*/
}

// Privates
impl<T> BList<T> {
    /// Makes a new block for insertion in the list.
    fn make_block(&self) -> RingBuf<T> {
         RingBuf::with_capacity(self.block_max())
    }

    /// Gets the largest a block is allowed to become.
    fn block_max(&self) -> uint {
        self.b + 1
    }

    /// Gets the smallest a (non-end) block is allowed to become.
    #[allow(unused)]
    fn block_min(&self) -> uint {
        self.b - 1
    }
}

/// Abstracts over getting the appropriate iterator from a T, &T, or &mut T
trait Traverse<I> {
    fn traverse(self) -> I;
}

impl<'a, T> Traverse<ring_buf::Items<'a, T>> for &'a RingBuf<T> {
    fn traverse(self) -> ring_buf::Items<'a, T> { self.iter() }
}

impl<'a, T> Traverse<ring_buf::MutItems<'a, T>> for &'a mut RingBuf<T> {
    fn traverse(self) -> ring_buf::MutItems<'a, T> { self.iter_mut() }
}

/*
impl<T> Traverse<ring_buf::MoveItems<T>> for RingBuf<T> {
    fn traverse(self) -> ring_buf::MoveItems<T> { self.into_iter() }
}
*/

/// A by-ref iterator for a BList
pub type Items<'a, T> = AbsItems<dlist::Items<'a, RingBuf<T>>, ring_buf::Items<'a, T>>;
/// A by-mut-ref iterator for a BList
pub type MutItems<'a, T> = AbsItems<dlist::MutItems<'a, RingBuf<T>>, ring_buf::MutItems<'a, T>>;
// A by-value iterator for a BList
//pub type MoveItems<T> = AbsItems<dlist::MoveItems<RingBuf<T>>, ring_buf::MoveItems<T>>;

/// An iterator that abstracts over all three kinds of ownership for a BList
struct AbsItems<DListIter, RingBufIter> {
    list_iter: DListIter,
    left_block_iter: Option<RingBufIter>,
    right_block_iter: Option<RingBufIter>,
    len: uint,
}

impl<A,
    RingBufIter: Iterator<A>,
    DListIter: Iterator<T>,
    T: Traverse<RingBufIter>> Iterator<A> for AbsItems<DListIter, RingBufIter> {
    // I would like to thank all my friends and the fact that Iterator::next doesn't
    // borrow self, for this passing borrowck with minimal gymnastics
    fn next(&mut self) -> Option<A> {
        if self.len > 0 { self.len -= 1; }
        // Keep loopin' till we hit gold
        loop {
            // Try to read off the left iterator
            let (ret, iter) = match self.left_block_iter.as_mut() {
                // No left iterator, try to get one from the list iterator
                None => match self.list_iter.next() {
                    // No blocks left in the list, use the right iterator
                    None => match self.right_block_iter.as_mut() {
                        // Truly exhausted
                        None => return None,
                        // Got right iter; don't care about fixing right_block in forward iteration
                        Some(iter) => return iter.next(),
                    },
                    // Got new block from list iterator, make it the new left iterator
                    Some(block) => {
                        let mut next_iter = block.traverse();
                        let next = next_iter.next();
                        (next, Some(next_iter))
                    },
                },
                Some(iter) => match iter.next() {
                    // None out the iterator so we ask for a new one, or go to the right
                    None => (None, None),
                    Some(next) => return Some(next),
                },
            };

            // If we got here, we want to change what left_block_iter is, so do that
            // Also, if we got a return value, return that. Otherwise, just loop until we do.
            self.left_block_iter = iter;
            if ret.is_some() {
                return ret;
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        (self.len, Some(self.len))
    }
}

impl<A,
    RingBufIter: DoubleEndedIterator<A>,
    DListIter: DoubleEndedIterator<T>,
    T: Traverse<RingBufIter>> DoubleEndedIterator<A> for AbsItems<DListIter, RingBufIter> {
    // see `next` for details. This should be an exact mirror.
    fn next_back(&mut self) -> Option<A> {
        if self.len > 0 { self.len -= 1; }
        loop {
            let (ret, iter) = match self.right_block_iter.as_mut() {
                None => match self.list_iter.next_back() {
                    None => match self.left_block_iter.as_mut() {
                        None => return None,
                        Some(iter) => return iter.next_back(),
                    },
                    Some(block) => {
                        let mut next_iter = block.traverse();
                        let next = next_iter.next_back();
                        (next, Some(next_iter))
                    },
                },
                Some(iter) => match iter.next_back() {
                    None => (None, None),
                    Some(next) => return Some(next),
                },
            };

            self.right_block_iter = iter;
            if ret.is_some() {
                return ret;
            }
        }
    }
}

impl<A,
    RingBufIter: ExactSize<A>,
    DListIter: ExactSize<T>,
    T: Traverse<RingBufIter>> ExactSize<A> for AbsItems<DListIter, RingBufIter> { }

impl<A> FromIterator<A> for BList<A> {
    fn from_iter<T: Iterator<A>>(iterator: T) -> BList<A> {
        let mut ret = BList::new();
        ret.extend(iterator);
        ret
    }
}

impl<A> Extend<A> for BList<A> {
    fn extend<T: Iterator<A>>(&mut self, mut iterator: T) {
        for elt in iterator { self.push_back(elt); }
    }
}

impl<A: PartialEq> PartialEq for BList<A> {
    fn eq(&self, other: &BList<A>) -> bool {
        self.len() == other.len() &&
            iter::order::eq(self.iter(), other.iter())
    }

    fn ne(&self, other: &BList<A>) -> bool {
        self.len() != other.len() ||
            iter::order::ne(self.iter(), other.iter())
    }
}

impl<A: Eq> Eq for BList<A> {}

impl<A: PartialOrd> PartialOrd for BList<A> {
    fn partial_cmp(&self, other: &BList<A>) -> Option<Ordering> {
        iter::order::partial_cmp(self.iter(), other.iter())
    }
}

impl<A: Ord> Ord for BList<A> {
    #[inline]
    fn cmp(&self, other: &BList<A>) -> Ordering {
        iter::order::cmp(self.iter(), other.iter())
    }
}

impl<A: fmt::Show> fmt::Show for BList<A> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f, "["));

        for (i, e) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{}", *e));
        }

        write!(f, "]")
    }
}

impl<S: Writer, A: Hash<S>> Hash<S> for BList<A> {
    fn hash(&self, state: &mut S) {
        self.len().hash(state);
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}



#[cfg(test)]
mod test {
    use super::BList;
    use std::hash;

    fn generate_test() -> BList<int> {
        list_from(&[0i,1,2,3,4,5,6])
    }

    fn list_from<T: Clone>(v: &[T]) -> BList<T> {
        v.iter().map(|x| (*x).clone()).collect()
    }

    #[test]
    fn test_basic() {
        let mut m: BList<Box<int>> = BList::new();
        assert_eq!(m.pop_front(), None);
        assert_eq!(m.pop_back(), None);
        assert_eq!(m.pop_front(), None);
        m.push_front(box 1);
        assert_eq!(m.pop_front(), Some(box 1));
        m.push_back(box 2);
        m.push_back(box 3);
        assert_eq!(m.len(), 2);
        assert_eq!(m.pop_front(), Some(box 2));
        assert_eq!(m.pop_front(), Some(box 3));
        assert_eq!(m.len(), 0);
        assert_eq!(m.pop_front(), None);
        m.push_back(box 1);
        m.push_back(box 3);
        m.push_back(box 5);
        m.push_back(box 7);
        assert_eq!(m.pop_front(), Some(box 1));

        let mut n = BList::new();
        n.push_front(2i);
        n.push_front(3);
        {
            assert_eq!(n.front().unwrap(), &3);
            let x = n.front_mut().unwrap();
            assert_eq!(*x, 3);
            *x = 0;
        }
        {
            assert_eq!(n.back().unwrap(), &2);
            let y = n.back_mut().unwrap();
            assert_eq!(*y, 2);
            *y = 1;
        }
        assert_eq!(n.pop_front(), Some(0));
        assert_eq!(n.pop_front(), Some(1));
    }

    #[test]
    fn test_iterator() {
        let m = generate_test();
        for (i, elt) in m.iter().enumerate() {
            assert_eq!(i as int, *elt);
        }
        let mut n = BList::new();
        assert_eq!(n.iter().next(), None);
        n.push_front(4i);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }


    #[test]
    fn test_iterator_double_end() {
        let mut n = BList::new();
        assert_eq!(n.iter().next(), None);
        n.push_front(4i);
        n.push_front(5);
        n.push_front(6);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(it.next().unwrap(), &6);
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(it.next_back().unwrap(), &4);
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next_back().unwrap(), &5);
        assert_eq!(it.next_back(), None);
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_rev_iter() {
        let m = generate_test();
        for (i, elt) in m.iter().rev().enumerate() {
            assert_eq!((6 - i) as int, *elt);
        }
        let mut n = BList::new();
        assert_eq!(n.iter().rev().next(), None);
        n.push_front(4i);
        let mut it = n.iter().rev();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_mut_iter() {
        let mut m = generate_test();
        let mut len = m.len();
        for (i, elt) in m.iter_mut().enumerate() {
            assert_eq!(i as int, *elt);
            len -= 1;
        }
        assert_eq!(len, 0);
        let mut n = BList::new();
        assert!(n.iter_mut().next().is_none());
        n.push_front(4i);
        n.push_back(5);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert!(it.next().is_some());
        assert!(it.next().is_some());
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert!(it.next().is_none());
    }

    #[test]
    fn test_iterator_mut_double_end() {
        let mut n = BList::new();
        assert!(n.iter_mut().next_back().is_none());
        n.push_front(4i);
        n.push_front(5);
        n.push_front(6);
        let mut it = n.iter_mut();
        assert_eq!(it.size_hint(), (3, Some(3)));
        assert_eq!(*it.next().unwrap(), 6);
        assert_eq!(it.size_hint(), (2, Some(2)));
        assert_eq!(*it.next_back().unwrap(), 4);
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(*it.next_back().unwrap(), 5);
        assert!(it.next_back().is_none());
        assert!(it.next().is_none());
    }

    #[test]
    fn test_eq() {
        let mut n: BList<u8> = list_from(&[]);
        let mut m = list_from(&[]);
        assert!(n == m);
        n.push_front(1);
        assert!(n != m);
        m.push_back(1);
        assert!(n == m);

        let n = list_from(&[2i,3,4]);
        let m = list_from(&[1i,2,3]);
        assert!(n != m);
    }

    #[test]
    fn test_hash() {
      let mut x = BList::new();
      let mut y = BList::new();

      assert!(hash::hash(&x) == hash::hash(&y));

      x.push_back(1i);
      x.push_back(2);
      x.push_back(3);

      y.push_front(3i);
      y.push_front(2);
      y.push_front(1);

      assert!(hash::hash(&x) == hash::hash(&y));
    }

    #[test]
    fn test_ord() {
        let n: BList<int> = list_from(&[]);
        let m = list_from(&[1i,2,3]);
        assert!(n < m);
        assert!(m > n);
        assert!(n <= n);
        assert!(n >= n);
    }

    #[test]
    fn test_ord_nan() {
        let nan = 0.0f64/0.0;
        let n = list_from(&[nan]);
        let m = list_from(&[nan]);
        assert!(!(n < m));
        assert!(!(n > m));
        assert!(!(n <= m));
        assert!(!(n >= m));

        let n = list_from(&[nan]);
        let one = list_from(&[1.0f64]);
        assert!(!(n < one));
        assert!(!(n > one));
        assert!(!(n <= one));
        assert!(!(n >= one));

        let u = list_from(&[1.0f64,2.0,nan]);
        let v = list_from(&[1.0f64,2.0,3.0]);
        assert!(!(u < v));
        assert!(!(u > v));
        assert!(!(u <= v));
        assert!(!(u >= v));

        let s = list_from(&[1.0f64,2.0,4.0,2.0]);
        let t = list_from(&[1.0f64,2.0,3.0,2.0]);
        assert!(!(s < t));
        assert!(s > one);
        assert!(!(s <= one));
        assert!(s >= one);
    }

    #[test]
    fn test_show() {
        let list: BList<int> = range(0i, 10).collect();
        assert!(list.to_string().as_slice() == "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: BList<&str> = vec!["just", "one", "test", "more"].iter()
                                                                   .map(|&s| s)
                                                                   .collect();
        assert!(list.to_string().as_slice() == "[just, one, test, more]");
    }
}

#[cfg(test)]
mod bench{
    use super::BList;
    use test;

    #[bench]
    fn bench_collect_into(b: &mut test::Bencher) {
        let v = &[0i, ..64];
        b.iter(|| {
            let _: BList<int> = v.iter().map(|x| *x).collect();
        })
    }

    #[bench]
    fn bench_push_front(b: &mut test::Bencher) {
        let mut m: BList<int> = BList::new();
        b.iter(|| {
            m.push_front(0);
        })
    }

    #[bench]
    fn bench_push_back(b: &mut test::Bencher) {
        let mut m: BList<int> = BList::new();
        b.iter(|| {
            m.push_back(0);
        })
    }

    #[bench]
    fn bench_push_back_pop_back(b: &mut test::Bencher) {
        let mut m: BList<int> = BList::new();
        b.iter(|| {
            m.push_back(0);
            m.pop_back();
        })
    }

    #[bench]
    fn bench_push_front_pop_front(b: &mut test::Bencher) {
        let mut m: BList<int> = BList::new();
        b.iter(|| {
            m.push_front(0);
            m.pop_front();
        })
    }

    #[bench]
    fn bench_iter(b: &mut test::Bencher) {
        let v = &[0i, ..128];
        let m: BList<int> = v.iter().map(|&x|x).collect();
        b.iter(|| {
            assert!(m.iter().count() == 128);
        })
    }
    #[bench]
    fn bench_iter_mut(b: &mut test::Bencher) {
        let v = &[0i, ..128];
        let mut m: BList<int> = v.iter().map(|&x|x).collect();
        b.iter(|| {
            assert!(m.iter_mut().count() == 128);
        })
    }
    #[bench]
    fn bench_iter_rev(b: &mut test::Bencher) {
        let v = &[0i, ..128];
        let m: BList<int> = v.iter().map(|&x|x).collect();
        b.iter(|| {
            assert!(m.iter().rev().count() == 128);
        })
    }
    #[bench]
    fn bench_iter_mut_rev(b: &mut test::Bencher) {
        let v = &[0i, ..128];
        let mut m: BList<int> = v.iter().map(|&x|x).collect();
        b.iter(|| {
            assert!(m.iter_mut().rev().count() == 128);
        })
    }
}