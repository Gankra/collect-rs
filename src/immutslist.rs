use std::rc::{try_unwrap, Rc};
use std::hash::{Writer, Hash};
use std;

struct Node<T> {
    elem: T,
    next: Option<Rc<Node<T>>>,
}

impl<T> Node<T> {
    fn new(elem: T) -> Node<T> {
        Node { elem: elem, next: None }
    }
}

/// An iterator over the items of an ImmutSList
pub struct Items<'a, T: 'a> {
    head: Option<&'a Node<T>>,
    nelem: uint,
}

/// An immutable singly-linked list, as seen in basically every functional language
pub struct ImmutSList<T> {
    front: Option<Rc<Node<T>>>,
    length: uint,
}

impl<T> ImmutSList<T> {
    /// Constructs a new, empty `ImmutSList`
    pub fn new () -> ImmutSList<T> {
        ImmutSList{ front: None, length: 0 }
    }

    /// Returns a copy of the list, with `elem` appended to the front
    pub fn append (&self, elem: T) -> ImmutSList<T>{
        let mut new_node = Node::new(elem);
        new_node.next = self.front.clone();

        ImmutSList{
            front: Some(Rc::new(new_node)),
            length: self.len() + 1,
        }
    }

    /// Returns a reference to the first element in the list
    pub fn head (&self) -> Option<&T> {
        self.front.as_ref().map(|node| &node.elem)
    }

    /// Returns a copy of the list, with the first element removed
    pub fn tail (&self) -> ImmutSList<T> {
        self.tailn(1)
    }

    /// Returns a copy of the list, with the first `n` elements removed
    pub fn tailn (&self, n: uint) -> ImmutSList<T> {
        if self.len() <= n {
            ImmutSList::new()
        } else {
            let len = self.len() - n;
            let mut head = self.front.as_ref();
            for _ in range(0, n) {
                head = head.unwrap().next.as_ref();
            }
            ImmutSList {
                front: Some(head.unwrap().clone()),
                length: len,
            }
        }
    }

    /// Returns the last element in the list
    pub fn last (&self) -> Option<&T> {
        self.iter().last()
    }

    /// Returns a copy of the list, with only the last `n` elements remaining
    pub fn lastn (&self, n: uint) -> ImmutSList<T> {
        if n >= self.length {
            self.clone()
        } else {
            self.tailn(self.length - n)
        }

    }

    /// Returns an iterator over references to the elements of the list in order
    pub fn iter <'a> (&'a self) -> Items<'a, T> {
        Items{ head: self.front.as_ref().map(|x| &**x), nelem: self.len() }
    }

    pub fn len (&self) -> uint {
        self.length
    }

    pub fn is_empty(&self) -> bool {
        return self.len() == 0
    }
}

#[unsafe_destructor]
impl<T> Drop for ImmutSList<T> {
    fn drop (&mut self) {
        // don't want to blow the stack with destructors,
        // but also don't want to walk the whole list.
        // So walk the list until we find a non-uniquely owned item
        let mut head = self.front.take();
        loop {
            let temp = head;
            match temp {
                Some(node) => match try_unwrap(node) {
                    Ok(mut node) => {
                        head = node.next.take();
                    }
                    _ => return,
                },
                _ => return,
            }
        }
    }
}


impl<'a, T> Iterator<&'a T> for Items<'a, T> {
    fn next(&mut self) -> Option<&'a T> {
        match self.head.take() {
            None => None,
            Some(head) => {
                self.nelem -= 1;
                self.head = head.next.as_ref().map(|next| &**next);
                Some(&head.elem)
            }
        }
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        (self.nelem, Some(self.nelem))
    }
}

impl<'a, T> Clone for Items<'a, T> {
    fn clone(&self) -> Items<'a, T> { *self }
}

impl<T> FromIterator<T> for ImmutSList<T> {
    fn from_iter<I: Iterator<T>>(mut iterator: I) -> ImmutSList<T> {
        let mut list = ImmutSList::new();
        for elem in iterator {
            list = list.append(elem);
        }
        list
    }
}

impl<T: PartialEq> PartialEq for ImmutSList<T> {
    fn eq(&self, other: &ImmutSList<T>) -> bool {
        self.len() == other.len() &&
            std::iter::order::eq(self.iter(), other.iter())
    }

    fn ne(&self, other: &ImmutSList<T>) -> bool {
        self.len() != other.len() ||
            std::iter::order::ne(self.iter(), other.iter())
    }
}

impl<T: PartialOrd> PartialOrd for ImmutSList<T> {
    fn partial_cmp(&self, other: &ImmutSList<T>) -> Option<Ordering> {
        std::iter::order::partial_cmp(self.iter(), other.iter())
    }
}

impl <T> Clone for ImmutSList<T> {
    fn clone(&self) -> ImmutSList<T> {
        ImmutSList {
            front: self.front.clone(),
            length: self.length,
        }
    }
}

impl<T: std::fmt::Show> std::fmt::Show for ImmutSList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        try!(write!(f, "["));

        for (i, e) in self.iter().enumerate() {
            if i != 0 { try!(write!(f, ", ")); }
            try!(write!(f, "{}", *e));
        }

        write!(f, "]")
    }
}

impl<S: Writer, A: Hash<S>> Hash<S> for ImmutSList<A> {
    fn hash(&self, state: &mut S) {
        self.len().hash(state);
        for elt in self.iter() {
            elt.hash(state);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::hash;
    use test::Bencher;
    use test;

    use super::ImmutSList;

    #[test]
    fn test_basic() {
        let mut m: ImmutSList<Box<int>> = ImmutSList::new();
        assert_eq!(m.head(), None);
        assert_eq!(m.tail().head(), None);
        m = m.append(box 1);
        assert_eq!(m.head().unwrap(), & box 1);
        m = m.tail().append(box 2).append(box 3);
        assert_eq!(m.len(), 2);
        assert_eq!(m.head().unwrap(), & box 3);
        m = m.tail();
        assert_eq!(m.head().unwrap(), & box 2);
        m = m.tail();
        assert_eq!(m.len(), 0);
        assert_eq!(m.head(), None);
        m = m.append(box 7).append(box 5).append(box 3).append(box 1);
        assert_eq!(m.head().unwrap(), & box 1);
    }

    #[test]
    fn test_tailn() {
        let m = list_from(&[0i,1,2,3,4,5]);
        assert_eq!(m.tailn(0), m);
        assert_eq!(m.tailn(3), m.tail().tail().tail());
    }

    #[test]
    fn test_last() {
        let mut m = list_from(&[0i,1,2,3,4,5]);
        assert_eq!(m.last().unwrap(), &5);

        m = ImmutSList::new();
        assert_eq!(m.last(), None);
    }

    #[test]
    fn test_lastn() {
        let m = list_from(&[0i,1,2,3,4,5]);
        assert_eq!(m.lastn(0).head(), None);
        assert_eq!(m.lastn(8), m);
        assert_eq!(m.lastn(4), m.tail().tail());
    }

    #[cfg(test)]
    fn generate_test() -> ImmutSList<int> {
        list_from(&[0i,1,2,3,4,5,6])
    }

    #[cfg(test)]
    fn list_from<T: Clone>(v: &[T]) -> ImmutSList<T> {
        v.iter().rev().map(|x| (*x).clone()).collect()
    }

    #[test]
    fn test_iterator() {
        let m = generate_test();
        for (i, elt) in m.iter().enumerate() {
            assert_eq!(i as int, *elt);
        }
        let mut n = ImmutSList::new();
        assert_eq!(n.iter().next(), None);
        n = n.append(4i);
        let mut it = n.iter();
        assert_eq!(it.size_hint(), (1, Some(1)));
        assert_eq!(it.next().unwrap(), &4);
        assert_eq!(it.size_hint(), (0, Some(0)));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn test_iterator_clone() {
        let mut n = ImmutSList::new();
        n = n.append(1i).append(2).append(3);
        let mut it = n.iter();
        it.next();
        let mut jt = it.clone();
        assert_eq!(it.next(), jt.next());
        assert_eq!(it.next(), jt.next());
    }

    #[test]
    fn test_eq() {
        let mut n: ImmutSList<u8> = list_from(&[]);
        let mut m = list_from(&[]);
        assert!(n == m);
        n = n.append(1);
        assert!(n != m);
        m = m.append(1);
        assert!(n == m);

        let n = list_from(&[2i,3,4]);
        let m = list_from(&[1i,2,3]);
        assert!(n != m);
    }

    #[test]
    fn test_hash() {
      let mut x = ImmutSList::new();
      let mut y = ImmutSList::new();

      assert!(hash::hash(&x) == hash::hash(&y));

      x = x.append(1i).append(2).append(3);
      y = y.append(1i).append(4).tail().append(2).append(3);

      assert!(hash::hash(&x) == hash::hash(&y));
    }

    #[test]
    fn test_ord() {
        let n: ImmutSList<int> = list_from(&[]);
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
        let list: ImmutSList<int> = range(0i, 10).rev().collect();
        assert!(list.to_string().as_slice() == "[0, 1, 2, 3, 4, 5, 6, 7, 8, 9]");

        let list: ImmutSList<&str> = vec!["just", "one", "test", "more"].iter()
                                                                   .rev()
                                                                   .map(|&s| s)
                                                                   .collect();
        assert!(list.to_string().as_slice() == "[just, one, test, more]");
    }

    #[bench]
    fn bench_collect_into(b: &mut test::Bencher) {
        let v = &[0i, ..64];
        b.iter(|| {
            let _: ImmutSList<int> = v.iter().map(|x| *x).collect();
        })
    }

    #[bench]
    fn bench_append(b: &mut test::Bencher) {
        let mut m: ImmutSList<int> = ImmutSList::new();
        b.iter(|| {
            m = m.append(0);
        })
    }

    #[bench]
    fn bench_append_tail(b: &mut test::Bencher) {
        let mut m: ImmutSList<int> = ImmutSList::new();
        b.iter(|| {
            m = m.append(0).tail();
        })
    }

    #[bench]
    fn bench_iter(b: &mut test::Bencher) {
        let v = &[0i, ..128];
        let m: ImmutSList<int> = v.iter().map(|&x|x).collect();
        b.iter(|| {
            assert!(m.iter().count() == 128);
        })
    }
}
