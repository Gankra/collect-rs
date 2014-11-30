use std::iter::Peekable;

use std::collections::{
    btree_map,
    tree_map,
    trie_map,
    vec_map,
};

/// this provides a way to do a full outer join on two ordered iterators
pub trait OuterJoinMap<K, A>: Iterator<(K, A)> {
    /// Join an ordered iterator with the right ordered iterator. The
    /// new iterator will return a key value pair for every key in
    /// either iterator. If a key is present in both iterators they
    /// will be returned together (two values). If a value is in the Right,
    /// but not the left iterator it will be return without the value in the
    /// left iterator. If the value is in the left iterator by not the right
    /// that will be return without the value from the left iterator.
    fn outer_join<B, T: OuterJoinMap<K, B>>(self, right: T)
        -> OuterJoinIterator<Self, T, (K, A), (K, B)> {
        OuterJoinIterator {
            left: self.peekable(),
            right: right.peekable()
        }
    }
}

pub struct OuterJoinIterator<A, B, VA, VB> {
    left: Peekable<VA, A>,
    right: Peekable<VB, B>
}

impl<K: Ord+Eq,
     VA, VB,
     A: OuterJoinMap<K, VA>,
     B: OuterJoinMap<K, VB>>
     Iterator<(K, (Option<VA>, Option<VB>))> for OuterJoinIterator<A, B, (K, VA), (K, VB)> {

    fn next(&mut self) -> Option<(K, (Option<VA>, Option<VB>))> {
        let which = match (self.left.peek(), self.right.peek()) {
            (Some(&(ref ka, _)), Some(&(ref kb, _))) => kb.cmp(ka),
            (None, Some(_)) => Less,
            (Some(_), None) => Greater,
            (None, None) => return None
        };

        match which {
            Equal => {
                let ((k, a), (_, b)) =
                    (self.left.next().expect("no value found"),
                     self.right.next().expect("no value found"));

                Some((k, (Some(a), Some(b))))
            }
            Less => {
                let (k, v) = self.right.next().expect("no value found");
                Some((k, (None, Some(v))))
            }
            Greater => {
                let (k, v) = self.left.next().expect("no value found");
                Some((k, (Some(v), None)))
            }
        }
    }
}

impl<'a, K: Ord, V> OuterJoinMap<&'a K, &'a V> for btree_map::Entries<'a, K, V> {}
impl<'a, K: Ord, V> OuterJoinMap<&'a K, &'a V> for tree_map::Entries<'a, K, V> {}
impl<'a, V> OuterJoinMap<uint, &'a V> for trie_map::Entries<'a, V> {}
impl<'a, V> OuterJoinMap<uint, &'a V> for vec_map::Entries<'a, V> {}

#[test]
fn outer_join_fizz_buzz() {
    use std::collections::BTreeMap;

    let mul_of_three: BTreeMap<int, int> = range(0, 100).map(|x| (x*3, x)).collect();
    let mul_of_five: BTreeMap<int, int> = range(0, 100).map(|x| (x*5, x)).collect();

    let mut fizz_buzz = BTreeMap::new();

    for (key, (three, five)) in mul_of_three.iter()
                                            .outer_join(mul_of_five.iter()) {
        fizz_buzz.insert(key, (three.is_some(), five.is_some()));
    }

    let res: BTreeMap<int, String> = range(1, 100).map(|i|
        (i, match fizz_buzz.get(&i) {
            None => format!("{}", i),
            Some(&(true, false)) => format!("Fizz"),
            Some(&(false, true)) => format!("Buzz"),
            Some(&(true, true)) => format!("FizzBuzz"),
            Some(&(false, false)) => panic!("Outer join failed...")
        })).collect();

    for i in range(1, 100) {
        match (i % 3, i % 5) {
            (0, 0) => assert_eq!("FizzBuzz", res[i].as_slice()),
            (0, _) => assert_eq!("Fizz", res[i].as_slice()),
            (_, 0) => assert_eq!("Buzz", res[i].as_slice()),
            _ => assert_eq!(format!("{}", i).as_slice(), res[i].as_slice())
        }
    }
}