/// There are utilities that can be used to do an inner join between
/// ordered iterators. This can be useful to do selects between multiple
/// tables of items

use std::cmp::Ordering::{Less, Equal, Greater};
use std::iter::Peekable;
use std::collections::{
    btree_map, btree_set,
    vec_map,
    bitv_set
};

use super::super::{tree_set, tree_map, trie_set, trie_map};

/// Allows an iterator to be do an inner join with another
/// iterator to combine their values or filter based on their keys.
/// this trait is applied to an iterator over a map like structure
pub trait OrderedMapIterator<K, A>: Iterator<Item=(K, A)> + Sized {
    /// join two ordered maps together
    fn inner_join_map<B, T: OrderedMapIterator<K, B>>(self, map: T)
        -> InnerJoinMapIterator<Self, T> {
        InnerJoinMapIterator {
            a: self,
            b: map
        }
    }

    /// filter an ordered map with an ordered set
    fn inner_join_set<B, T: OrderedSetIterator<K>>(self, set: T)
        -> InnerJoinMapSetIterator<Self, T> {
        InnerJoinMapSetIterator {
            map: self,
            set: set
        }
    }

    /// Join an ordered iterator with the right ordered iterator. The
    /// new iterator will return a key value pair for every key in
    /// either iterator. If a key is present in both iterators they
    /// will be returned together (two values). If a value is in the Right,
    /// but not the left iterator it will be return without the value in the
    /// left iterator. If the value is in the left iterator by not the right
    /// that will be return without the value from the left iterator.
    fn outer_join<B, T: OrderedMapIterator<K, B>>(self, right: T)
        -> OuterJoinIterator<Self, T, (K, A), (K, B)> {
        OuterJoinIterator {
            left: self.peekable(),
            right: right.peekable()
        }
    }
}

/// Allows an iterator to be do an inner join with another
/// iterator to combine their values or filter based on their keys.
/// this trait is applied to an iterator over a set like structure
pub trait OrderedSetIterator<K>: Iterator<Item=K> + Sized {
    /// join two ordered maps together
    fn inner_join_map<B, T: OrderedMapIterator<K, B>>(self, map: T)
        -> InnerJoinMapSetIterator<T, Self> {
        InnerJoinMapSetIterator {
            map: map,
            set: self
        }
    }

    /// filter an ordered map with an ordered set
    fn inner_join_set<T: OrderedSetIterator<K>>(self, map: T)
        -> InnerJoinSetIterator<Self, T> {
        InnerJoinSetIterator {
            a: self,
            b: map
        }
    }
}

pub struct InnerJoinMapIterator<A, B> {a: A, b: B}
pub struct InnerJoinMapSetIterator<A, B> {map: A, set: B}
pub struct InnerJoinSetIterator<A, B> {a: A, b: B}
pub struct OuterJoinIterator<A: Iterator<Item=VA>, B: Iterator<Item=VB>, VA, VB> {
    left: Peekable<VA, A>,
    right: Peekable<VB, B>
}

#[old_impl_check]
impl<K: Ord, DataA, DataB,
     A: OrderedMapIterator<K, DataA>,
     B: OrderedMapIterator<K, DataB>>
     Iterator for InnerJoinMapIterator<A, B> {

    type Item = (K, (DataA, DataB));

    fn next(&mut self) -> Option<(K, (DataA, DataB))> {
        let (mut key_a, mut data_a) = match self.a.next() {
            None => return None,
            Some((key, data)) => (key, data)
        };

        let (mut key_b, mut data_b) = match self.b.next() {
            None => return None,
            Some((key, data)) => (key, data)
        };

        loop {
            match key_a.cmp(&key_b) {
                Less => {
                    match self.a.next() {
                        None => return None,
                        Some((key, data)) => {
                            key_a = key;
                            data_a = data;
                        }
                    };
                },
                Equal => return Some((key_a, (data_a, data_b))),
                Greater => {
                    match self.b.next() {
                        None => return None,
                        Some((key, data)) => {
                            key_b = key;
                            data_b = data;
                        }
                    };
                }
            }
        }
    }
}


#[old_impl_check]
impl<K: Ord,
     A: OrderedSetIterator<K>,
     B: OrderedSetIterator<K>>
     Iterator for InnerJoinSetIterator<A, B> {
    type Item = K;
    fn next(&mut self) -> Option<K> {
        let mut key_a = match self.a.next() {
            None => return None,
            Some(key) => key
        };

        let mut key_b = match self.b.next() {
            None => return None,
            Some(key) => key
        };

        loop {
            match key_a.cmp(&key_b) {
                Less => {
                    match self.a.next() {
                        None => return None,
                        Some(key) => { key_a = key; }
                    };
                },
                Equal => return Some(key_a),
                Greater => {
                    match self.b.next() {
                        None => return None,
                        Some(key) => { key_b = key; }
                    };
                }
            }
        }
    }
}

#[old_impl_check]
impl<K: Ord,
     V,
     SetIter: OrderedSetIterator<K>,
     MapIter: OrderedMapIterator<K, V>>
     Iterator for InnerJoinMapSetIterator<MapIter, SetIter> {
    type Item = (K, V);
    fn next(&mut self) -> Option<(K, V)> {
        let mut key_set = match self.set.next() {
            None => return None,
            Some(key) => key
        };

        let (mut key_map, mut data) = match self.map.next() {
            None => return None,
            Some((key, data)) => (key, data)
        };

        loop {
            match key_set.cmp(&key_map) {
                Less => {
                    match self.set.next() {
                        None => return None,
                        Some(key) => { key_set = key; }
                    };
                },
                Equal => return Some((key_set, data)),
                Greater => {
                    match self.map.next() {
                        None => return None,
                        Some((key, d)) => {
                            key_map = key;
                            data = d;
                        }
                    };
                }
            }
        }
    }
}

impl<K: Ord+Eq,
     VA, VB,
     A: OrderedMapIterator<K, VA>,
     B: OrderedMapIterator<K, VB>>
     Iterator for OuterJoinIterator<A, B, (K, VA), (K, VB)> {

    type Item = (K, (Option<VA>, Option<VB>));
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

impl<'a, K: Ord> OrderedSetIterator<&'a K> for btree_set::Iter<'a, K> {}
impl<'a, K: Ord, V> OrderedMapIterator<&'a K, &'a V> for btree_map::Iter<'a, K, V> {}
impl<'a, K> OrderedSetIterator<&'a K> for tree_set::Iter<'a, K> {}
impl<'a, K, V> OrderedMapIterator<&'a K, &'a V> for tree_map::Iter<'a, K, V> {}
impl<'a> OrderedSetIterator<usize> for trie_set::Iter<'a> {}
impl<'a, V> OrderedMapIterator<usize, &'a V> for trie_map::Iter<'a, V> {}
impl<'a, V> OrderedMapIterator<usize, &'a V> for vec_map::Iter<'a, V> {}
impl<'a> OrderedSetIterator<usize> for bitv_set::Iter<'a> {}


impl<K: Ord, VA, VB,
     A: OrderedMapIterator<K, VA>,
     B: OrderedMapIterator<K, VB>> OrderedMapIterator<K, (VA, VB)> for InnerJoinMapIterator<A, B> {}
impl<K: Ord, V,
     A: OrderedSetIterator<K>,
     B: OrderedMapIterator<K, V>> OrderedMapIterator<K, V> for InnerJoinMapSetIterator<B, A> {}
impl<K: Ord,
     A: OrderedSetIterator<K>,
     B: OrderedSetIterator<K>> OrderedSetIterator<K> for InnerJoinSetIterator<A, B> {}

#[cfg(test)]
mod tests {
    use test::Bencher;
    use test;

    use super::{OrderedSetIterator, OrderedMapIterator};

    #[test]
    fn join_two_sets() {
        use std::collections::BTreeSet;

        let powers_of_two: BTreeSet<isize> = range(1, 10).map(|x| x * 2).collect();
        let powers_of_three: BTreeSet<isize> = range(1, 10).map(|x| x * 3).collect();

        let expected = vec![6is, 12, 18];

        let powers_of_two_and_three: Vec<isize> =
            powers_of_two.iter()
            .inner_join_set(powers_of_three.iter())
            .map(|&x| x)
            .collect();

        assert_eq!(expected, powers_of_two_and_three);
    }

    #[test]
    fn join_three_sets() {
        use std::collections::BTreeSet;

        let powers_of_two: BTreeSet<isize> = range(1, 100).map(|x| x * 2).collect();
        let powers_of_three: BTreeSet<isize> = range(1, 100).map(|x| x * 3).collect();
        let powers_of_five: BTreeSet<isize> = range(1, 100).map(|x| x * 5).collect();

        let expected = vec![30, 60, 90, 120, 150, 180];

        let powers_of_two_and_three: Vec<isize> =
            powers_of_two.iter()
            .inner_join_set(powers_of_three.iter())
            .inner_join_set(powers_of_five.iter())
            .map(|&x| x)
            .collect();

        assert_eq!(expected, powers_of_two_and_three);
    }

    #[test]
    fn join_two_maps() {
        use std::collections::BTreeMap;

        let powers_of_two: BTreeMap<isize, isize> = range(1is, 10).map(|x| (x * 2, x)).collect();
        let powers_of_three: BTreeMap<isize, isize> = range(1is, 10).map(|x| (x * 3, x)).collect();

        let mut powers_of_two_and_three =
            powers_of_two.iter().inner_join_map(powers_of_three.iter())
            .map(|(&k, (&a, &b))| (k, a, b));

        assert_eq!(Some((6, 3, 2)), powers_of_two_and_three.next());
        assert_eq!(Some((12, 6, 4)), powers_of_two_and_three.next());
        assert_eq!(Some((18, 9, 6)), powers_of_two_and_three.next());
        assert_eq!(None, powers_of_two_and_three.next());
    }

    #[test]
    fn join_two_maps_to_set() {
        use std::collections::{BTreeMap, BTreeSet};

        let powers_of_two: BTreeSet<isize> = range(1, 10).map(|x| x * 2).collect();
        let powers_of_three: BTreeMap<isize, isize> = range(1is, 10).map(|x| (x * 3, x)).collect();

        let mut powers_of_two_and_three =
            powers_of_two.iter().inner_join_map(powers_of_three.iter())
            .map(|(&k, &a)| (k, a));

        assert_eq!(Some((6, 2)), powers_of_two_and_three.next());
        assert_eq!(Some((12, 4)), powers_of_two_and_three.next());
        assert_eq!(Some((18, 6)), powers_of_two_and_three.next());
        assert_eq!(None, powers_of_two_and_three.next());
    }

    #[test]
    fn outer_join_fizz_buzz() {
        use std::collections::BTreeMap;

        let mul_of_three: BTreeMap<isize, isize> = range(0, 100).map(|x| (x*3, x)).collect();
        let mul_of_five: BTreeMap<isize, isize> = range(0, 100).map(|x| (x*5, x)).collect();

        let mut fizz_buzz = BTreeMap::new();

        for (key, (three, five)) in mul_of_three.iter()
                                                .outer_join(mul_of_five.iter()) {
            fizz_buzz.insert(key, (three.is_some(), five.is_some()));
        }

        let res: BTreeMap<isize, String> = range(1, 100).map(|i|
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


    #[bench]
    pub fn inner_join_map(b: &mut test::Bencher) {
        use std::collections::BTreeSet;

        let powers_of_two: BTreeSet<usize> = range(1us, 1000000).map(|x| x * 2).collect();
        let powers_of_three: BTreeSet<usize> = range(1us, 1000000).map(|x| x * 3).collect();

        b.iter(||{
            for x in powers_of_two.iter()
                .inner_join_set(powers_of_three.iter()) {

                test::black_box(x);
            }
        })
    }
}
