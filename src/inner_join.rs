/// There are utilities that can be used to do an inner join between
/// ordered iterators. This can be useful to do selects between multiple
/// tables of items

use std::collections::{
    btree_map, btree_set,
    tree_map, tree_set,
    trie_map, trie_set,
    vec_map,
    bitv_set
};

/// Allows an iterator to be do an inner join with another
/// iterator to combine their values or filter based on their keys.
/// this trait is applied to an iterator over a map like structure
pub trait InnerJoinMap<K, A>: Iterator<(K, A)> {
    /// join two ordered maps together
    fn inner_join_map<B, T: InnerJoinMap<K, B>>(self, map: T)
        -> InnerJoinMapIterator<Self, T> {
        InnerJoinMapIterator {
            a: self,
            b: map
        }
    }

    /// filter an ordered map with an ordered set
    fn inner_join_set<B, T: InnerJoinSet<K>>(self, set: T)
        -> InnerJoinMapSetIterator<Self, T> {
        InnerJoinMapSetIterator {
            map: self,
            set: set
        }
    }
}

/// Allows an iterator to be do an inner join with another
/// iterator to combine their values or filter based on their keys.
/// this trait is applied to an iterator over a set like structure
pub trait InnerJoinSet<K>: Iterator<K> {
    /// join two ordered maps together
    fn inner_join_map<B, T: InnerJoinMap<K, B>>(self, map: T)
        -> InnerJoinMapSetIterator<T, Self> {
        InnerJoinMapSetIterator {
            map: map,
            set: self
        }
    }

    /// filter an ordered map with an ordered set
    fn inner_join_set<T: InnerJoinSet<K>>(self, map: T)
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

impl<K: Ord, DataA, DataB,
     A: InnerJoinMap<K, DataA>,
     B: InnerJoinMap<K, DataB>>
     Iterator<(K, (DataA, DataB))> for InnerJoinMapIterator<A, B> {

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


impl<K: Ord,
     A: InnerJoinSet<K>,
     B: InnerJoinSet<K>>
     Iterator<K> for InnerJoinSetIterator<A, B> {
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

impl<K: Ord,
     V,
     SetIter: InnerJoinSet<K>,
     MapIter: InnerJoinMap<K, V>>
     Iterator<(K, V)> for InnerJoinMapSetIterator<MapIter, SetIter> {
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

impl<'a, K: Ord> InnerJoinSet<&'a K> for btree_set::Items<'a, K> {}
impl<'a, K: Ord, V> InnerJoinMap<&'a K, &'a V> for btree_map::Entries<'a, K, V> {}
impl<'a, K: Ord> InnerJoinSet<&'a K> for tree_set::SetItems<'a, K> {}
impl<'a, K: Ord, V> InnerJoinMap<&'a K, &'a V> for tree_map::Entries<'a, K, V> {}
impl<'a> InnerJoinSet<uint> for trie_set::SetItems<'a> {}
impl<'a, V> InnerJoinMap<uint, &'a V> for trie_map::Entries<'a, V> {}
impl<'a, V> InnerJoinMap<uint, &'a V> for vec_map::Entries<'a, V> {}
impl<'a> InnerJoinSet<uint> for bitv_set::BitPositions<'a> {}


impl<K: Ord, VA, VB,
     A: InnerJoinMap<K, VA>,
     B: InnerJoinMap<K, VB>> InnerJoinMap<K, (VA, VB)> for InnerJoinMapIterator<A, B> {}
impl<K: Ord, V,
     A: InnerJoinSet<K>,
     B: InnerJoinMap<K, V>> InnerJoinMap<K, V> for InnerJoinMapSetIterator<B, A> {}
impl<K: Ord,
     A: InnerJoinSet<K>,
     B: InnerJoinSet<K>> InnerJoinSet<K> for InnerJoinSetIterator<A, B> {}

#[test]
fn join_two_sets() {
    use std::collections::BTreeSet;

    let powers_of_two: BTreeSet<int> = range(1, 10).map(|x| x * 2).collect();
    let powers_of_three: BTreeSet<int> = range(1, 10).map(|x| x * 3).collect();

    let expected = vec![6, 12, 18];

    let powers_of_two_and_three =
        powers_of_two.iter()
        .inner_join_set(powers_of_three.iter())
        .map(|&x| x)
        .collect();

    assert_eq!(expected, powers_of_two_and_three);
}

#[test]
fn join_three_sets() {
    use std::collections::BTreeSet;

    let powers_of_two: BTreeSet<int> = range(1, 100).map(|x| x * 2).collect();
    let powers_of_three: BTreeSet<int> = range(1, 100).map(|x| x * 3).collect();
    let powers_of_five: BTreeSet<int> = range(1, 100).map(|x| x * 5).collect();

    let expected = vec![30, 60, 90, 120, 150, 180];

    let powers_of_two_and_three =
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

    let powers_of_two: BTreeMap<int, int> = range(1i, 10).map(|x| (x * 2, x)).collect();
    let powers_of_three: BTreeMap<int, int> = range(1i, 10).map(|x| (x * 3, x)).collect();

    let mut powers_of_two_and_three =
        powers_of_two.iter().inner_join_map(powers_of_three.iter())
        .map(|(&k, (&a, &b))| (k, a, b));

    assert_eq!(Some((6, 3, 2)), powers_of_two_and_three.next())
    assert_eq!(Some((12, 6, 4)), powers_of_two_and_three.next())
    assert_eq!(Some((18, 9, 6)), powers_of_two_and_three.next())
    assert_eq!(None, powers_of_two_and_three.next())
}

#[test]
fn join_two_maps_to_set() {
    use std::collections::{BTreeMap, BTreeSet};

    let powers_of_two: BTreeSet<int> = range(1, 10).map(|x| x * 2).collect();
    let powers_of_three: BTreeMap<int, int> = range(1i, 10).map(|x| (x * 3, x)).collect();

    let mut powers_of_two_and_three =
        powers_of_two.iter().inner_join_map(powers_of_three.iter())
        .map(|(&k, &a)| (k, a));

    assert_eq!(Some((6, 2)), powers_of_two_and_three.next())
    assert_eq!(Some((12, 4)), powers_of_two_and_three.next())
    assert_eq!(Some((18, 6)), powers_of_two_and_three.next())
    assert_eq!(None, powers_of_two_and_three.next())
}
