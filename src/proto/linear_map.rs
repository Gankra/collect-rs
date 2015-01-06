use std::iter::Map;
use std::mem;
use std::slice;

#[derive(Clone, Default)]
pub struct LinearMap<K,V> {
    storage: Vec<(K,V)>,
}

pub type Iter<'a, K:'a, V:'a> = Map<(&'a (K, V)), (&'a K, &'a V), slice::Iter<'a, (K, V)>, fn(&'a (K, V)) -> (&'a K, &'a V)>;
pub type IterMut<'a, K:'a, V:'a> = Map<(&'a mut (K, V)), (&'a mut K, &'a mut V), slice::IterMut<'a, (K, V)>, fn(&'a mut (K, V)) -> (&'a mut K, &'a mut V)>;
pub type Keys<'a, K:'a, V:'a> = Map<(&'a K, &'a V), &'a K, Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a K>;
pub type Values<'a, K:'a, V:'a> = Map<(&'a K, &'a V), &'a V, Iter<'a, K, V>, fn((&'a K, &'a V)) -> &'a V>;

impl<K:PartialEq+Eq,V> LinearMap<K,V> {
    pub fn new() -> LinearMap<K,V> {
        LinearMap {
            storage: Vec::new(),
        }
    }
    pub fn with_capacity(capacity: uint) -> LinearMap<K,V> {
        LinearMap {
            storage: Vec::with_capacity(capacity),
        }
    }
    pub fn capacity(&self) -> uint {
        self.storage.capacity()
    }
    pub fn reserve(&mut self, additional: uint) {
        self.storage.reserve(additional);
    }
    pub fn reserve_exact(&mut self, additional: uint) {
        self.storage.reserve_exact(additional);
    }
    pub fn shrink_to_fit(&mut self) {
        self.storage.shrink_to_fit();
    }
    pub fn len(&self) -> uint {
        self.storage.len()
    }
    pub fn is_empty(&self) -> bool {
        self.storage.is_empty()
    }
    pub fn clear(&mut self) {
        self.storage.clear();
    }
    pub fn iter<'a>(&'a self) -> Iter<'a, K, V> {
        fn ref_<A,B>(&(ref v1, ref v2): &(A, B)) -> (&A, &B) { (v1, v2) }
        self.storage.iter().map(ref_ as fn(&'a (K, V)) -> (&'a K, &'a V))
    }
    pub fn iter_mut<'a>(&'a mut self) -> IterMut<'a, K, V> {
        fn ref_<A,B>(&(ref mut v1, ref mut v2): &mut (A, B)) -> (&mut A, &mut B) { (v1, v2) }
        self.storage.iter_mut().map(ref_ as fn(&'a mut (K, V)) -> (&'a mut K, &'a mut V))
    }
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        fn first<A,B>((v, _): (A, B)) -> A { v }
        self.iter().map(first as fn((&'a K, &'a V)) -> &'a K)
    }
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        fn second<A,B>((_, v): (A, B)) -> B { v }
        self.iter().map(second as fn((&'a K, &'a V)) -> &'a V)
    }
    pub fn get<'a>(&'a self, key: &K) -> Option<&'a V> {
        for (k, v) in self.iter() {
            if key == k {
                return Some(v);
            }
        }
        None
    }
    pub fn get_mut<'a>(&'a mut self, key: &K) -> Option<&'a mut V> {
        for (k, v) in self.iter_mut() {
            if key == k {
                return Some(v);
            }
        }
        None
    }
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }
    pub fn insert(&mut self, key: K, value: V) -> Option<V> {
        for kv in self.storage.iter_mut() {
            let found;
            {
                let &(ref k, _) = kv;
                found = key == *k;
            }
            if found {
                let (_, v) = mem::replace(kv, (key, value));
                return Some(v);
            }
        }
        self.storage.push((key, value));
        None
    }
    pub fn remove(&mut self, key: &K) -> Option<V> {
        for i in range(0, self.storage.len()) {
            let found;
            {
                let (ref k, _) = self.storage[i];
                found = key == k;
            }
            if found {
                let (_, v) = self.storage.swap_remove(i);
                return Some(v);
            }
        }
        None
    }
}
