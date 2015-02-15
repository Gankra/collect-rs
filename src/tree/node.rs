use std::cmp::Ordering;
use std::cmp::Ordering::*;
use std::mem::{replace, swap};

use compare::Compare;

// Nodes keep track of their level in the tree, starting at 1 in the
// leaves and with a red child sharing the level of the parent.
#[derive(Clone)]
pub struct Node<K, V> {
    key: K,
    value: V,
    left: Option<Box<Node<K, V>>>,
    right: Option<Box<Node<K, V>>>,
    level: usize,
}

impl<K, V> Node<K, V> {
    pub fn key(&self) -> &K { &self.key }

    pub fn value(&self) -> &V { &self.value }

    pub fn value_mut(&mut self) -> &mut V { &mut self.value }

    pub fn key_value_mut(&mut self) -> (&K, &mut V) { (&self.key, &mut self.value) }
}

impl<K, V> Node<K, V> {
    #[inline]
    fn new(key: K, value: V) -> Node<K, V> {
        Node {key: key, value: value, left: None, right: None, level: 1 }
    }

    // Remove left horizontal link by rotating right
    fn skew(&mut self) {
        if self.left.as_ref().map_or(false, |x| x.level == self.level) {
            let mut save = self.left.take().unwrap();
            swap(&mut self.left, &mut save.right); // save.right now None
            swap(self, &mut save);
            self.right = Some(save);
        }
    }

    // Remove dual horizontal link by rotating left and increasing level of
    // the parent
    fn split(&mut self) {
        if self.right.as_ref().map_or(false,
          |x| x.right.as_ref().map_or(false, |y| y.level == self.level)) {
            let mut save = self.right.take().unwrap();
            swap(&mut self.right, &mut save.left); // save.left now None
            save.level += 1;
            swap(self, &mut save);
            self.left = Some(save);
        }
    }
}

pub fn traverse<K, V, F>(mut node: &Option<Box<Node<K, V>>>, mut f: F)
    -> &Option<Box<Node<K, V>>> where F: FnMut(&Node<K, V>) -> Ordering {

    while let Some(ref r) = *node {
        node = match f(r) {
            Less => &r.left,
            Greater => &r.right,
            Equal => break,
        };
    }

    node
}

pub fn traverse_mut<K, V, F>(mut node: &mut Option<Box<Node<K, V>>>, mut f: F)
    -> &mut Option<Box<Node<K, V>>> where F: FnMut(&Node<K, V>) -> Ordering {

    loop {
        let curr = node;

        node = match *curr {
            None => break,
            Some(ref mut r) => match f(r) {
                Less => &mut r.left,
                Greater => &mut r.right,
                Equal => break,
            },
        };
    }

    node
}

pub fn max<K, V>(node: &Node<K, V>) -> Ordering {
    if node.right.is_some() { Greater } else { Equal }
}

pub fn min<K, V>(node: &Node<K, V>) -> Ordering {
    if node.left.is_some() { Less } else { Equal }
}

pub fn insert<K, V, C>(node: &mut Option<Box<Node<K, V>>>, key: K, value: V, cmp: &C)
    -> Option<V> where C: Compare<K> {

    match *node {
        Some(ref mut save) => {
            let old_value = match cmp.compare(&key, &save.key) {
                Less => insert(&mut save.left, key, value, cmp),
                Greater => insert(&mut save.right, key, value, cmp),
                Equal => {
                    save.key = key;
                    return Some(replace(&mut save.value, value));
                }
            };

            save.skew();
            save.split();
            old_value
        }
        None => {
            *node = Some(box Node::new(key, value));
            None
        }
    }
}

pub fn remove<K, V, C, Q: ?Sized>(node: &mut Option<Box<Node<K, V>>>, key: &Q, cmp: &C)
    -> Option<V> where C: Compare<Q, K> {

    fn heir_swap<K, V>(node: &mut Node<K, V>, mut child: &mut Option<Box<Node<K, V>>>) {
        loop {
            let curr = child;

            child = match *curr {
                None => return,
                Some(ref mut x) =>
                    if x.right.is_some() {
                        &mut x.right
                    } else {
                        swap(&mut node.key, &mut x.key);
                        swap(&mut node.value, &mut x.value);
                        return;
                    },
            }
        }
    }

    match *node {
      None => {
        return None; // bottom of tree
      }
      Some(ref mut save) => {
        let (ret, rebalance) = match cmp.compare(key, &save.key) {
          Less => (remove(&mut save.left, key, cmp), true),
          Greater => (remove(&mut save.right, key, cmp), true),
          Equal => {
            if save.left.is_some() {
                if save.right.is_some() {
                    let mut left = save.left.take();
                    heir_swap(save, &mut left);
                    save.left = left;
                    (remove(&mut save.left, key, cmp), true)
                } else {
                    let new = save.left.take().unwrap();
                    let old = replace(save, new);
                    *save = save.left.take().unwrap();
                    (Some(old.value), true)
                }
            } else if save.right.is_some() {
                let new = save.right.take().unwrap();
                let old = replace(save, new);
                (Some(old.value), true)
            } else {
                (None, false)
            }
          }
        };

        if rebalance {
            let left_level = save.left.as_ref().map_or(0, |x| x.level);
            let right_level = save.right.as_ref().map_or(0, |x| x.level);

            // re-balance, if necessary
            if left_level < save.level - 1 || right_level < save.level - 1 {
                save.level -= 1;

                if right_level > save.level {
                    let save_level = save.level;
                    for x in save.right.iter_mut() { x.level = save_level }
                }

                save.skew();

                for right in save.right.iter_mut() {
                    right.skew();
                    for x in right.right.iter_mut() { x.skew(); }
                }

                save.split();
                for x in save.right.iter_mut() { x.split(); }
            }

            return ret;
        }
      }
    }
    Some(node.take().unwrap().value)
}

trait Dir {
    fn pre<N>(node: &mut N) -> Option<N> where N: NodeRef;
    fn post<N>(node: &mut N) -> Option<N> where N: NodeRef;
}

pub enum Forward {}

impl Dir for Forward {
    fn pre<N>(node: &mut N) -> Option<N> where N: NodeRef { node.left() }
    fn post<N>(node: &mut N) -> Option<N> where N: NodeRef { node.right() }
}

pub enum Reverse {}

impl Dir for Reverse {
    fn pre<N>(node: &mut N) -> Option<N> where N: NodeRef { node.right() }
    fn post<N>(node: &mut N) -> Option<N> where N: NodeRef { node.left() }
}

trait NodeRef {
    type Item;

    fn left(&mut self) -> Option<Self>;
    fn right(&mut self) -> Option<Self>;

    fn item(self) -> Self::Item;
}

pub fn as_ref<K, V>(node: &Option<Box<Node<K, V>>>) -> Option<&Node<K, V>> {
    node.as_ref().map(|node| &**node)
}

impl<'a, K, V> NodeRef for &'a Node<K, V> {
    type Item = (&'a K, &'a V);

    fn left(&mut self) -> Option<&'a Node<K, V>> { as_ref(&self.left) }
    fn right(&mut self) -> Option<&'a Node<K, V>> { as_ref(&self.right) }

    fn item(self) -> (&'a K, &'a V) { (&self.key, &self.value) }
}

impl<K, V> NodeRef for Box<Node<K, V>> {
    type Item = (K, V);

    fn left(&mut self) -> Option<Box<Node<K, V>>> { self.left.take() }
    fn right(&mut self) -> Option<Box<Node<K, V>>> { self.right.take() }

    fn item(self) -> (K, V) {
        let node = *self;
        (node.key, node.value)
    }
}

trait IterSize {
    fn decrement(&mut self);

    fn get(&self) -> (usize, Option<usize>);
}

impl IterSize for usize {
    fn decrement(&mut self) { *self -= 1; }

    fn get(&self) -> (usize, Option<usize>) { (*self, Some(*self)) }
}

impl IterSize for (usize, usize) {
    fn decrement(&mut self) {
        use std::num::Int;
        self.1 -= 1;
        self.0 = self.0.saturating_sub(1);
    }

    fn get(&self) -> (usize, Option<usize>) { (self.0, Some(self.1)) }
}

pub struct Iter<N, S, D> where N: NodeRef, S: IterSize, D: Dir {
    stack: Vec<N>,
    node: Option<N>,
    size: S,
}

impl<N, S, D> Iter<N, S, D> where N: NodeRef, S: IterSize, D: Dir {
    pub fn new(node: Option<N>, size: S) -> Iter<N, S, D> {
        Iter { stack: vec![], node: node, size: size }
    }
}

impl<'a, K, V> Iter<&'a Node<K, V>, (usize, usize), Forward> {
    pub fn bounded<C, Q: ?Sized>(node: &'a Option<Box<Node<K, V>>>, cmp: C, key: &Q,
                                 lower: bool, max_size: usize)
        -> Iter<&'a Node<K, V>, (usize, usize), Forward> where C: Compare<Q, K> {

        let mut iter = Iter::new(as_ref(node), (0, max_size));

        loop {
            let order = if let Some(ref node) = iter.node {
                cmp.compare(key, &node.key)
            } else {
                break;
            };

            match order {
                Less => iter.traverse_left(),
                Greater => iter.traverse_right(),
                Equal => if lower { break } else { iter.traverse_right() },
            }
        }

        iter.traverse_complete();
        iter
    }

    fn traverse_left(&mut self) {
        let mut node = self.node.take().unwrap();
        self.node = node.left();
        self.stack.push(node);
    }

    fn traverse_right(&mut self) {
        let mut node = self.node.take().unwrap();
        self.node = node.right();
    }

    fn traverse_complete(&mut self) {
        if let Some(node) = self.node.take() {
            self.stack.push(node);
        }
    }
}

impl<N, S, D> Clone for Iter<N, S, D>
    where N: Clone + NodeRef, S: Clone + IterSize, D: Dir {

    fn clone(&self) -> Iter<N, S, D> {
        Iter {
            stack: self.stack.clone(),
            node: self.node.clone(),
            size: self.size.clone(),
        }
    }
}

impl<N, S, D> Iterator for Iter<N, S, D> where N: NodeRef, S: IterSize, D: Dir {
    type Item = <N as NodeRef>::Item;

    fn next(&mut self) -> Option<<N as NodeRef>::Item> {
        while let Some(mut node) = self.node.take() {
            self.node = <D as Dir>::pre(&mut node);
            self.stack.push(node);
        }

        self.stack.pop().map(|mut node| {
            self.node = <D as Dir>::post(&mut node);
            self.size.decrement();
            node.item()
        })
    }

    fn size_hint(&self) -> (usize, Option<usize>) { self.size.get() }
}

#[cfg(test)]
impl<K, V> Node<K, V> where K: Ord {
    pub fn check_left(&self) {
        match self.left {
            Some(ref r) => {
                assert_eq!(r.key.cmp(&self.key), Less);
                assert!(r.level == self.level - 1); // left is black
                r.check_left();
                r.check_right(false);
            }
            None => assert!(self.level == 1), // parent is leaf
        }
    }

    pub fn check_right(&self, parent_red: bool) {
        match self.right {
            Some(ref r) => {
                assert_eq!(r.key.cmp(&self.key), Greater);
                let red = r.level == self.level;
                if parent_red { assert!(!red) } // no dual horizontal links
                // Right red or black
                assert!(red || r.level == self.level - 1);
                r.check_left();
                r.check_right(red);
            }
            None => assert!(self.level == 1), // parent is leaf
        }
    }
}
