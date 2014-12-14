use std::mem;

#[deriving(Clone)]
pub struct Node<K, V> {
    pub key: K,
    pub value: V,
    pub left: Option<Box<Node<K, V>>>,
    pub right: Option<Box<Node<K, V>>>,
}

impl<K, V> Node<K, V> {
    pub fn new(k: K, v: V,
               l: Option<Box<Node<K, V>>>,
               r: Option<Box<Node<K, V>>>) -> Box<Node<K, V>> {
        box Node{ key: k, value: v, left: l, right: r }
    }

    #[inline(always)]
    pub fn pop_left(&mut self) -> Option<Box<Node<K, V>>> {
        mem::replace(&mut self.left, None)
    }

    #[inline(always)]
    pub fn pop_right(&mut self) -> Option<Box<Node<K, V>>> {
        mem::replace(&mut self.right, None)
    }
}
