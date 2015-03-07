
//! collect-rs is intended as an experimental extension of the Rust standard library's
//! libcollections. Ideas that are too niche, crazy, or experimental to land in libcollections
//! can be gathered here where they can gain the maintenance and network-effect benefits that
//! libcollections enjoys, but without worrying about such ivory tower concepts as
//! "general usefulness" and "consistency".
//!
//! For the time being we plan to be highly volatile with a low barrier of entry. We want to
//! explore the space of data structuring in Rust. We want to prove out ideas and implementations
//! that could one day make their way into the standard library.
//!
//! Got a Concurrent, Immutable, or Persistent collection? Awesome! Crazy ideas for collection or
//! iterator adapters? Heck yeah!
//!
//! Come on in!
//!
//! -----------
//!
//! Note that anything include in collect-rs is theoretically a candidate for inclusion in
//! libcollections. As such, this project is licensed under the same terms as Rust itself.

// there's too many combinations to track this stuff properly
#![allow(unused_features)]
#![allow(raw_pointer_derive)]

#![cfg_attr(test, feature(test))]

#![feature(box_patterns, box_syntax)]
#![feature(std_misc)]
#![feature(unboxed_closures)]
#![feature(unsafe_destructor)]

#![feature(core, hash, alloc)]

#[cfg(test)] extern crate rand;
#[cfg(test)] extern crate test;
extern crate core;

#[cfg(feature="traverse")]
extern crate traverse;

#[cfg(test)] #[macro_use] mod bench;

// Re-Exports
#[cfg(feature="blist")] pub use blist::BList;
#[cfg(feature="enum_set")] pub use enum_set::EnumSet;
#[cfg(feature="immut_slist")] pub use immut_slist::ImmutSList;
#[cfg(feature="interval_heap")] pub use interval_heap::IntervalHeap;
#[cfg(feature="linked_hash_map")] pub use linked_hash_map::LinkedHashMap;
#[cfg(feature="lru_cache")] pub use lru_cache::LruCache;
#[cfg(feature="tree_map")] pub use tree_map::TreeMap;
#[cfg(feature="tree_map")] pub use tree_set::TreeSet;
#[cfg(feature="trie_map")] pub use trie_map::TrieMap;
#[cfg(feature="trie_map")] pub use trie_set::TrieSet;

// privates
#[cfg(feature="tree_map")] mod tree;
#[cfg(feature="trie_map")] mod trie;

// publics

#[cfg(feature="compare")] pub mod compare;
pub mod iter;

#[cfg(feature="blist")] pub mod blist;
#[cfg(feature="enum_set")] pub mod enum_set;
#[cfg(feature="immut_slist")] pub mod immut_slist;
#[cfg(feature="interval_heap")] pub mod interval_heap;
#[cfg(feature="linked_hash_map")] pub mod linked_hash_map;
#[cfg(feature="lru_cache")] pub mod lru_cache;

#[cfg(feature="tree_map")]
pub mod tree_map {
    pub use tree::map::*;
}

#[cfg(feature="tree_map")]
pub mod tree_set {
    pub use tree::set::*;
}

#[cfg(feature="trie_map")]
pub mod trie_map {
    pub use trie::map::*;
}

#[cfg(feature="trie_map")]
pub mod trie_set {
    pub use trie::set::*;
}

#[cfg(feature="proto")]
pub mod proto;

