
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


#![feature(unsafe_destructor)]
#![feature(default_type_params)]
#![feature(unboxed_closures)]
#![feature(globs)]
#![feature(macro_rules)]

#[cfg(test)] extern crate test;
extern crate core;
extern crate traverse;




// Re-Exports

pub use blist::BList;
pub use enum_set::EnumSet;
pub use immut_slist::ImmutSList;
pub use interval_heap::IntervalHeap;
pub use lru_cache::LruCache;
pub use tree_map::TreeMap;
pub use tree_set::TreeSet;
pub use trie_map::TrieMap;
pub use trie_set::TrieSet;




// privates

mod tree;
mod trie;
#[cfg(test)] mod bench;



// publics

pub mod iter;

pub mod blist;
pub mod enum_set;
pub mod immut_slist;
pub mod interval_heap;
pub mod lru_cache;

pub mod tree_map {
    pub use tree::map::*;
}

pub mod tree_set {
    pub use tree::set::*;
}

pub mod trie_map {
    pub use trie::map::*;
}

pub mod trie_set {
    pub use trie::set::*;
}



pub mod proto;

