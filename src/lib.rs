#![feature(unsafe_destructor)]
#![feature(default_type_params)]

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

extern crate test;

pub mod immutslist;