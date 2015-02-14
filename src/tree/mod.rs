// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Maps are collections of unique keys with corresponding values, and sets are
//! just unique keys without a corresponding value.
//!
//! This crate defines the `TreeMap` and `TreeSet` types. Their keys must implement `Ord`.
//!
//! `TreeMap`s are ordered.
//!
//! # Examples
//!
//! ```{rust}
//! use collect::TreeSet;
//!
//! let mut tree_set = TreeSet::new();
//!
//! tree_set.insert(2);
//! tree_set.insert(1);
//! tree_set.insert(3);
//!
//! for i in tree_set.iter() {
//!    println!("{}", i) // prints 1, then 2, then 3
//! }
//! ```

pub mod map;
pub mod set;

mod node;
