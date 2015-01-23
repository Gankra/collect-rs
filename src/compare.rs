//! Comparators.
//!
//! A comparator is any type that implements the [`Compare`](trait.Compare.html) trait,
//! which imposes a [total order](https://en.wikipedia.org/wiki/Total_order). Its
//! [`compare`](trait.Compare.html#tymethod.compare) method accepts two values, which may
//! be of the same type or different types, and returns an ordering on them.
//!
//! Comparators are useful for parameterizing the behavior of sort methods and certain
//! data structures.
//!
//! The most basic comparator is [`Natural`](struct.Natural.html), which simply delegates
//! to the type's implementation of [`Ord`]
//! (http://doc.rust-lang.org/std/cmp/trait.Ord.html):
//!
//! ```rust
//! use collect::compare::{Compare, Natural};
//! use std::cmp::Ordering::{Less, Equal, Greater};
//!
//! let a = &1;
//! let b = &2;
//!
//! let cmp = Natural;
//! assert_eq!(cmp.compare(a, b), Less);
//! assert_eq!(cmp.compare(b, a), Greater);
//! assert_eq!(cmp.compare(a, a), Equal);
//! ```
//!
//! There are convenience methods for checking each of the six relations:
//!
//! ```rust
//! use collect::compare::{Compare, Natural};
//!
//! let a = &1;
//! let b = &2;
//!
//! let cmp = Natural;
//! assert!(cmp.compares_lt(a, b));
//! assert!(cmp.compares_le(a, b));
//! assert!(cmp.compares_ge(b, a));
//! assert!(cmp.compares_gt(b, a));
//! assert!(cmp.compares_eq(a, a));
//! assert!(cmp.compares_ne(a, b));
//! ```
//!
//! The [`CompareExt`](trait.CompareExt.html) trait provides extension methods that
//! consume a comparator to produce a new one with different behavior, similar to
//! [iterator adaptors](http://doc.rust-lang.org/std/iter/trait.IteratorExt.html). For
//! example, all comparators can be [reversed](trait.CompareExt.html#method.rev):
//!
//! ```rust
//! use collect::compare::{Compare, CompareExt, Natural};
//! use std::cmp::Ordering::Greater;
//!
//! let cmp = Natural.rev();
//! assert_eq!(cmp.compare(&1, &2), Greater);
//! ```
//!
//! It is possible to implement a comparator that is not based on the natural ordering of
//! a type by using a closure of type `Fn(&Lhs, &Rhs) -> Ordering`. For example, vectors
//! can be compared by their length instead of their contents:
//!
//! ```rust
//! use collect::compare::{Compare, CompareExt};
//! use std::cmp::Ordering::{Less, Greater};
//!
//! let a = vec![1, 2, 3];
//! let b = vec![4, 5];
//!
//! let cmp = |&: lhs: &Vec<u8>, rhs: &Vec<u8>| lhs.len().cmp(&rhs.len());
//! assert_eq!(cmp.compare(&a, &b), Greater);
//!
//! let cmp = cmp.rev();
//! assert_eq!(cmp.compare(&a, &b), Less);
//! ```
//!
//! Comparators can be combined [lexicographically]
//! (https://en.wikipedia.org/wiki/Lexicographical_order) in order to compare values
//! first by one key, [then](trait.CompareExt.html#method.then), if the first keys were
//! equal, by another:
//!
//! ```rust
//! use collect::compare::{Compare, CompareExt};
//! use std::cmp::Ordering::{Less, Equal, Greater};
//!
//! struct Pet { name: &'static str, age: u8 }
//!
//! let fido4 = &Pet { name: "Fido", age: 4 };
//! let ruff2 = &Pet { name: "Ruff", age: 2 };
//! let fido3 = &Pet { name: "Fido", age: 3 };
//!
//! let name_cmp = |&: lhs: &Pet, rhs: &Pet| lhs.name.cmp(rhs.name);
//! assert_eq!(name_cmp.compare(fido4, ruff2), Less);
//! assert_eq!(name_cmp.compare(fido4, fido3), Equal);
//! assert_eq!(name_cmp.compare(ruff2, fido3), Greater);
//!
//! let age_cmp = |&: lhs: &Pet, rhs: &Pet| lhs.age.cmp(&rhs.age);
//! assert_eq!(age_cmp.compare(fido4, ruff2), Greater);
//! assert_eq!(age_cmp.compare(fido4, fido3), Greater);
//! assert_eq!(age_cmp.compare(ruff2, fido3), Less);
//!
//! let name_age_cmp = name_cmp.then(age_cmp);
//! assert_eq!(name_age_cmp.compare(fido4, ruff2), Less);
//! assert_eq!(name_age_cmp.compare(fido4, fido3), Greater);
//! assert_eq!(name_age_cmp.compare(ruff2, fido3), Greater);
//! ```
//!
//! It is often repetitive to compare two values of the same type by the same key, so the
//! [key-extraction logic](struct.Extract.html) can be factored out, simplifying the
//! previous example:
//!
//! ```rust
//! use collect::compare::{Compare, CompareExt, Extract, Natural};
//! use std::cmp::Ordering::{Less, Greater};
//!
//! struct Pet { name: &'static str, age: u8 }
//!
//! let fido4 = &Pet { name: "Fido", age: 4 };
//! let ruff2 = &Pet { name: "Ruff", age: 2 };
//! let fido3 = &Pet { name: "Fido", age: 3 };
//!
//! let name_age_cmp = Extract::new(|p: &Pet| p.name, Natural)
//!              .then(Extract::new(|p: &Pet| p.age, Natural));
//!
//! assert_eq!(name_age_cmp.compare(fido4, ruff2), Less);
//! assert_eq!(name_age_cmp.compare(fido4, fido3), Greater);
//! assert_eq!(name_age_cmp.compare(ruff2, fido3), Greater);
//! ```

use std::borrow::BorrowFrom;
use std::cmp::Ordering::{self, Less, Equal, Greater};
use std::default::Default;
use std::fmt::{self, Debug};

/// Returns the maximum of two values according to the given comparator, or `lhs` if they
/// are equal.
///
/// # Examples
///
/// ```rust
/// use collect::compare::{Extract, Natural, max};
///
/// struct Foo { key: char, id: u8 }
///
/// let f1 = &Foo { key: 'a', id: 1};
/// let f2 = &Foo { key: 'a', id: 2};
/// let f3 = &Foo { key: 'b', id: 3};
///
/// let cmp = Extract::new(|f: &Foo| f.key, Natural);
/// assert_eq!(max(&cmp, f1, f2).id, f1.id);
/// assert_eq!(max(&cmp, f1, f3).id, f3.id);
/// ```
// FIXME: convert to default method on `Compare` once where clauses permit equality
// (https://github.com/rust-lang/rust/issues/20041)
pub fn max<'a, C: ?Sized, T: ?Sized>(cmp: &C, lhs: &'a T, rhs: &'a T) -> &'a T
    where C: Compare<T> {

    if cmp.compares_ge(lhs, rhs) { lhs } else { rhs }
}

/// Returns the minimum of two values according to the given comparator, or `lhs` if they
/// are equal.
///
/// # Examples
///
/// ```rust
/// use collect::compare::{Extract, Natural, min};
///
/// struct Foo { key: char, id: u8 }
///
/// let f1 = &Foo { key: 'b', id: 1};
/// let f2 = &Foo { key: 'b', id: 2};
/// let f3 = &Foo { key: 'a', id: 3};
///
/// let cmp = Extract::new(|f: &Foo| f.key, Natural);
/// assert_eq!(min(&cmp, f1, f2).id, f1.id);
/// assert_eq!(min(&cmp, f1, f3).id, f3.id);
/// ```
// FIXME: convert to default method on `Compare` once where clauses permit equality
// (https://github.com/rust-lang/rust/issues/20041)
pub fn min<'a, C: ?Sized, T: ?Sized>(cmp: &C, lhs: &'a T, rhs: &'a T) -> &'a T
    where C: Compare<T> {

    if cmp.compares_le(lhs, rhs) { lhs } else { rhs }
}

/// A comparator imposing a [total order](https://en.wikipedia.org/wiki/Total_order).
///
/// See the [`compare` module's documentation](index.html) for detailed usage.
///
/// The `compares_*` methods may be overridden to provide more efficient implementations.
pub trait Compare<Lhs: ?Sized, Rhs: ?Sized = Lhs> {
    /// Compares two values, returning `Less`, `Equal`, or `Greater` if `lhs` is less
    /// than, equal to, or greater than `rhs`, respectively.
    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering;

    /// Checks if `lhs` is less than `rhs`.
    fn compares_lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) == Less
    }

    /// Checks if `lhs` is less than or equal to `rhs`.
    fn compares_le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) != Greater
    }

    /// Checks if `lhs` is greater than or equal to `rhs`.
    fn compares_ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) != Less
    }

    /// Checks if `lhs` is greater than `rhs`.
    fn compares_gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) == Greater
    }

    /// Checks if `lhs` is equal to `rhs`.
    fn compares_eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) == Equal
    }

    /// Checks if `lhs` is not equal to `rhs`.
    fn compares_ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.compare(lhs, rhs) != Equal
    }
}

impl<F: ?Sized, Lhs: ?Sized, Rhs: ?Sized> Compare<Lhs, Rhs> for F
    where F: Fn(&Lhs, &Rhs) -> Ordering {

    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering { (*self)(lhs, rhs) }
}

impl<'a, Lhs: ?Sized, Rhs: ?Sized, C: ?Sized> Compare<Lhs, Rhs> for &'a C
    where C: Compare<Lhs, Rhs> {

    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        Compare::compare(*self, lhs, rhs)
    }
}

/// An extension trait with methods applicable to all comparators.
pub trait CompareExt<Lhs: ?Sized, Rhs: ?Sized = Lhs> : Compare<Lhs, Rhs> + Sized {
    /// Borrows the comparator's parameters before comparing them.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::compare::{Compare, CompareExt, Natural};
    /// use std::cmp::Ordering::{Less, Equal, Greater};
    ///
    /// let a_str = "a";
    /// let a_string = a_str.to_string();
    ///
    /// let b_str = "b";
    /// let b_string = b_str.to_string();
    ///
    /// let cmp = Natural::<str>.borrow();
    /// assert_eq!(cmp.compare(a_str, &a_string), Equal);
    /// assert_eq!(cmp.compare(a_str, b_str), Less);
    /// assert_eq!(cmp.compare(&b_string, a_str), Greater);
    /// ```
    fn borrow(self) -> Borrow<Self, Lhs, Rhs> { Borrow(self) }

    /// Reverses the ordering of the comparator.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::compare::{Compare, CompareExt, Natural};
    /// use std::cmp::Ordering::{Less, Equal, Greater};
    ///
    /// let a = &1;
    /// let b = &2;
    ///
    /// let cmp = Natural.rev();
    /// assert_eq!(cmp.compare(a, b), Greater);
    /// assert_eq!(cmp.compare(b, a), Less);
    /// assert_eq!(cmp.compare(a, a), Equal);
    /// ```
    fn rev(self) -> Rev<Self> { Rev(self) }

    /// Swaps the comparator's parameters, maintaining the underlying ordering.
    ///
    /// This is useful for providing a comparator `C: Compare<T, U>` in a context that
    /// expects `C: Compare<U, T>`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::compare::{Compare, CompareExt};
    /// use std::cmp::Ordering::{Less, Equal, Greater};
    ///
    /// let cmp = |&: lhs: &u8, rhs: &u16| (*lhs as u16).cmp(rhs);
    /// assert_eq!(cmp.compare(&1u8, &2u16), Less);
    /// assert_eq!(cmp.compare(&2u8, &1u16), Greater);
    /// assert_eq!(cmp.compare(&1u8, &1u16), Equal);
    ///
    /// let cmp = cmp.swap();
    /// assert_eq!(cmp.compare(&2u16, &1u8), Less);
    /// assert_eq!(cmp.compare(&1u16, &2u8), Greater);
    /// assert_eq!(cmp.compare(&1u16, &1u8), Equal);
    /// ```
    fn swap(self) -> Swap<Self> { Swap(self) }

    /// [Lexicographically](https://en.wikipedia.org/wiki/Lexicographical_order) combines
    /// the comparator with another.
    ///
    /// The retuned comparator compares values first using `self`, then, if they are
    /// equal, using `then`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use collect::compare::{Compare, CompareExt};
    /// use std::cmp::Ordering::{Less, Equal};
    ///
    /// struct Foo { key1: char, key2: u8 }
    ///
    /// let f1 = &Foo { key1: 'a', key2: 2};
    /// let f2 = &Foo { key1: 'a', key2: 3};
    ///
    /// let cmp = |&: lhs: &Foo, rhs: &Foo| lhs.key1.cmp(&rhs.key1);
    /// assert_eq!(cmp.compare(f1, f2), Equal);
    ///
    /// let cmp = cmp.then(|&: lhs: &Foo, rhs: &Foo| lhs.key2.cmp(&rhs.key2));
    /// assert_eq!(cmp.compare(f1, f2), Less);
    /// ```
    fn then<D>(self, then: D) -> Lexicographic<Self, D> where D: Compare<Lhs, Rhs> {
        Lexicographic(self, then)
    }
}

impl<C, Lhs: ?Sized, Rhs: ?Sized> CompareExt<Lhs, Rhs> for C where C: Compare<Lhs, Rhs> {}

/// A comparator that borrows its parameters before comparing them.
///
/// See [`CompareExt::borrow`](trait.CompareExt.html#method.borrow) for an example.
pub struct Borrow<C, Lb: ?Sized, Rb: ?Sized>(C) where C: Compare<Lb, Rb>;

impl<C, Lhs: ?Sized, Rhs: ?Sized, Lb: ?Sized, Rb: ?Sized> Compare<Lhs, Rhs> for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb>, Lb: BorrowFrom<Lhs>, Rb: BorrowFrom<Rhs> {

    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        self.0.compare(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_lt(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_le(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_ge(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_gt(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_eq(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }

    fn compares_ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_ne(BorrowFrom::borrow_from(lhs), BorrowFrom::borrow_from(rhs))
    }
}

// FIXME: replace with `derive(Clone)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> Clone for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb> + Clone {

    fn clone(&self) -> Borrow<C, Lb, Rb> { Borrow(self.0.clone()) }
}

// FIXME: replace with `derive(Copy)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> Copy for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb> + Copy {}

// FIXME: replace with `derive(Default)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> Default for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb> + Default {

    fn default() -> Borrow<C, Lb, Rb> { Borrow(Default::default()) }
}

// FIXME: replace with `derive(PartialEq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> PartialEq for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb> + PartialEq {

    fn eq(&self, other: &Borrow<C, Lb, Rb>) -> bool { self.0 == other.0 }
}

// FIXME: replace with `derive(Eq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> Eq for Borrow<C, Lb, Rb> where C: Compare<Lb, Rb> + Eq {}

// FIXME: replace with `derive(Debug)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<C, Lb: ?Sized, Rb: ?Sized> Debug for Borrow<C, Lb, Rb>
    where C: Compare<Lb, Rb> + Debug {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Borrow({:?})", self.0)
    }
}

/// A comparator that extracts a sort key from a value.
///
/// # Examples
///
/// ```rust
/// use collect::compare::{Compare, Extract, Natural};
/// use std::cmp::Ordering::Greater;
///
/// let a = vec![1, 2, 3];
/// let b = vec![4, 5];
///
/// let cmp = Extract::new(|vec: &Vec<u8>| vec.len(), Natural);
/// assert_eq!(cmp.compare(&a, &b), Greater);
/// ```
pub struct Extract<E, C, T: ?Sized, K> where E: Fn(&T) -> K, C: Compare<K> {
    ext: E,
    cmp: C,
}

// FIXME: convert to default method on `CompareExt` once where clauses permit equality
// (https://github.com/rust-lang/rust/issues/20041)
impl<E, C, T: ?Sized, K> Extract<E, C, T, K> where E: Fn(&T) -> K, C: Compare<K> {
    /// Returns a comparator that extracts a sort key using `ext` and compares it using
    /// `cmp`.
    pub fn new(ext: E, cmp: C) -> Extract<E, C, T, K> { Extract { ext: ext, cmp: cmp } }
}

impl<E, C, T: ?Sized, K> Compare<T> for Extract<E, C, T, K>
    where E: Fn(&T) -> K, C: Compare<K> {

    fn compare(&self, lhs: &T, rhs: &T) -> Ordering {
        self.cmp.compare(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_lt(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_lt(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_le(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_le(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_ge(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_ge(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_gt(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_gt(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_eq(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_eq(&(self.ext)(lhs), &(self.ext)(rhs))
    }

    fn compares_ne(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp.compares_ne(&(self.ext)(lhs), &(self.ext)(rhs))
    }
}

// FIXME: replace with `derive(Clone)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> Clone for Extract<E, C, T, K>
    where E: Fn(&T) -> K + Clone, C: Compare<K> + Clone {

    fn clone(&self) -> Extract<E, C, T, K> {
        Extract { ext: self.ext.clone(), cmp: self.cmp.clone() }
    }
}

// FIXME: replace with `derive(Copy)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> Copy for Extract<E, C, T, K>
    where E: Fn(&T) -> K + Copy, C: Compare<K> + Copy {}

// FIXME: replace with `derive(Default)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> Default for Extract<E, C, T, K>
    where E: Fn(&T) -> K + Default, C: Compare<K> + Default {

    fn default() -> Extract<E, C, T, K> {
        Extract { ext: Default::default(), cmp: Default::default() }
    }
}

// FIXME: replace with `derive(PartialEq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> PartialEq for Extract<E, C, T, K>
    where E: Fn(&T) -> K + PartialEq, C: Compare<K> + PartialEq {

    fn eq(&self, other: &Extract<E, C, T, K>) -> bool {
        self.ext == other.ext && self.cmp == other.cmp
    }
}

// FIXME: replace with `derive(Eq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> Eq for Extract<E, C, T, K>
    where E: Fn(&T) -> K + Eq, C: Compare<K> + Eq {}

// FIXME: replace with `derive(Debug)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<E, C, T: ?Sized, K> Debug for Extract<E, C, T, K>
    where E: Fn(&T) -> K + Debug, C: Compare<K> + Debug {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Extract {{ ext: {:?}, cmp: {:?} }}", self.ext, self.cmp)
    }
}

/// A comparator that [lexicographically]
/// (https://en.wikipedia.org/wiki/Lexicographical_order) combines two others.
///
/// See [`CompareExt::then`](trait.CompareExt.html#method.then) for an example.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Lexicographic<C, D>(C, D);

impl<C, D, Lhs: ?Sized, Rhs: ?Sized> Compare<Lhs, Rhs> for Lexicographic<C, D>
    where C: Compare<Lhs, Rhs>, D: Compare<Lhs, Rhs> {

    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        match self.0.compare(lhs, rhs) {
            Equal => self.1.compare(lhs, rhs),
            order => order,
        }
    }
}

/// A comparator that delegates to [`Ord`]
/// (http://doc.rust-lang.org/std/cmp/trait.Ord.html).
///
/// # Examples
///
/// ```rust
/// use collect::compare::{Compare, Natural};
/// use std::cmp::Ordering::{Less, Equal, Greater};
///
/// let a = &1;
/// let b = &2;
///
/// let cmp = Natural;
/// assert_eq!(cmp.compare(a, b), Less);
/// assert_eq!(cmp.compare(b, a), Greater);
/// assert_eq!(cmp.compare(a, a), Equal);
/// ```
pub struct Natural<T: Ord + ?Sized>;

impl<T: Ord + ?Sized> Compare<T> for Natural<T> {
    fn compare(&self, lhs: &T, rhs: &T) -> Ordering { Ord::cmp(lhs, rhs) }

    fn compares_lt(&self, lhs: &T, rhs: &T) -> bool { PartialOrd::lt(lhs, rhs) }

    fn compares_le(&self, lhs: &T, rhs: &T) -> bool { PartialOrd::le(lhs, rhs) }

    fn compares_ge(&self, lhs: &T, rhs: &T) -> bool { PartialOrd::ge(lhs, rhs) }

    fn compares_gt(&self, lhs: &T, rhs: &T) -> bool { PartialOrd::gt(lhs, rhs) }

    fn compares_eq(&self, lhs: &T, rhs: &T) -> bool { PartialEq::eq(lhs, rhs) }

    fn compares_ne(&self, lhs: &T, rhs: &T) -> bool { PartialEq::ne(lhs, rhs) }
}

// FIXME: replace with `derive(Clone)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> Clone for Natural<T> {
    fn clone(&self) -> Natural<T> { *self }
}

// FIXME: replace with `derive(Copy)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> Copy for Natural<T> {}

// FIXME: replace with `derive(Default)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> Default for Natural<T> {
    fn default() -> Natural<T> { Natural }
}

// FIXME: replace with `derive(PartialEq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> PartialEq for Natural<T> {
    fn eq(&self, _other: &Natural<T>) -> bool { true }
}

// FIXME: replace with `derive(Eq)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> Eq for Natural<T> {}

// FIXME: replace with `derive(Debug)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<T: Ord + ?Sized> Debug for Natural<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Natural") }
}

/// A comparator that reverses the ordering of another.
///
/// See [`CompareExt::rev`](trait.CompareExt.html#method.rev) for an example.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Rev<C>(C);

impl<C, Lhs: ?Sized, Rhs: ?Sized> Compare<Lhs, Rhs> for Rev<C> where C: Compare<Lhs, Rhs> {
    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        self.0.compare(lhs, rhs).reverse()
    }

    fn compares_lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_gt(lhs, rhs) }

    fn compares_le(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_ge(lhs, rhs) }

    fn compares_ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_le(lhs, rhs) }

    fn compares_gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_lt(lhs, rhs) }

    fn compares_eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_eq(lhs, rhs) }

    fn compares_ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool { self.0.compares_ne(lhs, rhs) }
}

/// A comparator that swaps another's parameters, maintaining the underlying ordering.
///
/// This is useful for providing a comparator `C: Compare<T, U>` in a context that
/// expects `C: Compare<U, T>`.
///
/// See [`CompareExt::swap`](trait.CompareExt.html#method.swap) for an example.
#[derive(Clone, Copy, Default, PartialEq, Eq, Debug)]
pub struct Swap<C>(C);

impl<C, Lhs: ?Sized, Rhs: ?Sized> Compare<Rhs, Lhs> for Swap<C>
    where C: Compare<Lhs, Rhs> {

    fn compare(&self, rhs: &Rhs, lhs: &Lhs) -> Ordering { self.0.compare(lhs, rhs) }

    fn compares_lt(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_lt(lhs, rhs) }

    fn compares_le(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_le(lhs, rhs) }

    fn compares_ge(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_ge(lhs, rhs) }

    fn compares_gt(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_gt(lhs, rhs) }

    fn compares_eq(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_eq(lhs, rhs) }

    fn compares_ne(&self, rhs: &Rhs, lhs: &Lhs) -> bool { self.0.compares_ne(lhs, rhs) }
}
