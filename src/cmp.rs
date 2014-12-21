//! Comparators.

/// A comparator.
pub trait Compare<Sized? Lhs, Sized? Rhs = Lhs> for Sized? {
    /// Compares two values.
    ///
    /// Returns `Less` if `lhs` is less than `rhs`, `Equal` if `lhs` is equal to `rhs`,
    /// or `Greater` if `lhs` is greater than `rhs`.
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

    /* FIXME: uncomment once where clauses permit equality constraints
    /// Returns the maximum of two values, or `lhs` if the values are equal.
    fn max<'a>(&self, lhs: &'a Lhs, rhs: &'a Rhs) -> &'a Lhs where Lhs = Rhs {
        if self.compares_ge(lhs, rhs) { lhs } else { rhs }
    }

    /// Returns the minimum of two values, or `lhs` if the values are equal.
    fn min<'a>(&self, lhs: &'a Lhs, rhs: &'a Rhs) -> &'a Lhs where Lhs = Rhs {
        if self.compares_le(lhs, rhs) { lhs } else { rhs }
    }
    */
}

/// An extension trait providing methods applicable to all comparators.
pub trait CompareExt<Sized? Lhs, Sized? Rhs = Lhs> : Compare<Lhs, Rhs> {
    /// Lexicographically orders the comparator with another comparator.
    fn then<D: Compare<Lhs, Rhs>>(self, other: D) -> Lexicographic<Self, D> {
        Lexicographic(self, other)
    }

    /// Reverses the order of the comparator.
    fn rev(self) -> Rev<Self> {
        Rev(self)
    }
}

impl<Sized? Lhs, Sized? Rhs, Sized? F: Fn(&Lhs, &Rhs) -> Ordering> Compare<Lhs, Rhs> for F {
    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        (*self)(lhs, rhs)
    }
}

impl<Sized? Lhs, Sized? Rhs, C: Compare<Lhs, Rhs>> CompareExt<Lhs, Rhs> for C {
}

/// A comparator that delegates to `Ord::cmp`.
pub struct Natural<Sized? Lhs: Ord<Rhs>, Sized? Rhs = Lhs>;

impl<Sized? Lhs: Ord<Rhs>, Sized? Rhs> Compare<Lhs, Rhs> for Natural<Lhs, Rhs> {
    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        Ord::cmp(lhs, rhs)
    }

    fn compares_lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialOrd::lt(lhs, rhs)
    }

    fn compares_le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialOrd::le(lhs, rhs)
    }

    fn compares_ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialOrd::ge(lhs, rhs)
    }

    fn compares_gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialOrd::gt(lhs, rhs)
    }

    fn compares_eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialEq::eq(lhs, rhs)
    }

    fn compares_ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        PartialEq::ne(lhs, rhs)
    }
}

// FIXME: replace with `deriving(Copy)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<Sized? Lhs: Ord<Rhs>, Sized? Rhs> Copy for Natural<Lhs, Rhs> {
}

// FIXME: replace with `deriving(Clone)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<Sized? Lhs: Ord<Rhs>, Sized? Rhs> Clone for Natural<Lhs, Rhs> {
    fn clone(&self) -> Natural<Lhs, Rhs> {
        Natural
    }
}

/// A comparator that reverses the order of another comparator.
#[deriving(Copy, Clone)]
pub struct Rev<C>(C);

impl<Sized? Lhs, Sized? Rhs, C: Compare<Lhs, Rhs>> Compare<Lhs, Rhs> for Rev<C> {
    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        self.0.compare(lhs, rhs).reverse()
    }

    fn compares_lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_gt(lhs, rhs)
    }

    fn compares_le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_ge(lhs, rhs)
    }

    fn compares_ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_le(lhs, rhs)
    }

    fn compares_gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_lt(lhs, rhs)
    }

    fn compares_eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_eq(lhs, rhs)
    }

    fn compares_ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.compares_ne(lhs, rhs)
    }
}

/// A comparator that lexicographically orders two comparators.
#[deriving(Copy, Clone)]
pub struct Lexicographic<C, D>(C, D);

impl<Sized? Lhs, Sized? Rhs, C, D> Compare<Lhs, Rhs> for Lexicographic<C, D>
    where C: Compare<Lhs, Rhs>, D: Compare<Lhs, Rhs> {

    fn compare(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        match self.0.compare(lhs, rhs) {
            Equal => self.1.compare(lhs, rhs),
            ord => ord,
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Compare, CompareExt, Natural};

    struct Foo(u8, u8);

    #[test]
    fn test_closure() {
        let c = |&: lhs: &Foo, rhs: &Foo| lhs.1.cmp(&rhs.1);
        assert_eq!(c.compare(&Foo(1, 2), &Foo(0, 3)), Less);
        assert_eq!(c.compare(&Foo(1, 2), &Foo(0, 2)), Equal);
        assert_eq!(c.compare(&Foo(1, 2), &Foo(0, 1)), Greater);
    }

    /* FIXME: uncomment once where clauses permit equality constraints
    #[test]
    fn test_min_max() {
        let c = |&: lhs: &Foo, rhs: &Foo| lhs.0.cmp(&rhs.0);

        let a = Foo(1, 2);
        let b = Foo(2, 3);
        assert_eq!(c.min(&a, &b).1, 2);
        assert_eq!(c.max(&a, &b).1, 3);

        let a = Foo(1, 2);
        let b = Foo(1, 3);
        assert_eq!(c.min(&a, &b).1, 2);
        assert_eq!(c.max(&a, &b).1, 2);
    }
    */

    #[test]
    fn test_natural() {
        let c = Natural;
        assert_eq!(c.compare(&1u, &2u), Less);
        assert_eq!(c.compare(&1u, &1u), Equal);
        assert_eq!(c.compare(&2u, &1u), Greater); }

    #[test]
    fn test_rev() {
        let c = Natural.rev();
        assert_eq!(c.compare(&1u, &2u), Greater);
        assert_eq!(c.compare(&1u, &1u), Equal);
        assert_eq!(c.compare(&2u, &1u), Less);

        let c = c.rev();
        assert_eq!(c.compare(&1u, &2u), Less);
        assert_eq!(c.compare(&1u, &1u), Equal);
        assert_eq!(c.compare(&2u, &1u), Greater);
    }

    #[test]
    fn test_lexicographic() {
        let c =  (|&: lhs: &Foo, rhs: &Foo| lhs.0.cmp(&rhs.0))
            .then(|&: lhs: &Foo, rhs: &Foo| lhs.1.cmp(&rhs.1));

        assert_eq!(c.compare(&Foo(1, 2), &Foo(2, 2)), Less);
        assert_eq!(c.compare(&Foo(2, 2), &Foo(1, 2)), Greater);

        assert_eq!(c.compare(&Foo(1, 1), &Foo(1, 2)), Less);
        assert_eq!(c.compare(&Foo(1, 2), &Foo(1, 2)), Equal);
        assert_eq!(c.compare(&Foo(1, 3), &Foo(1, 2)), Greater);
    }
}
