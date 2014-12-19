//! Comparators.

/// A comparator.
pub trait Cmp<Sized? Lhs, Sized? Rhs = Lhs> for Sized? {
    /// Compares two values.
    ///
    /// Returns `Less` if `lhs` is less than `rhs`, `Equal` if `lhs` is equal to `rhs`,
    /// or `Greater` if `lhs` is greater than `rhs`.
    fn cmp(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering;

    /// Checks if `lhs` is less than `rhs`.
    fn lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) == Less
    }

    /// Checks if `lhs` is less than or equal to `rhs`.
    fn le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) != Greater
    }

    /// Checks if `lhs` is greater than or equal to `rhs`.
    fn ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) != Less
    }

    /// Checks if `lhs` is greater than `rhs`.
    fn gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) == Greater
    }

    /// Checks if `lhs` is equal to `rhs`.
    fn eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) == Equal
    }

    /// Checks if `lhs` is not equal to `rhs`.
    fn ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.cmp(lhs, rhs) != Equal
    }

    /* FIXME: uncomment once where clauses permit equality constraints
    /// Returns the maximum of two values, or `lhs` if the values are equal.
    fn max<'a>(&self, lhs: &'a Lhs, rhs: &'a Rhs) -> &'a Lhs where Lhs = Rhs {
        if self.ge(lhs, rhs) { lhs } else { rhs }
    }

    /// Returns the minimum of two values, or `lhs` if the values are equal.
    fn min<'a>(&self, lhs: &'a Lhs, rhs: &'a Rhs) -> &'a Lhs where Lhs = Rhs {
        if self.le(lhs, rhs) { lhs } else { rhs }
    }
    */
}

/// An extension trait providing methods applicable to all comparators.
pub trait CmpExt<Sized? Lhs, Sized? Rhs = Lhs> : Cmp<Lhs, Rhs> {
    /// Lexicographically orders the comparator with another comparator.
    fn then<D: Cmp<Lhs, Rhs>>(self, other: D) -> Lexicographic<Self, D> {
        Lexicographic(self, other)
    }

    /// Reverses the order of the comparator.
    fn rev(self) -> Rev<Self> {
        Rev(self)
    }
}

impl<Sized? Lhs, Sized? Rhs, Sized? F: Fn(&Lhs, &Rhs) -> Ordering> Cmp<Lhs, Rhs> for F {
    fn cmp(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        (*self)(lhs, rhs)
    }
}

impl<Sized? Lhs, Sized? Rhs, C: Cmp<Lhs, Rhs>> CmpExt<Lhs, Rhs> for C {
}

/// A comparator that delegates to `Ord::cmp`.
pub struct Natural<Sized? Lhs: Ord<Rhs>, Sized? Rhs = Lhs>;

impl<Sized? Lhs: Ord<Rhs>, Sized? Rhs> Cmp<Lhs, Rhs> for Natural<Lhs, Rhs> {
    fn cmp(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        lhs.cmp(rhs)
    }

    fn lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.lt(rhs)
    }

    fn le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.le(rhs)
    }

    fn ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.ge(rhs)
    }

    fn gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.gt(rhs)
    }

    fn eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.eq(rhs)
    }

    fn ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        lhs.ne(rhs)
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

impl<Sized? Lhs, Sized? Rhs, C: Cmp<Lhs, Rhs>> Cmp<Lhs, Rhs> for Rev<C> {
    fn cmp(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        self.0.cmp(lhs, rhs).reverse()
    }

    fn lt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.gt(lhs, rhs)
    }

    fn le(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.ge(lhs, rhs)
    }

    fn ge(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.le(lhs, rhs)
    }

    fn gt(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.lt(lhs, rhs)
    }

    fn eq(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.eq(lhs, rhs)
    }

    fn ne(&self, lhs: &Lhs, rhs: &Rhs) -> bool {
        self.0.ne(lhs, rhs)
    }
}

/// A comparator that lexicographically orders two comparators.
#[deriving(Copy, Clone)]
pub struct Lexicographic<C, D>(C, D);

impl<Sized? Lhs, Sized? Rhs, C, D> Cmp<Lhs, Rhs> for Lexicographic<C, D>
    where C: Cmp<Lhs, Rhs>, D: Cmp<Lhs, Rhs> {

    fn cmp(&self, lhs: &Lhs, rhs: &Rhs) -> Ordering {
        match self.0.cmp(lhs, rhs) {
            Equal => self.1.cmp(lhs, rhs),
            ord => ord,
        }
    }
}

#[cfg(test)]
mod test {
    use super::{Cmp, CmpExt, Natural};

    struct Foo(u8, u8);

    #[test]
    fn test_closure() {
        let c = |&: lhs: &Foo, rhs: &Foo| lhs.1.cmp(&rhs.1);
        assert_eq!(c.cmp(&Foo(1, 2), &Foo(0, 3)), Less);
        assert_eq!(c.cmp(&Foo(1, 2), &Foo(0, 2)), Equal);
        assert_eq!(c.cmp(&Foo(1, 2), &Foo(0, 1)), Greater);
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
        assert_eq!(c.cmp(&1u, &2u), Less);
        assert_eq!(c.cmp(&1u, &1u), Equal);
        assert_eq!(c.cmp(&2u, &1u), Greater); }

    #[test]
    fn test_rev() {
        let c = Natural.rev();
        assert_eq!(c.cmp(&1u, &2u), Greater);
        assert_eq!(c.cmp(&1u, &1u), Equal);
        assert_eq!(c.cmp(&2u, &1u), Less);

        let c = c.rev();
        assert_eq!(c.cmp(&1u, &2u), Less);
        assert_eq!(c.cmp(&1u, &1u), Equal);
        assert_eq!(c.cmp(&2u, &1u), Greater);
    }

    #[test]
    fn test_lexicographic() {
        let c =  (|&: lhs: &Foo, rhs: &Foo| lhs.0.cmp(&rhs.0))
            .then(|&: lhs: &Foo, rhs: &Foo| lhs.1.cmp(&rhs.1));

        assert_eq!(c.cmp(&Foo(1, 2), &Foo(2, 2)), Less);
        assert_eq!(c.cmp(&Foo(2, 2), &Foo(1, 2)), Greater);

        assert_eq!(c.cmp(&Foo(1, 1), &Foo(1, 2)), Less);
        assert_eq!(c.cmp(&Foo(1, 2), &Foo(1, 2)), Equal);
        assert_eq!(c.cmp(&Foo(1, 3), &Foo(1, 2)), Greater);
    }
}
