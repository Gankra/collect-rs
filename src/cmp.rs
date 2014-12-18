//! Comparators.

/// A comparator.
pub trait Cmp<Sized? T> for Sized? {
    /// Compares two values.
    ///
    /// Returns `Less` if `lhs` is less than `rhs`, `Equal` if `lhs` is equal to `rhs`,
    /// or `Greater` if `lhs` is greater than `rhs`.
    fn cmp(&self, lhs: &T, rhs: &T) -> Ordering;

    /// Checks if `lhs` is less than `rhs`.
    fn lt(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) == Less
    }

    /// Checks if `lhs` is less than or equal to `rhs`.
    fn le(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) != Greater
    }

    /// Checks if `lhs` is greater than or equal to `rhs`.
    fn ge(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) != Less
    }

    /// Checks if `lhs` is greater than `rhs`.
    fn gt(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) == Greater
    }

    /// Checks if `lhs` is equal to `rhs`.
    fn eq(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) == Equal
    }

    /// Checks if `lhs` is not equal to `rhs`.
    fn ne(&self, lhs: &T, rhs: &T) -> bool {
        self.cmp(lhs, rhs) != Equal
    }

    /// Returns the maximum of two values, or `lhs` if the values are equal.
    fn max<'a>(&self, lhs: &'a T, rhs: &'a T) -> &'a T {
        if self.ge(lhs, rhs) { lhs } else { rhs }
    }

    /// Returns the minimum of two values, or `lhs` if the values are equal.
    fn min<'a>(&self, lhs: &'a T, rhs: &'a T) -> &'a T {
        if self.le(lhs, rhs) { lhs } else { rhs }
    }
}

/// An extension trait providing methods applicable to all comparators.
pub trait CmpExt<Sized? T> : Cmp<T> {
    /// Lexicographically orders the comparator with another comparator.
    fn then<D: Cmp<T>>(self, other: D) -> Lexicographic<Self, D> {
        Lexicographic(self, other)
    }

    /// Reverses the order of the comparator.
    fn rev(self) -> Rev<Self> {
        Rev(self)
    }
}

impl<Sized? T, Sized? F: Fn(&T, &T) -> Ordering> Cmp<T> for F {
    fn cmp(&self, lhs: &T, rhs: &T) -> Ordering {
        (*self)(lhs, rhs)
    }
}

impl<Sized? T, C: Cmp<T>> CmpExt<T> for C {
}

/// A comparator that delegates to `Ord::cmp`.
pub struct Natural<Sized? T: Ord>;

impl<Sized? T: Ord> Cmp<T> for Natural<T> {
    fn cmp(&self, lhs: &T, rhs: &T) -> Ordering {
        lhs.cmp(rhs)
    }
}

// TODO: replace with `deriving(Copy)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<Sized? T: Ord> Copy for Natural<T> {
}

// TODO: replace with `deriving(Clone)` once
// https://github.com/rust-lang/rust/issues/19839 is fixed
impl<Sized? T: Ord> Clone for Natural<T> {
    fn clone(&self) -> Natural<T> {
        Natural
    }
}

/// A comparator that reverses the order of another comparator.
#[deriving(Copy, Clone)]
pub struct Rev<C>(C);

impl<Sized? T, C: Cmp<T>> Cmp<T> for Rev<C> {
    fn cmp(&self, lhs: &T, rhs: &T) -> Ordering {
        self.0.cmp(rhs, lhs)
    }
}

/// A comparator that lexicographically orders two comparators.
#[deriving(Copy, Clone)]
pub struct Lexicographic<C, D>(C, D);

impl<Sized? T, C: Cmp<T>, D: Cmp<T>> Cmp<T> for Lexicographic<C, D> {
    fn cmp(&self, lhs: &T, rhs: &T) -> Ordering {
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
