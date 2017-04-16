/// Creates an iterator that will yield the given elements.
/// Supports all the syntax of `vec!`.
///
/// # Examples
///
/// ```
/// #[macro_use] extern crate collect;
/// use std::collections::RingBuf;
/// fn main() {
///     // RingBuf contains 10 1's
///     let buf: RingBuf<_> = iter![1; 10].collect();
/// }
/// ```
///
/// ```
/// #[macro_use] extern crate collect;
/// use std::collections::HashSet;
///
/// fn main() {
///     // HashSet contains 1, 2, 3
///     let buf: HashSet<_> = iter![1, 2, 3].collect();
/// }
/// ```
/// ```
///
#[macro_export]
#[stable(feature = "rust1", since = "1.0.0")]
macro_rules! iter {
    ($x:expr; $y:expr) => (
        vec![$x; $y].into_iter()
    );
    ($($x:expr),*) => (
        vec![$($x),*].into_iter()
    );
}

#[cfg(test)]
mod test {
    #[test]
    fn test_iter() {
        let mut foo = iter![1, 2, 3];
        assert_eq!(foo.next(), Some(1));
        assert_eq!(foo.next(), Some(2));
        assert_eq!(foo.next(), Some(3));
        assert_eq!(foo.next(), None);

        let mut foo = iter![];
        assert_eq!(foo.next(), None::<i32>);

        let mut foo = iter![1; 3];
        assert_eq!(foo.next(), Some(1));
        assert_eq!(foo.next(), Some(1));
        assert_eq!(foo.next(), Some(1));
        assert_eq!(foo.next(), None);
    }
}
