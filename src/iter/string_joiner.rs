/// An Iterator adapter that walks through all the elements in the Iterator,
/// converts them to Strings and joins them to one big String, seperated by
/// some seperator string slice.
pub trait StringJoiner {
  /// Converts all elements the Iterator yields to Strings,
  /// then combines them all into one String, seperated by sep.
  ///
  /// # Example
  ///
  /// ```rust
  /// use collect::iter::StringJoiner;
  ///
  /// let vec = vec![1,2,3];
  /// assert_eq!(&*vec.iter().join(", "), "1, 2, 3");
  /// ```
  fn join(&mut self, sep: &str) -> String;
}

// Implement it for all Iterators with Elements convertable into a String
impl<A: ToString, T: Iterator<Item=A>> StringJoiner for T {
  fn join(&mut self, sep: &str) -> String {
    match self.next() {
      Some(elem) => {
        let mut output = elem.to_string();
        for elem in *self {
          output.push_str(sep);
          output.push_str(elem.to_string().as_slice());
        }
        output
      }
      None => String::new()
    }
  }
}

#[test]
fn test_join() {
  let many = vec![1,2,3];
  let one  = vec![1];
  let none: Vec<usize> = vec![];

  assert_eq!(many.iter().join(", ").as_slice(), "1, 2, 3");
  assert_eq!( one.iter().join(", ").as_slice(), "1");
  assert_eq!(none.iter().join(", ").as_slice(), "");
}
