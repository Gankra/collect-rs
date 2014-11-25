trait JoinIterator {
  fn join(&mut self, sep: &str) -> String;
}

impl<A: ToString, T: Iterator<A>> JoinIterator for T {
  fn join(&mut self, sep: &str) -> String {
    match self.next() {
      Some(elem) => {
        let mut output = String::from_str(elem.to_string().as_slice());
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
  let many = vec![1u,2,3];
  let one  = vec![1u];
  let none: Vec<uint> = vec![];

  assert_eq!(many.iter().join(", ").as_slice(), "1, 2, 3");
  assert_eq!(one .iter().join(", ").as_slice(), "1");
  assert_eq!(none.iter().join(", ").as_slice(), "");
}
