use std::collections::RingBuf;
use std::rand::{Rng, TaskRng, task_rng};

/// An Iterator that uses a pseudo-random number generator to decide whether to
/// skip a value and yield it later, or yield it now.
///
/// Once the underlying iterator is exhausted, all the remaining skipped values will be yielded.
///
/// For finite iterators, this adaptor will yield all elements in a random order.  
/// For infinite iterators, this adaptor will randomly skip elements and possibly yield them later,
/// but will not discard any.
///
/// ###Example
/// ```rust
/// use collect::iter::SampleIterator;
///
/// for i in range(1u, 20).sample(2) {
///     println!("{}", i);
/// }
/// ```
pub struct Sample<T, I, R> {
    iter: I,
    skipped: RingBuf<T>,
    rng: R,
    /// This iterator has a one in `weight` chance of skipping a value.
    pub weight: uint,
}

impl<T, I: Iterator<T>, R: Rng> Iterator<T> for Sample<T, I, R> {

    /// Yield `I::next()` or skip it and yield it later, yielding a previously skipped value
    /// instead.
    ///
    /// If `self.weight == 1`, this will yield the oldest skipped element, if any (always `None` if the
    /// iterator is fresh).  
    /// If `self.weight == 0`, this will yield `I::next()`.
    fn next(&mut self) -> Option<T> { 
        match self.weight {
             1 => return self.skipped.pop_back(), // Would skip forever, causing infinite recursion
             0 => return self.iter.next(), // Just an optimization
             _ => (),
        }

        if let Some(next) = self.iter.next() {
            // If true, skip this iteration and yield a skipped value instead.
            if self.rng.gen_weighted_bool(self.weight) {
                // Get the oldest skipped value and push this iteration
                let res = if let Some(skipped) = self.skipped.pop_back() {
                    Some(skipped)
                } else {
                    self.next()
                };

                self.skipped.push_front(next);
                res
            } else {
                Some(next)
            }
       } else {
           self.skipped.pop_back()
       }
    }

    /// Returns the size hint of the underlying `Iterator`.
    fn size_hint(&self) -> (uint, Option<uint>) {
        // This adaptor will always yield the same number of values as the underlying iterator.
        self.iter.size_hint()    
    }
}

/// A trait describing iterators that the `Sample` adaptor can be applied to.
pub trait SampleIterator<T>: Iterator<T> {
    /// Sample this iterator using the task-local random number generator
    /// with a one in `weight` chance of skipping a value.
    ///
    /// A `weight` of `1` will cause this iterator to always return `None`.  
    /// A `weight` of `0` will cause this iterator to always yield the next value.
    fn sample(self, weight: uint) -> Sample<T, Self, TaskRng> {
        self.sample_with_rng(task_rng(), weight)
    }

    /// Sample this iterator using the given `Rng` and a one in `weight` chance 
    /// of skipping a value.
    ///
    /// See `sample()` for details on `weight`.
    fn sample_with_rng<R: Rng>(self, rng: R, weight: uint) -> Sample<T, Self, R>{
        Sample {
            iter: self,
            skipped: RingBuf::new(),
            rng: rng,
            weight: weight,
        }
    }
}

impl<T, I: Iterator<T>> SampleIterator<T> for I {}

#[test]
fn yields_all() {
    const MAX: uint = 20;
    let values: Vec<uint> = range(1, MAX).sample(2).collect();
    assert_eq!(values.len(), MAX - 1);
}

#[test]
fn uniform_distribution() {
    let mut counts = [0u; 1000];
   
    for _ in range(0u, 1000) { 
        for i in range(0u, 1000).sample(2) {
            counts[i] += 1;
        }
    }

    for (val, &count) in counts.iter().enumerate() {
        assert!(count >= 990 && count <= 1010, "Failed Uniform distribution: {} [{}])", val, count);  
    }
}
