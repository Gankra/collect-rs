extern crate alloc;

use self::alloc::arc;

use std::cmp::min;
use std::fmt::{Formatter, Show};
use std::fmt::Error as FmtError;
use std::iter::range_inclusive;
use std::sync::Arc;
use std::mem;

/// A vector that can be operated on concurrently via non-overlapping slices.
///
/// Get a `ParVec` and a vector of slices via `new()`, send the slices to other threads
/// and mutate them, then get the mutated vector with `into_inner()` when finished.
pub struct ParVec<T> {
    data: Arc<Vec<T>>,
}

impl<T: Send + Sync> ParVec<T> {
    /// Create a new `ParVec`, returning it and a vector of slices that can be sent
    /// to other threads and mutated concurrently.
    pub fn new(vec: Vec<T>, slices: uint) -> (ParVec<T>, Vec<ParSlice<T>>) {
        let data = Arc::new(vec);

        let par_slices = sub_slices(data.as_slice(), slices).into_iter()
            .map(|slice|
                ParSlice {
                    _vec: data.clone(),
                    data: unsafe { mem::transmute(slice) },                
                }
            ).collect();
 
        let par_vec = ParVec {
            data: data,
        };

        (par_vec, par_slices)
    }    
        
    /// Take the inner `Vec` if there are no slices remaining.
    /// Returns `Err(self)` if there are still slices out there.
    pub fn into_inner_opt(self) -> Result<Vec<T>, ParVec<T>> {
        // Unwrap if we hold a unique reference 
        // (we don't use weak refs so ignore those)
        if arc::strong_count(&self.data) == 1 {
            let vec_ptr: &mut Vec<T> = unsafe { mem::transmute(&*self.data) };
            Ok(mem::replace(vec_ptr, Vec::new()))
        } else {
            Err(self)
        }
    }

    /// Take the inner `Vec`, waiting until all slices have been freed.
    pub fn into_inner(mut self) -> Vec<T> {
        loop {
            match self.into_inner_opt() {
                Ok(vec) => return vec,
                Err(new_self) => self = new_self,
            } 
        }
    }
}

fn sub_slices<T>(parent: &[T], slice_count: uint) -> Vec<&[T]> {
    let mut slices = Vec::new();

    let len = parent.len();
    let mut start = 0u;

    for curr in range_inclusive(1, slice_count).rev() {
        let slice_len = (len - start) / curr;
        let end = min(start + slice_len, len);
 
        slices.push(parent.slice(start, end));
        start += slice_len;          
    }

    slices        
}

/// A slice of `ParVec` that can be sent to another task for processing.
/// Automatically releases the slice on drop.
pub struct ParSlice<T: Send> {
    // Just to keep the source vector alive while the slice is,
    // since the ParVec can die asynchronously.
    _vec: Arc<Vec<T>>,
    // This isn't actually &'static but we're guarding it so it's safe.
    data: &'static mut [T],
}

impl<T: Send> Deref<[T]> for ParSlice<T> {
    fn deref<'a>(&'a self) -> &'a [T] {
        self.data    
    }    
}

impl<T: Send> DerefMut<[T]> for ParSlice<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut [T] {
        self.data
    }    
}

impl<T: Send> Show for ParSlice<T> where T: Show {
    fn fmt(&self, f: &mut Formatter) -> Result<(), FmtError> {
        write!(f, "{}", self.data)  
    } 
}

#[cfg(test)]
mod test {
    extern crate test;
    use self::test::Bencher;
    use super::ParVec;
    use std::mem;
    use std::rand::{thread_rng, Rng};
    use std::iter::range_inclusive;
    
    const TEST_SLICES: uint = 8;
    const TEST_MAX: u32 = 1000;

    #[test]
    fn test_unwrap_safely() {
        let (vec, slices) = ParVec::new([5u, ..TEST_MAX as uint].to_vec(), TEST_SLICES);
        mem::drop(slices);

        let vec = vec.into_inner();

        assert_eq!(&*vec, [5u, ..TEST_MAX as uint].as_slice());                            
    }

    #[test]
    fn test_slices() {
        let (_, slices) = ParVec::new(range(1u32, TEST_MAX).collect(), TEST_SLICES);

        assert_eq!(slices.len(), TEST_SLICES);
    }

    #[bench]
    fn seq_prime_factors_1000(b: &mut Bencher) {
        let vec: Vec<u32> = range_inclusive(1, TEST_MAX).collect();

        b.iter(|| {
            let _: Vec<(u32, Vec<u32>)> = vec.iter()
                .map(|&x| (x, get_prime_factors(x)))
                .collect();
        });            
    }

    #[bench]
    fn par_prime_factors_1000(b: &mut Bencher) {
        use std::sync::TaskPool;

        let mut rng = thread_rng();
        let pool = TaskPool::new(TEST_SLICES);

        b.iter(|| {
            let mut vec: Vec<(u32, Vec<u32>)> = range_inclusive(1, TEST_MAX)
                .map(|x| (x, Vec::new())).collect();

            // Shuffle so each thread gets an even distribution of work.
            // Otherwise, the lower threads will quit early.
            rng.shuffle(&mut *vec);

            let (par_vec, par_slices) = ParVec::new(vec, TEST_SLICES);

            for mut slice in par_slices.into_iter() {
                pool.execute(move || 
                    for pair in slice.iter_mut() {
                        let (x, ref mut x_primes) = *pair;
                        *x_primes = get_prime_factors(x);
                    }
                );
            }

            let mut vec = par_vec.into_inner();
            // Sort so they're in the same order as sequential.
            vec.sort();
        });
    }
     
    fn get_prime_factors(x: u32) -> Vec<u32> {
        range(1, x).filter(|&y| x % y == 0 && is_prime(y)).collect()   
    }

    fn is_prime(x: u32) -> bool {
        use std::iter::range_step;

        if x < 3 { return true; }

        if x & 1 == 0 { return false; }

        for i in range_step(3, x, 2) {
            if x % i == 0 { return false; }            
        }

        true          
    }

}

