use alloc::heap::{EMPTY, allocate, reallocate, deallocate};

// Implemented on top of `core` to demonstrate the ability to substitute HybridVec for Vec
use core::borrow::{BorrowFrom, ToOwned};
use core::default::Default;
use core::fmt;
use core::hash::{self, Hash};
use core::intrinsics::forget;
use core::iter;
use core::marker::ContravariantLifetime;
use core::nonzero::NonZero;
use core::mem;
use core::num::{Int, UnsignedInt};
use core::ops;
use core::ptr;
use core::raw::Slice as RawSlice;
use core::usize;

// Make this configurable?
const ARRAY_SIZE: usize = 32;
// The number of bytes a type has to be larger than to automatically be allocated on the heap.
// This limits the on-stack size of `HybridVec` to a maximum of 
// `ARRAY_SIZE * HEAP_BYTES_THRESHOLD`.
const HEAP_BYTES_THRESHOLD: usize = 64;

/// An implementation of `HybridVec` that uses stack-allocated storage below a certain length.
/// A drop-in replacement for `Vec` from the stdlib, with a couple minor changes to the API and internal
/// behavior.
pub enum HybridVec<T> {
    Stack {
        array: [T; ARRAY_SIZE], 
        len: usize,
    },
    Heap {
        ptr: NonZero<*mut T>, 
        len: usize, 
        cap: usize,
    },
}

//#[inline]
fn should_use_heap<T>() -> bool {
    // Determine this based on actual available stack space instead?
    mem::size_of::<T>() > HEAP_BYTES_THRESHOLD   
}

//#[inline]
fn nonzero_ptr<T>() -> NonZero<*mut T> {
    unsafe { NonZero::new(EMPTY as *mut T) }    
}

macro_rules! hybrid_vec [
    // This will need to be adjusted
    [$($elem:expr),*] => (HybridVec::from_boxed_slice(Box::new([$($elem),*])))
];
           
impl<T> HybridVec<T> {
    pub fn new() -> HybridVec<T> {
        // Go directly to heap if the size of the type is greater than our threshold.
        if should_use_heap::<T>() {
            HybridVec::Heap { 
                ptr: nonzero_ptr(),
                len: 0,
                cap: 0,
            } 
        } else {
            HybridVec::Stack {
                // Allocate the stack space for our array.
                // We'll do length checks as usual.
                array: unsafe { mem::uninitialized() },
                len: 0,
            }    
        }
    }

    pub fn with_capacity(cap: usize) -> HybridVec<T> {
        if mem::size_of::<T>() == 0 {
            HybridVec::Heap { ptr: nonzero_ptr(), len: 0, cap: usize::MAX }
        } else if cap > ARRAY_SIZE || should_use_heap::<T>() {
            let size_bytes = cap.checked_mul(mem::size_of::<T>())
                .expect("Capacity overflow!");
            let ptr = unsafe { allocate(size_bytes, mem::min_align_of::<T>()) };
            if ptr.is_null() { ::alloc::oom() }

            HybridVec::Heap {
                ptr: unsafe { NonZero::new(ptr as *mut T) },
                len: 0,
                cap: cap,
            }                
        } else {
            HybridVec::Stack {
                array: unsafe { mem::uninitialized() },
                len: 0,
            }  
        }
    }

    /// Necessary because `SliceExt::into_vec` goes directly into `Vec`.
    pub fn from_boxed_slice(mut slice: Box<[T]>) -> HybridVec<T> {
        unsafe { 
            let vec = HybridVec::from_raw_parts(slice.as_mut_ptr(), slice.len(), slice.len());
            mem::forget(slice);
            vec
        }    
    }
        
    pub unsafe fn from_raw_parts(ptr: *mut T, length: usize, capacity: usize) -> HybridVec<T> {
        HybridVec::Heap { ptr: NonZero::new(ptr), len: length, cap: capacity }
    }
    
    pub unsafe fn from_raw_buf(ptr: *const T, elts: usize) -> HybridVec<T> {
        let mut dst = HybridVec::with_capacity(elts);
        dst.set_len(elts);
        ptr::copy_nonoverlapping_memory(dst.as_mut_ptr(), ptr, elts);
        dst
    }

    #[inline]
    pub fn len(&self) -> usize {
        match *self {
            HybridVec::Heap {  ptr: _, len, cap: _ } => len,
            HybridVec::Stack { array: _, len } => len,    
        }    
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        match *self {
            HybridVec::Heap { ptr: _, len: _, cap } => cap,
            HybridVec::Stack { array: _, len: _ } => ARRAY_SIZE,    
        }    
    }
    
    pub fn insert(&mut self, index: usize, element: T) {
        let len = self.len();
        assert!(index <= len);
        // space for the new element
        self.reserve(1);

        unsafe { // infallible
            // The spot to put the new value
            {
                let p = self.as_mut_ptr().offset(index as isize);
                // Shift everything over to make space. (Duplicating the
                // `index`th element into two consecutive places.)
                ptr::copy_memory(p.offset(1), &*p, len - index);
                // Write it in, overwriting the first copy of the `index`th
                // element.
                ptr::write(&mut *p, element);
            }
            self.set_len(len + 1);
        }
    }

    pub fn remove(&mut self, index: usize) -> T {
        let len = self.len();
        assert!(index < len);
        unsafe { // infallible
            let ret;
            {
                // the place we are taking from.
                let ptr = self.as_mut_ptr().offset(index as isize);
                // copy it out, unsafely having a copy of the value on
                // the stack and in the vector at the same time.
                ret = ptr::read(ptr as *const T);

                // Shift everything down to fill in that spot.
                ptr::copy_memory(ptr, &*ptr.offset(1), len - index - 1);
            }
            self.set_len(len - 1);
            ret
        }
    }
    
    //#[inline]
    pub fn push(&mut self, value: T) {
        if mem::size_of::<T>() == 0 {
            // zero-size types consume no memory, so we can't rely on the
            // address space running out.
            // This will automatically use the heap variant.
            unsafe {                
                let new_len = self.len().checked_add(1).expect("length overflow");
                self.set_len(new_len);
                mem::forget(value); 
            }
            return
        }
        
        // `HybridVec::push()` had some weird reallocation logic that wasn't explained in the code
        // and didn't seem to change much except the growth rate of `HybridVec`.
        // This should suffice unless the old behavior is shown to be preferiential.
        self.reserve(1);

        unsafe {
            let len = self.len();
            let end = self.as_mut_ptr().offset(len as isize);
            ptr::write(&mut *end, value);
            self.set_len(len + 1);
        }
    }

    //#[inline]
    pub fn pop(&mut self) -> Option<T> {
        if self.len() == 0 { return None }
        
        let new_len = self.len() - 1;

        unsafe { 
            self.set_len(new_len);
            Some(ptr::read(self.get_unchecked(self.len())))
        }    
    }
    
    pub fn truncate(&mut self, len: usize) {
        unsafe {
            // drop any extra elements
            while len < self.len() {
                let curr_len = self.len();
                // decrement len before the read(), so a panic on Drop doesn't
                // re-drop the just-failed value.
                self.set_len(curr_len - 1);
                ptr::read(self.get_unchecked(self.len()));
            }
        }
    }

    pub unsafe fn set_len(&mut self, new_len: usize) {
        match *self {
            HybridVec::Heap { ptr: _, ref mut len, cap: _ } => *len = new_len,
            HybridVec::Stack { array: _, ref mut len } => *len = new_len,
        }
    }
    
    pub fn reserve(&mut self, additional: usize) {
        if self.capacity() - self.len() < additional {
            let err_msg = "HybridVec::reserve: `usize` overflow";
            let new_cap = self.len().checked_add(additional).expect(err_msg)
                .checked_next_power_of_two().expect(err_msg);
            self.grow_capacity(new_cap);
        }
    }
    
    fn grow_capacity(&mut self, capacity: usize) {
        if mem::size_of::<T>() == 0 { return }

        if capacity > self.capacity() {
            if self.is_stack() {
                self.move_to_heap(capacity);    
            } else if let HybridVec::Heap { ref mut ptr, len: _, ref mut cap} = *self {
               
                let size = capacity.checked_mul(mem::size_of::<T>())
                               .expect("capacity overflow");
                unsafe {
                    let new_ptr = alloc_or_realloc(**ptr, *cap * mem::size_of::<T>(), size);
                    if ptr.is_null() { ::alloc::oom() }
                    *ptr = NonZero::new(new_ptr);
                }
                *cap = capacity;
            }
        }
    }

    //#[inline]
    fn is_stack(&self) -> bool {
        match *self {
            HybridVec::Stack { array: _, len: _ } => true,
            _ => false,    
        } 
    }
    
    /// Move to the heap if the new capacity requirement is too big for the stack
    fn move_to_heap(&mut self, capacity: usize) {
        // Sanity checks
        if !self.is_stack() { return }
        
        unsafe { 
            let temp = mem::replace(self, HybridVec::with_capacity(capacity));
            
            if let HybridVec::Stack { ref array, len } = temp {
                ptr::copy_nonoverlapping_memory(self.as_mut_ptr(), array.as_ptr(), len);
                self.set_len(len);
            }
            
            forget(temp);                       
        }
    }

    /// Move back to the stack if the vector can fit
    fn move_to_stack(&mut self) {
        if self.is_stack() || self.len() > ARRAY_SIZE || should_use_heap::<T>() { return }

        unsafe {
            let temp = mem::replace(self, HybridVec::new());
            self.set_len(temp.len());
            ptr::copy_nonoverlapping_memory(self.as_mut_ptr(), temp.as_ptr(), temp.len());
            
            if let HybridVec::Heap { ptr, cap, len: _ } = temp {
                dealloc(*ptr, cap);
            }

            forget(temp);
        }
    }

    pub fn as_mut_slice<'a>(&'a mut self) -> &'a mut [T] {
        match *self {
            HybridVec::Heap { ptr, len, cap: _ } => unsafe {
                mem::transmute(RawSlice {
                    data: *ptr as *const T,
                    len: len,
                })
            },
            HybridVec::Stack { ref mut array, len } => &mut array[..len],                     
        } 
    }
    
    pub fn into_iter(self) -> IntoIter<T> {
        let ret = match self {
            HybridVec::Stack { ref array, len } => {
                let array = unsafe { ptr::read(array) };
                
                IntoIter::Stack {
                    array: array,
                    curr: 0,
                    len: len,
                }
            },
            HybridVec::Heap { ptr, len, cap } => {        
                let end = if mem::size_of::<T>() == 0 {
                    (*ptr as usize + len) as *const T
                } else {
                    unsafe { ptr.offset(len as isize) as *const T }
                };
                    
                IntoIter::Heap {
                    ptr: *ptr,
                    cap: cap,
                    curr: *ptr as *const T,
                    end: end,
                }
            },
        };
        
        unsafe { mem::forget(self) }
        
        ret                   
    }

    pub fn retain<F>(&mut self, mut f: F) where F: FnMut(&T) -> bool {
        let len = self.len();
        let mut del = 0us;
        {
            let v = self.as_mut_slice();

            for i in range(0us, len) {
                if !f(&v[i]) {
                    del += 1;
                } else if del > 0 {
                    v.swap(i-del, i);
                }
            }
        }
        if del > 0 {
            self.truncate(len - del);
        }    
    }
    
    //#[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        let length = self.len();
        self.swap(index, length - 1);
        self.pop().unwrap()
    }
    
    pub fn into_boxed_slice(mut self) -> Box<[T]> {
        if self.is_stack() {
            let cap = self.len();
            self.move_to_heap(cap);
        } else {
            self.shrink_to_fit(false);
        }

        unsafe {
            let xs: Box<[T]> = mem::transmute(self.as_mut_slice());
            mem::forget(self);
            xs
        }
    }
    
    pub fn shrink_to_fit(&mut self, move_to_stack: bool) {
        if mem::size_of::<T>() == 0 { return }

        match *self {
            HybridVec::Stack { array: _, len: _ } => (),
            HybridVec::Heap { ptr: _, cap:_ , len } if len < ARRAY_SIZE && move_to_stack => self.move_to_stack(),
            HybridVec::Heap { ref mut ptr, ref mut cap, len } => unsafe {
                // Overflow check is unnecessary as the vector is already at
                // least this large.
                let new_ptr = reallocate(
                    **ptr as *mut u8,
                    *cap * mem::size_of::<T>(),
                    len * mem::size_of::<T>(),
                    mem::min_align_of::<T>()
                ) as *mut T;

                if new_ptr.is_null() { ::alloc::oom() }
                *ptr = NonZero::new(new_ptr);
                *cap = len;
            }
        }
    }

    //#[inline]
    pub fn append(&mut self, other: &mut Self) {
        if mem::size_of::<T>() == 0 {
            // zero-size types consume no memory, so we can't rely on the
            // address space running out
            let new_len = self.len().checked_add(other.len()).expect("length overflow");
            unsafe { 
                self.set_len(new_len);
                other.set_len(0);
            }
            return;
        }
        self.reserve(other.len());
        let len = self.len();
        unsafe {
            ptr::copy_nonoverlapping_memory(
                self.get_unchecked_mut(len),
                other.as_ptr(),
                other.len());
        }
    
        let new_len = self.len() + other.len();
        unsafe {
            self.set_len(new_len);
            other.set_len(0); 
        }
    }

    pub fn drain<'a>(&'a mut self) -> Drain<'a, T> {
        match *self {
            HybridVec::Stack { ref mut array, len } => Drain::Stack { array: array, curr: 0, len: len },
            HybridVec::Heap { ptr, cap: _, len } => 
            Drain::Heap { 
                curr: *ptr as *const T,
                end: unsafe { ptr.offset(len as isize) },
                marker: ContravariantLifetime,
            },
        }
    }
}

impl<T> HybridVec<T> where T: Clone {

    pub fn resize(&mut self, new_len: usize, val: T) {
        let len = self.len();
        
        if new_len > len {
            self.extend(iter::repeat(val).take(new_len - len));    
        } else {
            self.truncate(new_len);
        }
    }

    pub fn push_all(&mut self, other: &[T]) {
        self.extend(other.iter().cloned())    
    }
}

impl<T> Clone for HybridVec<T> where T: Clone {
    fn clone(&self) -> HybridVec<T> {
        self.iter().cloned().collect()
    }
    
    fn clone_from(&mut self, other: &HybridVec<T>) {
        if self.len() > other.len() {
            self.truncate(other.len());    
        }

        for (place, thing) in self.iter_mut().zip(other.iter()) {
            place.clone_from(thing)    
        }

        let slice = &other[self.len()..];
        self.push_all(slice);
    }    
}

impl<T> Default for HybridVec<T> {
    fn default() -> HybridVec<T> {
        HybridVec::new()    
    }    
}

impl<T> ToOwned<HybridVec<T>> for [T] where T: Clone {
    fn to_owned(&self) -> HybridVec<T> {
        let mut vec = HybridVec::new();
        vec.extend(self.iter().cloned());
        vec    
    }    
}

impl<T> AsSlice<T> for HybridVec<T> {
    fn as_slice<'a>(&'a self) -> &[T] {
        match *self {
            HybridVec::Heap { ptr, len, cap: _ } => unsafe {
                mem::transmute(RawSlice {
                    data: *ptr as *const T,
                    len: len,
                })
            },
            HybridVec::Stack { ref array, len } => &array[..len],                     
        }
    }
}

impl<T> BorrowFrom<HybridVec<T>> for [T] {
    fn borrow_from(owned: &HybridVec<T>) -> &[T] {
        &**owned    
    }    
}

impl<T> ops::Deref for HybridVec<T> {
    type Target = [T];

    fn deref<'a>(&'a self) -> &'a [T] { self.as_slice() }    
}

impl<T> ops::DerefMut for HybridVec<T> {
    fn deref_mut<'a>(&'a mut self) -> &'a mut [T] { self.as_mut_slice() }
}

impl<T> fmt::Debug for HybridVec<T> where T: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)    
    }    
}

impl<S: hash::Writer + hash::Hasher, T: Hash<S>> Hash<S> for HybridVec<T> {
    //#[inline]
    fn hash(&self, state: &mut S) {
        self.as_slice().hash(state);
    }
}

impl<A, B> PartialEq<HybridVec<B>> for HybridVec<A> where A: PartialEq<B> {
    //#[inline]
    fn eq(&self, other: &HybridVec<B>) -> bool { PartialEq::eq(&**self, &**other) }
    //#[inline]
    fn ne(&self, other: &HybridVec<B>) -> bool { PartialEq::ne(&**self, &**other) }
}

macro_rules! impl_eq {
    ($lhs:ty, $rhs:ty) => {
        impl<'b, A, B> PartialEq<$rhs> for $lhs where A: PartialEq<B> {
            //#[inline]
            fn eq(&self, other: &$rhs) -> bool { PartialEq::eq(&**self, &**other) }
            //#[inline]
            fn ne(&self, other: &$rhs) -> bool { PartialEq::ne(&**self, &**other) }
        }

        impl<'b, A, B> PartialEq<$lhs> for $rhs where B: PartialEq<A> {
            //#[inline]
            fn eq(&self, other: &$lhs) -> bool { PartialEq::eq(&**self, &**other) }
            //#[inline]
            fn ne(&self, other: &$lhs) -> bool { PartialEq::ne(&**self, &**other) }
        }
    }
}

impl_eq! { HybridVec<A>, &'b [B] }
impl_eq! { HybridVec<A>, &'b mut [B] }

#[inline(never)]
unsafe fn alloc_or_realloc<T>(ptr: *mut T, old_size: usize, size: usize) -> *mut T {
    if old_size == 0 {
        allocate(size, mem::min_align_of::<T>()) as *mut T
    } else {
        reallocate(ptr as *mut u8, old_size, size, mem::min_align_of::<T>()) as *mut T
    }
}

//#[inline]
unsafe fn dealloc<T>(ptr: *mut T, len: usize) {
    if mem::size_of::<T>() != 0 {
        deallocate(ptr as *mut u8,
                   len * mem::size_of::<T>(),
                   mem::min_align_of::<T>())
    }
}

impl<T> Extend<T> for HybridVec<T> {
    fn extend<I: Iterator<Item=T>>(&mut self, mut iter: I) {
        let (lower, _) = iter.size_hint();
        self.reserve(lower);
        for elem in iter {
            self.push(elem)    
        }    
    }
}

impl<T> iter::FromIterator<T> for HybridVec<T> {
    fn from_iter<I: Iterator<Item=T>>(iter: I) -> HybridVec<T> {
        let mut vec = HybridVec::new();
        vec.extend(iter);
        vec
    }    
}

impl<T> ops::Index<usize> for HybridVec<T> {
    type Output = T;
    //#[inline]
    fn index(&self, index: &usize) -> &T {
        self.as_slice().index(index)   
    }
}

impl<T> ops::Index<ops::Range<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index(&self, index: &ops::Range<usize>) -> &[T] {
        self.as_slice().index(index)
    }
}

impl<T> ops::Index<ops::RangeTo<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index(&self, index: &ops::RangeTo<usize>) -> &[T] {
        self.as_slice().index(index)
    }
}

impl<T> ops::Index<ops::RangeFrom<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index(&self, index: &ops::RangeFrom<usize>) -> &[T] {
        self.as_slice().index(index)
    }
}

impl<T> ops::Index<ops::FullRange> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index(&self, _index: &ops::FullRange) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::IndexMut<usize> for HybridVec<T> {
    type Output = T;
    //#[inline]
    fn index_mut(&mut self, index: &usize) -> &mut T {
        self.as_mut_slice().index_mut(index)
    }    
}

impl<T> ops::IndexMut<ops::Range<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index_mut(&mut self, index: &ops::Range<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::RangeTo<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index_mut(&mut self, index: &ops::RangeTo<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::RangeFrom<usize>> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index_mut(&mut self, index: &ops::RangeFrom<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::FullRange> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index_mut(&mut self, _index: &ops::FullRange) -> &mut [T] {
        self.as_mut_slice()
    }
}

#[unsafe_destructor]
impl<T> Drop for HybridVec<T> {
    fn drop(&mut self) {
        if self.capacity() == 0 { return }

        unsafe {
            // We zero self here so the drop glue knows not to run the dtor again
            let temp = mem::replace(self, mem::zeroed());

            for x in temp.iter() {
                ptr::read(x);    
            }

            match temp {
                HybridVec::Heap { ptr, len: _, cap } => dealloc(*ptr, cap),
                _ => (),
            }

            forget(temp);
        }
    }
}

pub enum IntoIter<T> {
    Stack {
        array: [T; ARRAY_SIZE],
        curr: usize,
        len: usize,
    },
    Heap {
        ptr: *mut T,
        cap: usize,
        curr: *const T,
        end: *const T,
    },
}

impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<T> {
        match *self {
            IntoIter::Stack { ref array, ref mut curr, len } if *curr != len => { 
                let ret = unsafe { ptr::read(&array[*curr]) };
                *curr += 1;
                Some(ret)
            },
            IntoIter::Heap { ptr: _, cap: _, ref mut curr, end } if *curr != end => unsafe {
                if mem::size_of::<T>() == 0 {
                    *curr = mem::transmute(*curr as usize + 1);
                    return Some(ptr::read(mem::transmute(1us)));
                }

                let ret = ptr::read(*curr);
                *curr = curr.offset(1);
                Some(ret)
            },
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = match *self {
            IntoIter::Stack { array: _, curr, len } => len - curr,
            IntoIter::Heap { ptr: _, cap: _, curr, end } => {
                let diff = (end as usize) - (curr as usize);
                let size = mem::size_of::<T>();
                diff / (if size == 0 {1} else {size})
            }
        };
        
        (exact, Some(exact))  
    }
}

impl<T> DoubleEndedIterator for IntoIter<T> {
    //#[inline]
    fn next_back<'a>(&'a mut self) -> Option<T> {
        match *self {
            IntoIter::Stack { ref mut array, curr, ref mut len } if curr != *len => {
                *len -= 1;
                Some(unsafe { ptr::read(&array[*len]) })
            },
            IntoIter::Heap { ptr: _, cap: _, curr, ref mut end } if curr != *end => unsafe {
                if mem::size_of::<T>() == 0 {
                    *end = mem::transmute(*end as usize - 1);
                    Some(ptr::read(mem::transmute(1us)))
                } else {
                    *end = end.offset(-1);
                    Some(ptr::read(mem::transmute(*end)))
                }
            },
            _ => None,
        }
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> IntoIter<T> { 
    pub fn into_inner(mut self) -> HybridVec<T> {
        for _ in self {}

        let ret = match self {
            IntoIter::Stack { ref array, curr: _, len: _ } =>
            HybridVec::Stack {
                array: unsafe { ptr::read(array) },
                len: 0,
            },
            IntoIter::Heap { ptr, cap, curr: _, end: _, } => unsafe { 
                HybridVec::from_raw_parts(ptr, cap, 0) 
            },
        };

        unsafe { mem::forget(self); }
        ret
    }    
}

#[unsafe_destructor]
impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        for _ in *self {}

        unsafe { 
            let temp = mem::replace(self, mem::zeroed());
            match temp {
                IntoIter::Heap { ptr, cap, curr: _, end: _ } if cap != 0 => dealloc(ptr, cap),
                _ => (),
            }

            mem::forget(temp);
        }     
    }    
}

pub enum Drain<'a, T: 'a> {
    Stack {
        array: &'a mut [T],
        curr: usize,
        len: usize,
    },
    Heap {
        curr: *const T,
        end: *const T,
        marker: ContravariantLifetime<'a>,
    } 
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    //#[inline]
    fn next(&mut self) -> Option<T> {
        match *self {
            Drain::Stack { ref array, ref mut curr, len } if *curr != len => {
                let ret = unsafe { ptr::read(&array[*curr]) };
                *curr += 1;
                Some(ret)
            },
            Drain::Heap { ref mut curr, end, marker: _ } if *curr != end => unsafe {
                if mem::size_of::<T>() == 0 {
                    *curr = mem::transmute(*curr as usize + 1);
                    return Some(ptr::read(mem::transmute(1us)));
                }

                let ret = ptr::read(*curr);
                *curr = curr.offset(1);
                Some(ret)    
            },
            _ => None,
        }
    }

    //#[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let exact = match *self {
            Drain::Stack { array: _, curr, len } => len - curr,
            Drain::Heap { curr, end, marker: _ } => {
                let diff = (end as usize) - (curr as usize);
                let size = mem::size_of::<T>();
                diff / (if size == 0 {1} else {size})
            },
        };

        (exact, Some(exact))                
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    //#[inline]
    fn next_back(&mut self) -> Option<T> {
        match *self {
            Drain::Stack { ref array, curr, ref mut len } if curr != *len => {
                *len -= 1;
                Some(unsafe { ptr::read(&array[*len]) })
            },
            Drain::Heap { curr, ref mut end, marker: _ } if curr != *end => unsafe {
                if mem::size_of::<T>() == 0 {
                    *end = mem::transmute(*end as usize - 1);
                    return Some(ptr::read(mem::transmute(1us)));
                }

                *end = end.offset(-1);
                Some(ptr::read(*end))
            },
            _ => None,
        }
    }
}

impl<'a, T> ExactSizeIterator for Drain<'a, T> {}

#[unsafe_destructor]
impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        for _ in *self {}    
    }    
}

#[cfg(test)]
mod tests {
    use core::iter::{FromIterator, repeat};
    use core::ops::FullRange;
    use test::Bencher;

    use super::HybridVec;

    struct DropCounter<'a> {
        count: &'a mut isize
    }

    #[unsafe_destructor]
    impl<'a> Drop for DropCounter<'a> {
        fn drop(&mut self) {
            *self.count += 1;
        }
    }

    #[test]
    fn test_drop_empty() {
        let _: HybridVec<()> = HybridVec::new();    
    }

    #[test]
    fn test_double_drop() {
        struct TwoVec<T> {
            x: HybridVec<T>,
            y: HybridVec<T>
        }

        let (mut count_x, mut count_y) = (0, 0);
        {
            let mut tv = TwoVec {
                x: HybridVec::new(),
                y: HybridVec::new()
            };
            tv.x.push(DropCounter {count: &mut count_x});
            tv.y.push(DropCounter {count: &mut count_y});

            // If Vec had a drop flag, here is where it would be zeroed.
            // Instead, it should rely on its internal state to prevent
            // doing anything significant when dropped multiple times.
            drop(tv.x);

            // Here tv goes out of scope, tv.y should be dropped, but not tv.x.
        }

        assert_eq!(count_x, 1);
        assert_eq!(count_y, 1);
    }

    #[test]
    fn test_reserve() {
        let mut v = HybridVec::new();
        //This assert will fail because the on-stack capacity is 64.
        //assert_eq!(v.capacity(), 0);

        v.reserve(2);
        assert!(v.capacity() >= 2);

        for i in range(0is, 16) {
            v.push(i);
        }

        assert!(v.capacity() >= 16);
        v.reserve(16);
        assert!(v.capacity() >= 32);

        v.push(16);

        v.reserve(16);
        assert!(v.capacity() >= 33)
    }

    #[test]
    fn test_extend() {
        let mut v = HybridVec::new();
        let mut w = HybridVec::new();

        v.extend(range(0is, 3));
        for i in range(0is, 3) { w.push(i) }

        assert_eq!(v, w);

        v.extend(range(3is, 10));
        for i in range(3is, 10) { w.push(i) }

        assert_eq!(v, w);
    }

    #[test]
    fn test_slice_from_mut() {
        let mut values = hybrid_vec![1u8,2,3,4,5];
        {
            let slice = &mut values[2..];
            assert!(slice == [3, 4, 5]);
            for p in slice.iter_mut() {
                *p += 2;
            }
        }

        assert!(values == [1, 2, 5, 6, 7]);
    }

    #[test]
    fn test_slice_to_mut() {
        let mut values = hybrid_vec![1u8,2,3,4,5];
        {
            let slice = &mut values[..2];
            assert!(slice == [1, 2]);
            for p in slice.iter_mut() {
                *p += 1;
            }
        }

        assert!(values == [2, 3, 3, 4, 5]);
    }

    #[test]
    fn test_split_at_mut() {
        let mut values = hybrid_vec![1u8,2,3,4,5];
        {
            let (left, right) = values.split_at_mut(2);
            {
                let left: &[_] = left;
                assert!(&left[..left.len()] == &[1, 2][]);
            }
            for p in left.iter_mut() {
                *p += 1;
            }

            {
                let right: &[_] = right;
                assert!(&right[..right.len()] == &[3, 4, 5][]);
            }
            for p in right.iter_mut() {
                *p += 2;
            }
        }

        assert!(values == hybrid_vec![2u8, 3, 5, 6, 7]);
    }

    #[test]
    fn test_clone() {
        let v: HybridVec<isize> = hybrid_vec!();
        let w = hybrid_vec!(1is, 2, 3);

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);
        // they should be disjoint in memory.
        assert!(w.as_ptr() != z.as_ptr())
    }

    #[test]
    fn test_clone_from() {
        let mut v = hybrid_vec!();
        let three = hybrid_vec!(box 1is, box 2, box 3);
        let two = hybrid_vec!(box 4is, box 5);
        // zero, long
        v.clone_from(&three);
        assert_eq!(v, three);

        // equal
        v.clone_from(&three);
        assert_eq!(v, three);

        // long, short
        v.clone_from(&two);
        assert_eq!(v, two);

        // short, long
        v.clone_from(&three);
        assert_eq!(v, three)
    }

    #[test]
    fn test_retain() {
        let mut vec = hybrid_vec![1us, 2, 3, 4];
        vec.retain(|&x| x % 2 == 0);
        assert!(vec == hybrid_vec![2us, 4]);
    }

    #[test]
    fn zero_sized_values() {
        let mut v = HybridVec::new();
        assert_eq!(v.len(), 0);
        v.push(());
        assert_eq!(v.len(), 1);
        v.push(());
        assert_eq!(v.len(), 2);
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), Some(()));
        assert_eq!(v.pop(), None);

        assert_eq!(v.iter().count(), 0);
        v.push(());
        assert_eq!(v.iter().count(), 1);
        v.push(());
        assert_eq!(v.iter().count(), 2);

        for &() in v.iter() {}

        assert_eq!(v.iter_mut().count(), 2);
        v.push(());
        assert_eq!(v.iter_mut().count(), 3);
        v.push(());
        assert_eq!(v.iter_mut().count(), 4);

        for &mut () in v.iter_mut() {}
        unsafe { v.set_len(0); }
        assert_eq!(v.iter_mut().count(), 0);
    }

    #[test]
    fn test_partition() {
        assert_eq!(hybrid_vec![].into_iter().partition(|x: &isize| *x < 3), (hybrid_vec![], hybrid_vec![]));
        assert_eq!(hybrid_vec![1is, 2, 3].into_iter().partition(|x: &isize| *x < 4), (hybrid_vec![1, 2, 3], hybrid_vec![]));
        assert_eq!(hybrid_vec![1is, 2, 3].into_iter().partition(|x: &isize| *x < 2), (hybrid_vec![1], hybrid_vec![2, 3]));
        assert_eq!(hybrid_vec![1is, 2, 3].into_iter().partition(|x: &isize| *x < 0), (hybrid_vec![], hybrid_vec![1, 2, 3]));
    }

    #[test]
    fn test_zip_unzip() {
        let z1 = hybrid_vec![(1is, 4is), (2, 5), (3, 6)];

        let (left, right): (HybridVec<_>, HybridVec<_>) = z1.iter().map(|&x| x).unzip();

        assert_eq!((1, 4), (left[0], right[0]));
        assert_eq!((2, 5), (left[1], right[1]));
        assert_eq!((3, 6), (left[2], right[2]));
    }

    #[test]
    fn test_unsafe_ptrs() {
        unsafe {
            // Test on-stack copy-from-buf.
            let a = [1is, 2, 3];
            let ptr = a.as_ptr();
            let b = HybridVec::from_raw_buf(ptr, 3us);
            assert_eq!(b, hybrid_vec![1, 2, 3]);

            // Test on-heap copy-from-buf.
            let c = hybrid_vec![1is, 2, 3, 4, 5];
            let ptr = c.as_ptr();
            let d = HybridVec::from_raw_buf(ptr, 5us);
            assert_eq!(d, hybrid_vec![1, 2, 3, 4, 5]);
        }
    }

    #[test]
    fn test_vec_truncate_drop() {
        static mut drops: usize = 0;
        struct Elem(isize);
        impl Drop for Elem {
            fn drop(&mut self) {
                unsafe { drops += 1; }
            }
        }

        let mut v = hybrid_vec![Elem(1), Elem(2), Elem(3), Elem(4), Elem(5)];
        assert_eq!(unsafe { drops }, 0);
        v.truncate(3);
        assert_eq!(unsafe { drops }, 2);
        v.truncate(0);
        assert_eq!(unsafe { drops }, 5);
    }

    #[test]
    #[should_fail]
    fn test_vec_truncate_fail() {
        struct BadElem(isize);
        impl Drop for BadElem {
            fn drop(&mut self) {
                let BadElem(ref mut x) = *self;
                if *x == 0xbadbeef {
                    panic!("BadElem panic: 0xbadbeef")
                }
            }
        }

        let mut v = hybrid_vec![BadElem(1), BadElem(2), BadElem(0xbadbeef), BadElem(4)];
        v.truncate(0);
    }

    #[test]
    fn test_index() {
        let vec = hybrid_vec!(1is, 2, 3);
        assert!(vec[1] == 2);
    }

    #[test]
    #[should_fail]
    fn test_index_out_of_bounds() {
        let vec = hybrid_vec!(1is, 2, 3);
        let _ = vec[3];
    }

    #[test]
    #[should_fail]
    fn test_slice_out_of_bounds_1() {
        let x: HybridVec<isize> = hybrid_vec![1, 2, 3, 4, 5];
        &x[-1..];
    }

    #[test]
    #[should_fail]
    fn test_slice_out_of_bounds_2() {
        let x: HybridVec<isize> = hybrid_vec![1, 2, 3, 4, 5];
        &x[..6];
    }

    #[test]
    #[should_fail]
    fn test_slice_out_of_bounds_3() {
        let x: HybridVec<isize> = hybrid_vec![1, 2, 3, 4, 5];
        &x[-1..4];
    }

    #[test]
    #[should_fail]
    fn test_slice_out_of_bounds_4() {
        let x: HybridVec<isize> = hybrid_vec![1, 2, 3, 4, 5];
        &x[1..6];
    }

    #[test]
    #[should_fail]
    fn test_slice_out_of_bounds_5() {
        let x: HybridVec<isize> = hybrid_vec![1, 2, 3, 4, 5];
        &x[3..2];
    }

    #[test]
    #[should_fail]
    fn test_swap_remove_empty() {
        let mut vec: HybridVec<usize> = hybrid_vec!();
        vec.swap_remove(0);
    }

    #[test]
    fn test_move_iter_unwrap() {
        let mut vec: HybridVec<usize> = HybridVec::with_capacity(7);
        vec.push(1);
        vec.push(2);
        let ptr = vec.as_ptr();
        vec = vec.into_iter().into_inner();
        assert_eq!(vec.as_ptr(), ptr);
        // This assert will fail because the vector is on-stack.
        //assert_eq!(vec.capacity(), 7);
        assert_eq!(vec.len(), 0);
    }
 
    #[test]
    fn test_move_items() {
        let vec = hybrid_vec![1, 2, 3];
        let mut vec2 : HybridVec<i32> = hybrid_vec![];
        for i in vec.into_iter() {
            vec2.push(i);
        }
        assert!(vec2 == hybrid_vec![1, 2, 3]);
    }

    #[test]
    fn test_move_items_reverse() {
        let vec = hybrid_vec![1, 2, 3];
        let mut vec2 : HybridVec<i32> = hybrid_vec![];
        for i in vec.into_iter().rev() {
            vec2.push(i);
        }
        assert!(vec2 == hybrid_vec![3, 2, 1]);
    }

    #[test]
    fn test_move_items_zero_sized() {
        let vec = hybrid_vec![(), (), ()];
        let mut vec2 : HybridVec<()> = hybrid_vec![];
        for i in vec.into_iter() {
            vec2.push(i);
        }
        assert_eq!(vec2, hybrid_vec![(), (), ()]);
    }
    
    #[test]
    fn test_drain_items() {
        let mut vec = vec![1, 2, 3];
        let mut vec2: Vec<i32> = vec![];
        for i in vec.drain() {
            vec2.push(i);
        }
        assert_eq!(vec, []);
        assert_eq!(vec2, [ 1, 2, 3 ]);
    }

    #[test]
    fn test_drain_items_reverse() {
        let mut vec = vec![1, 2, 3];
        let mut vec2: Vec<i32> = vec![];
        for i in vec.drain().rev() {
            vec2.push(i);
        }
        assert_eq!(vec, []);
        assert_eq!(vec2, [ 3, 2, 1 ]);
    }

    #[test]
    fn test_drain_items_zero_sized() {
        let mut vec = vec![(), (), ()];
        let mut vec2: Vec<()> = vec![];
        for i in vec.drain() {
            vec2.push(i);
        }
        assert_eq!(vec, []);
        assert_eq!(vec2, [(), (), ()]);
    }
 
    #[test]
    fn test_into_boxed_slice() {
        let xs = hybrid_vec![1us, 2, 3];
        let ys = xs.into_boxed_slice();
        assert_eq!(ys.as_slice(), [1us, 2, 3]);
    }

    #[test]
    fn test_append() {
        let mut vec = hybrid_vec![1, 2, 3];
        let mut vec2 = hybrid_vec![4, 5, 6];
        vec.append(&mut vec2);
        assert_eq!(vec, hybrid_vec![1, 2, 3, 4, 5, 6]);
        assert_eq!(vec2, hybrid_vec![]);
    }

    #[bench]
    fn bench_new(b: &mut Bencher) {
        b.iter(|| {
            let v: HybridVec<usize> = HybridVec::new();
            assert_eq!(v.len(), 0);
            // Will fail because initial capacity is 64 (on-stack)
            //assert_eq!(v.capacity(), 0);
        })
    }

    fn do_bench_with_capacity(b: &mut Bencher, src_len: usize) {
        b.bytes = src_len as u64;

        b.iter(|| {
            let v: HybridVec<usize> = HybridVec::with_capacity(src_len);
            assert_eq!(v.len(), 0);
            //This may not be the same as src_len
            //assert_eq!(v.capacity(), src_len);
        })
    }

    #[bench]
    fn bench_with_capacity_0000(b: &mut Bencher) {
        do_bench_with_capacity(b, 0)
    }

    #[bench]
    fn bench_with_capacity_0010(b: &mut Bencher) {
        do_bench_with_capacity(b, 10)
    }

    #[bench]
    fn bench_with_capacity_0100(b: &mut Bencher) {
        do_bench_with_capacity(b, 100)
    }

    #[bench]
    fn bench_with_capacity_1000(b: &mut Bencher) {
        do_bench_with_capacity(b, 1000)
    }

    fn do_bench_from_fn(b: &mut Bencher, src_len: usize) {
        b.bytes = src_len as u64;

        b.iter(|| {
            let dst = range(0, src_len).collect::<HybridVec<_>>();
            assert_eq!(dst.len(), src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        })
    }

    #[bench]
    fn bench_from_fn_0000(b: &mut Bencher) {
        do_bench_from_fn(b, 0)
    }

    #[bench]
    fn bench_from_fn_0010(b: &mut Bencher) {
        do_bench_from_fn(b, 10)
    }

    #[bench]
    fn bench_from_fn_0100(b: &mut Bencher) {
        do_bench_from_fn(b, 100)
    }

    #[bench]
    fn bench_from_fn_1000(b: &mut Bencher) {
        do_bench_from_fn(b, 1000)
    }

    fn do_bench_from_elem(b: &mut Bencher, src_len: usize) {
        b.bytes = src_len as u64;

        b.iter(|| {
            let dst: HybridVec<usize> = repeat(5).take(src_len).collect();
            assert_eq!(dst.len(), src_len);
            assert!(dst.iter().all(|x| *x == 5));
        })
    }

    #[bench]
    fn bench_from_elem_0000(b: &mut Bencher) {
        do_bench_from_elem(b, 0)
    }

    #[bench]
    fn bench_from_elem_0010(b: &mut Bencher) {
        do_bench_from_elem(b, 10)
    }

    #[bench]
    fn bench_from_elem_0100(b: &mut Bencher) {
        do_bench_from_elem(b, 100)
    }

    #[bench]
    fn bench_from_elem_1000(b: &mut Bencher) {
        do_bench_from_elem(b, 1000)
    }

    fn do_bench_from_slice(b: &mut Bencher, src_len: usize) {
        let src: HybridVec<usize> = FromIterator::from_iter(range(0, src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let dst = src.clone()[].to_vec();
            assert_eq!(dst.len(), src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_from_slice_0000(b: &mut Bencher) {
        do_bench_from_slice(b, 0)
    }

    #[bench]
    fn bench_from_slice_0010(b: &mut Bencher) {
        do_bench_from_slice(b, 10)
    }

    #[bench]
    fn bench_from_slice_0100(b: &mut Bencher) {
        do_bench_from_slice(b, 100)
    }

    #[bench]
    fn bench_from_slice_1000(b: &mut Bencher) {
        do_bench_from_slice(b, 1000)
    }

    fn do_bench_from_iter(b: &mut Bencher, src_len: usize) {
        let src: HybridVec<usize> = FromIterator::from_iter(range(0, src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let dst: HybridVec<usize> = FromIterator::from_iter(src.clone().into_iter());
            assert_eq!(dst.len(), src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_from_iter_0000(b: &mut Bencher) {
        do_bench_from_iter(b, 0)
    }

    #[bench]
    fn bench_from_iter_0010(b: &mut Bencher) {
        do_bench_from_iter(b, 10)
    }

    #[bench]
    fn bench_from_iter_0100(b: &mut Bencher) {
        do_bench_from_iter(b, 100)
    }

    #[bench]
    fn bench_from_iter_1000(b: &mut Bencher) {
        do_bench_from_iter(b, 1000)
    }

    fn do_bench_extend(b: &mut Bencher, dst_len: usize, src_len: usize) {
        let dst: HybridVec<usize> = FromIterator::from_iter(range(0, dst_len));
        let src: HybridVec<usize> = FromIterator::from_iter(range(dst_len, dst_len + src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let mut dst = dst.clone();
            dst.extend(src.clone().into_iter());
            assert_eq!(dst.len(), dst_len + src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_extend_0000_0000(b: &mut Bencher) {
        do_bench_extend(b, 0, 0)
    }

    #[bench]
    fn bench_extend_0000_0010(b: &mut Bencher) {
        do_bench_extend(b, 0, 10)
    }

    #[bench]
    fn bench_extend_0000_0100(b: &mut Bencher) {
        do_bench_extend(b, 0, 100)
    }

    #[bench]
    fn bench_extend_0000_1000(b: &mut Bencher) {
        do_bench_extend(b, 0, 1000)
    }

    #[bench]
    fn bench_extend_0010_0010(b: &mut Bencher) {
        do_bench_extend(b, 10, 10)
    }

    #[bench]
    fn bench_extend_0100_0100(b: &mut Bencher) {
        do_bench_extend(b, 100, 100)
    }

    #[bench]
    fn bench_extend_1000_1000(b: &mut Bencher) {
        do_bench_extend(b, 1000, 1000)
    }

    fn do_bench_push_all(b: &mut Bencher, dst_len: usize, src_len: usize) {
        let dst: HybridVec<usize> = FromIterator::from_iter(range(0, dst_len));
        let src: HybridVec<usize> = FromIterator::from_iter(range(dst_len, dst_len + src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let mut dst = dst.clone();
            dst.push_all(src.as_slice());
            assert_eq!(dst.len(), dst_len + src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_push_all_0000_0000(b: &mut Bencher) {
        do_bench_push_all(b, 0, 0)
    }

    #[bench]
    fn bench_push_all_0000_0010(b: &mut Bencher) {
        do_bench_push_all(b, 0, 10)
    }

    #[bench]
    fn bench_push_all_0000_0100(b: &mut Bencher) {
        do_bench_push_all(b, 0, 100)
    }

    #[bench]
    fn bench_push_all_0000_1000(b: &mut Bencher) {
        do_bench_push_all(b, 0, 1000)
    }

    #[bench]
    fn bench_push_all_0010_0010(b: &mut Bencher) {
        do_bench_push_all(b, 10, 10)
    }

    #[bench]
    fn bench_push_all_0100_0100(b: &mut Bencher) {
        do_bench_push_all(b, 100, 100)
    }

    #[bench]
    fn bench_push_all_1000_1000(b: &mut Bencher) {
        do_bench_push_all(b, 1000, 1000)
    }

    fn do_bench_push_all_move(b: &mut Bencher, dst_len: usize, src_len: usize) {
        let dst: HybridVec<usize> = FromIterator::from_iter(range(0us, dst_len));
        let src: HybridVec<usize> = FromIterator::from_iter(range(dst_len, dst_len + src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let mut dst = dst.clone();
            dst.extend(src.clone().into_iter());
            assert_eq!(dst.len(), dst_len + src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_push_all_move_0000_0000(b: &mut Bencher) {
        do_bench_push_all_move(b, 0, 0)
    }

    #[bench]
    fn bench_push_all_move_0000_0010(b: &mut Bencher) {
        do_bench_push_all_move(b, 0, 10)
    }

    #[bench]
    fn bench_push_all_move_0000_0100(b: &mut Bencher) {
        do_bench_push_all_move(b, 0, 100)
    }

    #[bench]
    fn bench_push_all_move_0000_1000(b: &mut Bencher) {
        do_bench_push_all_move(b, 0, 1000)
    }

    #[bench]
    fn bench_push_all_move_0010_0010(b: &mut Bencher) {
        do_bench_push_all_move(b, 10, 10)
    }

    #[bench]
    fn bench_push_all_move_0100_0100(b: &mut Bencher) {
        do_bench_push_all_move(b, 100, 100)
    }

    #[bench]
    fn bench_push_all_move_1000_1000(b: &mut Bencher) {
        do_bench_push_all_move(b, 1000, 1000)
    }

    fn do_bench_clone(b: &mut Bencher, src_len: usize) {
        let src: HybridVec<usize> = FromIterator::from_iter(range(0, src_len));

        b.bytes = src_len as u64;

        b.iter(|| {
            let dst = src.clone();
            assert_eq!(dst.len(), src_len);
            assert!(dst.iter().enumerate().all(|(i, x)| i == *x));
        });
    }

    #[bench]
    fn bench_clone_0000(b: &mut Bencher) {
        do_bench_clone(b, 0)
    }

    #[bench]
    fn bench_clone_0010(b: &mut Bencher) {
        do_bench_clone(b, 10)
    }

    #[bench]
    fn bench_clone_0100(b: &mut Bencher) {
        do_bench_clone(b, 100)
    }

    #[bench]
    fn bench_clone_1000(b: &mut Bencher) {
        do_bench_clone(b, 1000)
    }

    fn do_bench_clone_from(b: &mut Bencher, times: usize, dst_len: usize, src_len: usize) {
        let dst: HybridVec<usize> = FromIterator::from_iter(range(0, src_len));
        let src: HybridVec<usize> = FromIterator::from_iter(range(dst_len, dst_len + src_len));

        b.bytes = (times * src_len) as u64;

        b.iter(|| {
            let mut dst = dst.clone();

            for _ in range(0, times) {
                dst.clone_from(&src);

                assert_eq!(dst.len(), src_len);
                assert!(dst.iter().enumerate().all(|(i, x)| dst_len + i == *x));
            }
        });
    }

    #[bench]
    fn bench_clone_from_01_0000_0000(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 0, 0)
    }

    #[bench]
    fn bench_clone_from_01_0000_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 0, 10)
    }

    #[bench]
    fn bench_clone_from_01_0000_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 0, 100)
    }

    #[bench]
    fn bench_clone_from_01_0000_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 0, 1000)
    }

    #[bench]
    fn bench_clone_from_01_0010_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 10, 10)
    }

    #[bench]
    fn bench_clone_from_01_0100_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 100, 100)
    }

    #[bench]
    fn bench_clone_from_01_1000_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 1000, 1000)
    }

    #[bench]
    fn bench_clone_from_01_0010_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 10, 100)
    }

    #[bench]
    fn bench_clone_from_01_0100_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 100, 1000)
    }

    #[bench]
    fn bench_clone_from_01_0010_0000(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 10, 0)
    }

    #[bench]
    fn bench_clone_from_01_0100_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 100, 10)
    }

    #[bench]
    fn bench_clone_from_01_1000_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 1, 1000, 100)
    }

    #[bench]
    fn bench_clone_from_10_0000_0000(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 0, 0)
    }

    #[bench]
    fn bench_clone_from_10_0000_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 0, 10)
    }

    #[bench]
    fn bench_clone_from_10_0000_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 0, 100)
    }

    #[bench]
    fn bench_clone_from_10_0000_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 0, 1000)
    }

    #[bench]
    fn bench_clone_from_10_0010_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 10, 10)
    }

    #[bench]
    fn bench_clone_from_10_0100_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 100, 100)
    }

    #[bench]
    fn bench_clone_from_10_1000_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 1000, 1000)
    }

    #[bench]
    fn bench_clone_from_10_0010_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 10, 100)
    }

    #[bench]
    fn bench_clone_from_10_0100_1000(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 100, 1000)
    }

    #[bench]
    fn bench_clone_from_10_0010_0000(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 10, 0)
    }

    #[bench]
    fn bench_clone_from_10_0100_0010(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 100, 10)
    }

    #[bench]
    fn bench_clone_from_10_1000_0100(b: &mut Bencher) {
        do_bench_clone_from(b, 10, 1000, 100)
    }
}
