use std::borrow::{Borrow, BorrowMut};
use std::default::Default;
use std::fmt;
use std::hash::{self, Hash};
use std::iter;
use std::marker::PhantomData;
use std::mem;
use std::num::Int;
use std::ops;
use std::ptr;
use std::vec::IntoIter as VecIntoIter;

/// Used internally, public so it is accessible by the `tests` submodule.
#[doc(hidden)]
pub const ARRAY_SIZE: usize = 8;

macro_rules! hybrid_vec [
    // This will need to be adjusted
    [$($elem:expr),*] => (HybridVec::from_boxed_slice(Box::new([$($elem),*])))
];

/// An implementation of `HybridVec` that uses stack-allocated storage below a certain length.
/// A drop-in replacement for `Vec` from the stdlib, with a couple minor changes to the API and internal
/// behavior.
pub enum HybridVec<T> {
    // Data and actual safe length
    // RFC: should this be a struct variant instead? What about `Heap`?
    Stack([T; ARRAY_SIZE], usize),
    Heap(Vec<T>),
}

impl<T> HybridVec<T> {
    #[inline]
    pub fn new() -> HybridVec<T> {
        // Safe because we never allow access to uninited memory from a safe API
        HybridVec::Stack(unsafe { mem::uninitialized() }, 0)
    }

    #[inline]
    pub fn with_capacity(cap: usize) -> HybridVec<T> {
        if mem::size_of::<T>() == 0 {
            HybridVec::Heap(Vec::new())
        } else if cap > ARRAY_SIZE {
            HybridVec::Heap(Vec::with_capacity(cap))
        } else {
            HybridVec::new()
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
        HybridVec::Heap(Vec::from_raw_parts(ptr, length, capacity))
    }

    pub unsafe fn from_raw_buf(ptr: *const T, elts: usize) -> HybridVec<T> {
        let mut vec = HybridVec::with_capacity(elts);
        ptr::copy_nonoverlapping_memory(vec.as_mut_ptr(), ptr, elts);
        vec.set_len(elts);

        vec
    }

    #[inline]
    pub fn len(&self) -> usize {
        match *self {
            HybridVec::Heap(ref vec) => vec.len(),
            HybridVec::Stack(_, len) => len,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        match *self {
            HybridVec::Heap(ref vec) => vec.capacity(),
            HybridVec::Stack(..) => ARRAY_SIZE,
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
            HybridVec::Heap(ref mut vec) => vec.set_len(new_len),
            HybridVec::Stack(_, ref mut len) => *len = new_len,
        }
    }

    pub fn reserve(&mut self, additional: usize) {
        let new_cap = self.len() + additional;
        if self.capacity() < new_cap {
            if self.is_stack() {
                self.move_to_heap(new_cap);
            } else if let HybridVec::Heap(ref mut vec) = *self {
                vec.reserve(additional);
            }
        }
    }

    //#[inline]
    fn is_stack(&self) -> bool {
        match *self {
            HybridVec::Stack(..) => true,
            _ => false,
        }
    }

    /// Move to the heap if the new capacity requirement is too big for the stack
    fn move_to_heap(&mut self, capacity: usize) {
        // Sanity checks
        if !self.is_stack() { return }

        unsafe {
            let temp = mem::replace(self, HybridVec::with_capacity(capacity));

            if let HybridVec::Stack(ref array, len) = temp {
                ptr::copy_nonoverlapping_memory(self.as_mut_ptr(), array.as_ptr(), len);
                self.set_len(len);
            }

            mem::forget(temp);
        }
    }

    /// Move back to the stack if the vector can fit
    fn move_to_stack(&mut self) {
        if self.is_stack() || self.len() > ARRAY_SIZE { return }

        unsafe {
            let mut temp = mem::replace(self, HybridVec::new());
            self.set_len(temp.len());
            ptr::copy_nonoverlapping_memory(self.as_mut_ptr(), temp.as_ptr(), temp.len());

            // Don't let the vector drop its elements, just have it dealloc
            temp.set_len(0);
        }
    }

    #[inline]
    pub fn as_mut_slice<'a>(&'a mut self) -> &'a mut [T] {
        match *self {
            HybridVec::Heap(ref mut vec) => vec,
            HybridVec::Stack(ref mut array, len) => &mut array[..len],
        }
    }

    pub fn into_iter(mut self) -> IntoIter<T> {
        let ret = match self {
            HybridVec::Stack(ref array, len) => {
                let array = unsafe { ptr::read(array) };

                IntoIter::Stack {
                    array: array,
                    curr: 0,
                    len: len,
                }
            },
            HybridVec::Heap(ref mut vec) => {
                let vec = mem::replace(vec, Vec::new());

                IntoIter::Heap {
                    iter: vec.into_iter(),
                }
            },
        };

        unsafe { mem::forget(self) }

        ret
    }

    pub fn retain<F>(&mut self, mut f: F) where F: FnMut(&T) -> bool {
        let len = self.len();
        let mut del = 0usize;
        {
            let v = self.as_mut_slice();

            for i in range(0usize, len) {
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
            HybridVec::Stack(..) => (),
            HybridVec::Heap(_) if self.len() <= ARRAY_SIZE && move_to_stack => self.move_to_stack(),
            HybridVec::Heap(ref mut vec) => vec.shrink_to_fit(),
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
        let(ptr, len): (*const T, usize) = match *self {
            HybridVec::Stack(ref mut array, len) => (array.as_ptr(), len),
            HybridVec::Heap(ref vec) => (vec.as_ptr(), vec.len()),
        };

        Drain {
            curr: ptr,
            end: unsafe { ptr.offset(len as isize) },
            marker: PhantomData,
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

/* changes to this trait now disallow this impl
impl<T> ToOwned<HybridVec<T>> for [T] where T: Clone {
    fn to_owned(&self) -> HybridVec<T> {
        let mut vec = HybridVec::new();
        vec.extend(self.iter().cloned());
        vec
    }
}
*/

impl<T> AsSlice<T> for HybridVec<T> {
    fn as_slice<'a>(&'a self) -> &[T] {
        match *self {
            HybridVec::Heap(ref vec) => vec,
            HybridVec::Stack(ref array, len) => &array[..len],
        }
    }
}

impl<T> Borrow<[T]> for HybridVec<T> {
    fn borrow(&self) -> &[T] {
        self.as_slice()
    }
}

impl<T> BorrowMut<[T]> for HybridVec<T> {
    fn borrow_mut(&mut self) -> &mut [T] {
        self.as_mut_slice()
    }
}

impl<T> ops::Deref for HybridVec<T> {
    type Target = [T];

    fn deref<'a>(&'a self) -> &'a [T] { self.as_slice() }
}

impl<T> ops::DerefMut for HybridVec<T> {
    #[inline]
    fn deref_mut<'a>(&'a mut self) -> &'a mut [T] { self.as_mut_slice() }
}

impl<T> fmt::Debug for HybridVec<T> where T: fmt::Debug {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Debug::fmt(self.as_slice(), f)
    }
}

impl<T: Hash> Hash for HybridVec<T> {
    //#[inline]
    fn hash<H>(&self, state: &mut H) where H: hash::Hasher {
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

impl<T> Extend<T> for HybridVec<T> {
    #[inline]
    fn extend<I: iter::IntoIterator<Item=T>>(&mut self, iterable: I) {
        let iter = iterable.into_iter();
        let (lower, _) = iter.size_hint();
        self.reserve(lower);

        for elem in iter {
            self.push(elem);
        }
    }
}

impl<T> iter::FromIterator<T> for HybridVec<T> {
    #[inline]
    fn from_iter<I: iter::IntoIterator<Item=T>>(iterable: I) -> HybridVec<T> {
        let mut iter = iterable.into_iter();
        let (lower, _) = iter.size_hint();

        let mut vec = HybridVec::with_capacity(lower);

        for elem in iter.by_ref().take(vec.capacity()) {
            let len = vec.len();
            unsafe {
                ptr::write(vec.get_unchecked_mut(len), elem);
                vec.set_len(len + 1);
            }
        }

        if vec.len() == vec.capacity() {
            for elem in iter {
                vec.push(elem);
            }
        }

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

impl<T> ops::Index<ops::RangeFull> for HybridVec<T> {
    type Output = [T];
    //#[inline]
    fn index(&self, _index: &ops::RangeFull) -> &[T] {
        self.as_slice()
    }
}

impl<T> ops::IndexMut<usize> for HybridVec<T> {
    //#[inline]
    fn index_mut(&mut self, index: &usize) -> &mut T {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::Range<usize>> for HybridVec<T> {
    //#[inline]
    fn index_mut(&mut self, index: &ops::Range<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::RangeTo<usize>> for HybridVec<T> {
    //#[inline]
    fn index_mut(&mut self, index: &ops::RangeTo<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::RangeFrom<usize>> for HybridVec<T> {
    //#[inline]
    fn index_mut(&mut self, index: &ops::RangeFrom<usize>) -> &mut [T] {
        self.as_mut_slice().index_mut(index)
    }
}

impl<T> ops::IndexMut<ops::RangeFull> for HybridVec<T> {
    //#[inline]
    fn index_mut(&mut self, _index: &ops::RangeFull) -> &mut [T] {
        self.as_mut_slice()
    }
}

#[unsafe_destructor]
impl<T> Drop for HybridVec<T> {
    fn drop(&mut self) {
        // We zero self here so the drop glue knows not to run the dtor again (FIXME)
        let mut temp = mem::replace(self, unsafe { mem::zeroed() });

        match temp {
            // Replace the vector and let its own drop glue clean up.
            // Forgetting an empty vector is safe because it hasn't allocated yet.
            HybridVec::Heap(ref mut vec) => *vec = Vec::new(),
            HybridVec::Stack(ref array, len) => {
                // Only drop the initialized elements of the array.
                for x in array[..len].iter() {
                    unsafe { ptr::read(x) };
                }
            },
        }

        unsafe { mem::forget(temp) };
    }
}

pub enum IntoIter<T> {
    Stack {
        array: [T; ARRAY_SIZE],
        curr: usize,
        len: usize,
    },
    Heap {
        iter: VecIntoIter<T>,
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
            IntoIter::Heap { ref mut iter } => iter.next(),
            _ => None,
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match *self {
            IntoIter::Stack { array: _, curr, len } => {
                let exact = len - curr;
                (exact, Some(exact))
            },
            IntoIter::Heap { ref iter } => iter.size_hint(),
        }
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
            IntoIter::Heap { ref mut iter } => iter.next_back(),
            _ => None,
        }
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {}

impl<T> IntoIter<T> {
    pub fn into_inner(mut self) -> HybridVec<T> {
        for _ in self.by_ref() {}

        let ret = match self {
            // I can't think of a case where you would want to re-use stack space,
            // except to get back at data that should have been dropped. This seems safer.
            // However, the heap variant preserves `Vec`'s behavior in this case, so not 100% safe.
            IntoIter::Stack { array: _, curr: _, len: _ } => HybridVec::new(),
            IntoIter::Heap { ref mut iter } => {
                // Forgetting an empty (Vec) IntoIter is safe for the same reason
                // forgetting an empty vector is. There's no allocation.
                HybridVec::Heap(
                    mem::replace(iter, Vec::new().into_iter())
                        .into_inner()
                )
            },
        };

        unsafe { mem::forget(self); }
        ret
    }
}

#[unsafe_destructor]
impl<T> Drop for IntoIter<T> {
    fn drop(&mut self) {
        let mut temp = mem::replace(self, unsafe { mem::zeroed() });

        match temp {
            IntoIter::Heap { ref mut iter } => *iter = Vec::new().into_iter(),
            IntoIter::Stack { .. } => for _ in temp.by_ref() {},
        }

        unsafe { mem::forget(temp); }
    }
}

pub struct Drain<'a, T: 'a> {
    curr: *const T,
    end: *const T,
    marker: PhantomData<&'a T>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = T;

    //#[inline]
    fn next(&mut self) -> Option<T> {
        if self.curr == self.end { return None; }

        unsafe {
            if mem::size_of::<T>() == 0 {
                self.curr = mem::transmute(self.curr as usize + 1);
                return Some(ptr::read(mem::transmute(1usize)));
            }

            let ret = ptr::read(self.curr);
            self.curr = self.curr.offset(1);
            Some(ret)
        }
    }

    //#[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let diff = (self.end as usize) - (self.curr as usize);
        let size = mem::size_of::<T>();
        let exact = diff / (if size == 0 {1} else {size});

        (exact, Some(exact))
    }
}

impl<'a, T> DoubleEndedIterator for Drain<'a, T> {
    //#[inline]
    fn next_back(&mut self) -> Option<T> {
        if self.curr == self.end { return None; }

        unsafe {
            if mem::size_of::<T>() == 0 {
                self.end = mem::transmute(self.end as usize - 1);
                return Some(ptr::read(mem::transmute(1usize)));
            }

            self.end = self.end.offset(-1);
            Some(ptr::read(self.end))
        }
    }
}

impl<'a, T> ExactSizeIterator for Drain<'a, T> {}

#[unsafe_destructor]
impl<'a, T> Drop for Drain<'a, T> {
    fn drop(&mut self) {
        for _ in self.by_ref() {}
    }
}

#[cfg(test)]
mod tests {
    use test::Bencher;

    use super::{ARRAY_SIZE, HybridVec};

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

        for i in range(0isize, 16) {
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

        v.extend(range(0isize, 3));
        for i in range(0isize, 3) { w.push(i) }

        assert_eq!(v, w);

        v.extend(range(3isize, 10));
        for i in range(3isize, 10) { w.push(i) }

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
                assert!(&left[..left.len()] == &[1, 2][..]);
            }
            for p in left.iter_mut() {
                *p += 1;
            }

            {
                let right: &[_] = right;
                assert!(&right[..right.len()] == &[3, 4, 5][..]);
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
        let w = hybrid_vec!(1isize, 2, 3);

        assert_eq!(v, v.clone());

        let z = w.clone();
        assert_eq!(w, z);
        // they should be disjoint in memory.
        assert!(w.as_ptr() != z.as_ptr())
    }

    #[test]
    fn test_clone_from() {
        let mut v = hybrid_vec!();
        let three = hybrid_vec!(box 1isize, box 2, box 3);
        let two = hybrid_vec!(box 4isize, box 5);
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
        let mut vec = hybrid_vec![1usize, 2, 3, 4];
        vec.retain(|&x| x % 2 == 0);
        assert!(vec == hybrid_vec![2usize, 4]);
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
        assert_eq!(hybrid_vec![1isize, 2, 3].into_iter().partition(|x: &isize| *x < 4), (hybrid_vec![1, 2, 3], hybrid_vec![]));
        assert_eq!(hybrid_vec![1isize, 2, 3].into_iter().partition(|x: &isize| *x < 2), (hybrid_vec![1], hybrid_vec![2, 3]));
        assert_eq!(hybrid_vec![1isize, 2, 3].into_iter().partition(|x: &isize| *x < 0), (hybrid_vec![], hybrid_vec![1, 2, 3]));
    }

    #[test]
    fn test_zip_unzip() {
        let z1 = hybrid_vec![(1isize, 4isize), (2, 5), (3, 6)];

        let (left, right): (HybridVec<_>, HybridVec<_>) = z1.iter().map(|&x| x).unzip();

        assert_eq!((1, 4), (left[0], right[0]));
        assert_eq!((2, 5), (left[1], right[1]));
        assert_eq!((3, 6), (left[2], right[2]));
    }

    #[test]
    fn test_unsafe_ptrs() {
        unsafe {
            // Test on-stack copy-from-buf.
            let a = [1isize, 2, 3];
            let ptr = a.as_ptr();
            let b = HybridVec::from_raw_buf(ptr, 3usize);
            assert_eq!(b, hybrid_vec![1, 2, 3]);

            // Test on-heap copy-from-buf.
            let c = hybrid_vec![1isize, 2, 3, 4, 5];
            let ptr = c.as_ptr();
            let d = HybridVec::from_raw_buf(ptr, 5usize);
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
        let vec = hybrid_vec!(1isize, 2, 3);
        assert!(vec[1] == 2);
    }

    #[test]
    #[should_fail]
    fn test_index_out_of_bounds() {
        let vec = hybrid_vec!(1isize, 2, 3);
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
        let xs = hybrid_vec![1usize, 2, 3];
        let ys = xs.into_boxed_slice();
        assert_eq!(ys.as_slice(), [1usize, 2, 3]);
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
    fn bench_small_hybrid(b: &mut Bencher) {
        b.iter(||{
            let _: HybridVec<_> = (0 .. ARRAY_SIZE).collect();
        });
    }

    #[bench]
    fn bench_small_vec(b: &mut Bencher) {
        b.iter(||{
            let _: Vec<_> = (0 .. ARRAY_SIZE).collect();
        });
    }
}

