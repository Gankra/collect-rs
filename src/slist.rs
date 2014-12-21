//! Singly Linked List.

#![allow(dead_code)]

use std::{ptr, mem, fmt};

type Link<T> = Option<Box<Element<T>>>;

struct Element<T> {
    value: T,
    next: Link<T>
}

pub struct SList<T> {
    head: Link<T>,
    tail: *mut Element<T>
}

// Until Some(T) has been returned by next, curr will be null
pub struct Items<'a, T: 'a> {
    list: &'a SList<T>,
    curr: *mut Element<T>
}

// Until Some(T) has been returned by next, curr will be null
pub struct MutItems<'a, T: 'a> {
    list: &'a mut SList<T>,
    prev: *mut Element<T>,
    curr: *mut Element<T>
}

pub struct MoveItems<'a, T: 'a> {
    list: &'a mut SList<T>
}

impl<T> Element<T> {
    #[inline]
    pub fn new(value: T, next: Link<T>) -> Element<T> {
        Element{value: value, next: next}
    }
}

impl<T> SList<T> {
    #[inline]
    pub fn new() -> SList<T> {
        SList{head: None, tail: ptr::null_mut()}
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }
    pub fn clear(&mut self) {
        if !self.is_empty() {
            self.head = None;
            self.tail = ptr::null_mut();
        }
    }
    pub fn append(&mut self, other: &mut SList<T>) {
        unsafe {
            (*self.tail).next = other.head.take();
        }
        self.tail = other.tail;
        other.tail = ptr::null_mut();
    }
    pub fn push_front(&mut self, value: T) {
        if self.is_empty() {
            self.head = Some(box Element::new(value, None));
            unsafe {
                self.tail = mem::transmute_copy(self.head.as_ref().unwrap());
            }
        } else {
            self.head = Some(box Element::new(value, mem::replace(&mut self.head, None)));
        }
    }
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            let mut tmp = self.head.take();
            self.head = mem::replace(&mut tmp.as_mut().unwrap().next, None);
            if self.head.is_none() {
                self.tail = ptr::null_mut();
            }
            Some(tmp.unwrap().value)
        }
    }
    pub fn push_back(&mut self, value: T) {
        if self.is_empty() {
            self.head = Some(box Element::new(value, None));
            unsafe {
                self.tail = mem::transmute_copy(self.head.as_ref().unwrap());
            }
        } else {
            unsafe {
                (*self.tail).next = Some(box Element::new(value, None));
                self.tail = mem::transmute_copy((*self.tail).next.as_ref().unwrap());
            }
        }
    }
    pub fn front<'a>(&'a self) -> Option<&'a T> {
        if self.is_empty() {
            None
        } else {
            Some(&self.head.as_ref().unwrap().value)
        }
    }
    pub fn back<'a>(&'a self) -> Option<&'a T> {
        unsafe {
            if self.is_empty() {
                None
            } else {
                Some(&(*self.tail).value)
            }
        }
    }
    #[inline]
    pub fn iter<'a>(&'a self) -> Items<'a, T> {
        Items{list: self, curr: ptr::null_mut()}
    }
    #[inline]
    pub fn iter_mut<'a>(&'a mut self) -> MutItems<'a, T> {
        MutItems{list: self, prev: ptr::null_mut(), curr: ptr::null_mut()}
    }
    #[inline]
    pub fn into_iter<'a>(&'a mut self) -> MoveItems<'a, T> {
        MoveItems{list: self}
    }
}

impl<T: Clone> Clone for SList<T> {
    fn clone(&self) -> SList<T> {
        let mut tmp = SList::new();
        for x in self.iter() {
            tmp.push_back(x.clone());
        }
        tmp
    }
}

impl<T: PartialEq> PartialEq for SList<T> {
    fn eq(&self, other: &SList<T>) -> bool {
        let mut it_self = self.iter();
        let mut it_other = other.iter();
        loop {
            match (it_self.next(), it_other.next()) {
                (Some(x), Some(y)) => if x != y {
                    return false;
                },
                (None, None) => { return true; },
                (_, _) => { return false; }
            }
        }
    }
}

impl<T: Eq> Eq for SList<T> {}

impl<T: fmt::Show> fmt::Show for SList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut it = self.iter();
        try!(write!(f, "["));
        if !self.is_empty() {
            try!(write!(f, "{}", it.next().unwrap()));
            let mut x = it.next();
            while x.is_some() {
                try!(write!(f, ", {}", x.unwrap()));
                x = it.next();
            }
            /*while let Some(x) = it.next() {
                try!(write!(f, ", {}", x));
            }*/
        }
        write!(f, "]")
    }
}

#[unsafe_destructor]
impl<T> Drop for SList<T> {
    fn drop(&mut self) {
        self.clear();
    }
}

impl<'a, T> Iterator<&'a T> for Items<'a, T> {
    fn next(&mut self) -> Option<&'a T> {
        if self.curr == self.list.tail {
            None
        } else if self.curr.is_null() {
            unsafe {
                self.curr = mem::transmute_copy(self.list.head.as_ref().unwrap());
                Some(&(*self.curr).value)
            }
        } else {
            unsafe {
                self.curr = mem::transmute_copy((*self.curr).next.as_ref().unwrap());
                Some(&(*self.curr).value)
            }
        }
    }
}

impl<'a, T> Clone for Items<'a, T> {
    fn clone(&self) -> Items<'a, T> {
        Items{list: &*self.list, curr: self.curr}
    }
}

impl<'a, T> Iterator<&'a mut T> for MutItems<'a, T> {
    fn next(&mut self) -> Option<&'a mut T> {
        // Check to see if the iterator is empty or if the iterator is at the
        // end of the list.
        if self.curr == self.list.tail {
            None
        } else if self.curr.is_null() {
            unsafe {
                self.curr = mem::transmute_copy(self.list.head.as_ref().unwrap());
                Some(&mut (*self.curr).value)
            }
        } else {
            self.prev = self.curr;
            unsafe {
                self.curr = mem::transmute_copy((*self.curr).next.as_ref().unwrap());
                Some(&mut (*self.curr).value)
            }
        }
    }
}

impl<'a, T> MutItems<'a, T> {
    pub fn insert_after(&mut self, value: T) {
        if self.curr.is_null() {
            self.list.push_front(value);
        } else {
            unsafe {
                (*self.curr).next = Some(box Element::new(value, mem::replace(&mut (*self.curr).next, None)));
                if self.curr == self.list.tail {
                    self.list.tail = mem::transmute_copy((*self.curr).next.as_ref().unwrap())
                }
            }
        }
    }
    /// Removes the current element but does not advance the iterator.
    /// This function will panic if called twice in a row.
    pub fn remove(&mut self) -> Option<T> {
        if self.prev.is_null() {
            self.curr = ptr::null_mut();
            self.list.pop_front()
        } else if self.curr == self.list.tail {
            let tmp = unsafe {
                mem::replace(&mut (*self.prev).next, None)
            };
            self.curr = self.prev;
            self.list.tail = self.prev;
            Some(tmp.unwrap().value)
        } else {
            let tmp = unsafe {
                mem::replace(&mut (*self.prev).next, mem::replace(&mut (*self.curr).next, None))
			};
            self.curr = self.prev;
			Some(tmp.unwrap().value)
        }
    }
}

impl<'a, T> Iterator<T> for MoveItems<'a, T> {
    fn next(&mut self) -> Option<T> {
        self.list.pop_front()
    }
}

#[cfg(test)]
mod test {
    use std::ptr;
    use super::SList;
    
    #[test]
    fn it_works() {
        let mut l: SList<int> = SList::new();
        l.push_front(2);
        l.push_front(3);
        l.push_back(1);
        assert_eq!(l.is_empty(), false);
        assert_eq!(l.front(), Some(&3));
        assert_eq!(l.back(), Some(&1));
        assert_eq!(l.pop_front(), Some(3));
        assert_eq!(l.pop_front(), Some(2));
        assert_eq!(l.pop_front(), Some(1));
        assert_eq!(l.pop_front(), None);
        assert_eq!(l.front(), None);
        assert_eq!(l.back(), None);
        assert_eq!(l.tail, ptr::null_mut());
    }
    
    #[test]
    fn test_iter() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        
        let mut it = l.iter();
        assert_eq!(it.next().unwrap(), &2);
        assert_eq!(it.next().unwrap(), &3);
        assert_eq!(it.next(), None);
    }
    
    #[test]
    fn test_empty_iter() {
        let mut l: SList<int> = SList::new();
        l.push_back(3);
        l.pop_front();
        
        let mut it = l.iter();
        assert_eq!(it.next(), None);
    }
    
    #[test]
    fn test_clone_iter() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        l.push_back(4);
        
        let mut it = l.iter();
        let mut it2 = it.clone();
        assert_eq!(it.next(), it2.next());
        assert_eq!(it.next(), it2.next());
        assert_eq!(it.next(), it2.next());
        assert_eq!(it.next(), it2.next());
    }
    
    #[test]
    fn test_iter_mut() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        
        let mut it = l.iter_mut();
        assert!(*it.next().unwrap() == 2);
        assert!(*it.next().unwrap() == 3);
        assert_eq!(it.next(), None);
    }
    
    #[test]
    fn test_empty_iter_mut() {
        let mut l: SList<int> = SList::new();
        l.push_back(3);
        l.pop_front();
        
        let mut it = l.iter_mut();
        assert_eq!(it.next(), None);
    }
    
    #[test]
    fn test_iter_mut_mutate() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        {
            let mut it = l.iter_mut();
            *it.next().unwrap() = 5;
            *it.next().unwrap() = 6;
        }
        assert_eq!(l.pop_front(), Some(5));
        assert_eq!(l.pop_front(), Some(6));
        assert_eq!(l.pop_front(), None);
    }
    
    #[test]
    fn test_iter_mut_insert() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        l.push_back(4);
        {
            let mut it = l.iter_mut();
            it.next();
            it.insert_after(6);
            it.next(); it.next();
            it.insert_after(8);
            it.insert_after(7);
            it.next(); it.next(); it.next();
            it.insert_after(9);
        }
        assert_eq!(l.pop_front(), Some(2));
        assert_eq!(l.pop_front(), Some(6));
        assert_eq!(l.pop_front(), Some(3));
        assert_eq!(l.pop_front(), Some(7));
        assert_eq!(l.pop_front(), Some(8));
        assert_eq!(l.pop_front(), Some(4));
        assert_eq!(l.pop_front(), Some(9));
        assert_eq!(l.pop_front(), None);
    }
    
    #[test]
    fn test_iter_mut_remove() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        l.push_back(4);
        l.push_back(5);
        {
            let mut it = l.iter_mut(); // 2, 3, 4, 5
            it.next(); // [2], 3, 4, 5
            it.remove(); // 3, 4, 5
            it.insert_after(6); // 6, 3, 4, 5
            it.next(); // [6], 3, 4, 5
            it.next(); // 6, [3], 4, 5
            it.remove(); // [6], 4, 5
            it.next(); // 6, [4], 5
            it.remove(); // [6], 5
        }
        assert_eq!(l.pop_front(), Some(6));
        assert_eq!(l.pop_front(), Some(5));
        assert_eq!(l.pop_front(), None);
    }
    
    #[test]
    fn test_into_iter() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        l.push_back(4);
        
        let mut it = l.into_iter();
        assert_eq!(it.next(), Some(2));
        assert_eq!(it.next(), Some(3));
        assert_eq!(it.next(), Some(4));
    }
    
    #[test]
    fn test_clone() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        
        let l2 = l.clone();
        assert_eq!(l, l2);
    }
    
    #[test]
    #[should_fail]
    fn test_clone_2() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        
        let mut l2 = l.clone();
        l2.push_front(4);
        assert_eq!(l, l2);
    }
    
    #[test]
    fn test_append() {
        let mut l: SList<int> = SList::new();
        l.push_back(2);
        l.push_back(3);
        
        let mut l2: SList<int> = SList::new();
        l2.push_back(4);
        l2.push_back(5);
        
        l.append(&mut l2);
        assert_eq!(l.pop_front(), Some(2));
        assert_eq!(l.pop_front(), Some(3));
        assert_eq!(l.pop_front(), Some(4));
        assert_eq!(l.pop_front(), Some(5));
        assert_eq!(l2.is_empty(), true);
    }
}
