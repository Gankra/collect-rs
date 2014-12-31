pub use self::mem_descriptor::MemDescriptor;

use rust_alloc::heap;

pub mod mem_descriptor;

pub trait Allocator {
    unsafe fn allocate(&mut self, descriptor: MemDescriptor) -> *mut u8;
    unsafe fn deallocate(&mut self, ptr: *mut u8, descriptor: MemDescriptor);
    unsafe fn shrink(&mut self, ptr: *mut u8, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool;
    unsafe fn grow(&mut self, ptr: *mut u8, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool;
    fn usable_size(&self, descriptor: MemDescriptor) -> uint;
}

#[deriving(Copy, Clone)]
pub struct RustAllocator;

impl Allocator for RustAllocator {
    unsafe fn allocate(&mut self, descriptor: MemDescriptor) -> *mut u8 {
        heap::allocate(descriptor.size, descriptor.alignment)
    }

    unsafe fn deallocate(&mut self, ptr: *mut u8, descriptor: MemDescriptor) {
        heap::deallocate(ptr, descriptor.size, descriptor.alignment)
    }

    unsafe fn shrink(&mut self, ptr: *mut u8, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool {
        heap::reallocate_inplace(ptr, old_descriptor.size, new_descriptor.size, old_descriptor.alignment) == self.usable_size(new_descriptor)
    }

    unsafe fn grow(&mut self, ptr: *mut u8, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool {
        heap::reallocate_inplace(ptr, old_descriptor.size, new_descriptor.size, old_descriptor.alignment) == self.usable_size(new_descriptor)
    }

    fn usable_size(&self, descriptor: MemDescriptor) -> uint {
        heap::usable_size(descriptor.size, descriptor.alignment)
    }
}
