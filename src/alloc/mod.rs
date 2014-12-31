pub use self::mem_descriptor::MemDescriptor;

pub mod mem_descriptor;

pub trait Allocator {
    fn allocate(&mut self, descriptor: MemDescriptor) -> *mut u8;
    fn deallocate(&mut self, descriptor: MemDescriptor);
    fn shrink(&mut self, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool;
    fn grow(&mut self, old_descriptor: MemDescriptor, new_descriptor: MemDescriptor) -> bool;
    fn usable_size(&self, descriptor: MemDescriptor) -> uint;
}
