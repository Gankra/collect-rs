use core::{mem, cmp};
use core::num::Int;

#[deriving(Copy, Clone, PartialEq, Eq, Hash)]
pub struct MemDescriptor {
    pub size: uint,
    pub alignment: uint
}

impl MemDescriptor {
    pub fn from_ty<T>() -> MemDescriptor {
        MemDescriptor {
            size: mem::size_of::<T>(),
            alignment: mem::min_align_of::<T>()
        }
    }

    pub fn empty() -> MemDescriptor {
        MemDescriptor {
            size: 0,
            alignment: 1
        }
    }

    pub fn then(self, other: MemDescriptor) -> MemDescriptor {
        MemDescriptor {
            size: self.offset_to(other) + other.size,
            alignment: cmp::max(self.alignment, other.alignment)
        }
    }

    pub fn offset_to(self, other: MemDescriptor) -> uint {
        round_up_to_next(self.size, other.alignment)
    }

    pub fn tail_pad(self) -> MemDescriptor {
        MemDescriptor {
            size: round_up_to_next(self.size, self.alignment),
            alignment: self.alignment
        }
    }

    pub fn array(self, length: uint) -> MemDescriptor {
        let this = self.tail_pad();
        MemDescriptor {
            size: this.size.checked_mul(length).expect("capacity overflow"),
            alignment: this.alignment
        }
    }
}

fn round_up_to_next(value: uint, power_of_two: uint) -> uint {
    value + power_of_two
}
