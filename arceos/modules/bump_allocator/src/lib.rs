#![no_std]

use allocator::{AllocResult, BaseAllocator, ByteAllocator, PageAllocator};
use core::alloc::Layout;
use core::ptr::NonNull;

/// Early memory allocator
/// Use it before formal bytes-allocator and pages-allocator can work!
/// This is a double-end memory range:
/// - Alloc bytes forward
/// - Alloc pages backward
///
/// [ bytes-used | avail-area | pages-used ]
/// |            | -->    <-- |            |
/// start       b_pos        p_pos       end
///
/// For bytes area, 'count' records number of allocations.
/// When it goes down to ZERO, free bytes-used area.
/// For pages area, it will never be freed!
///
#[derive(Default)]
pub struct EarlyAllocator<const PAGE_SIZE: usize> {
    // memory pool
    pool_start: usize,
    pool_end: usize,
    //
    byte_pos: usize,
    page_pos: usize,
    // number of byte allocation
    byte_count: usize,
}

impl<const PAGE_SIZE: usize> EarlyAllocator<PAGE_SIZE> {
    pub const fn new() -> Self {
        EarlyAllocator {
            pool_start: 0,
            pool_end: 0,
            byte_pos: 0,
            page_pos: 0,
            byte_count: 0,
        }
    }
}

impl<const PAGE_SIZE: usize> BaseAllocator for EarlyAllocator<PAGE_SIZE> {
    fn init(&mut self, start: usize, size: usize) {
        // if !size.is_power_of_two(){Err(allocator::AllocError::InvalidParam)}
        self.pool_start = start;
        self.pool_end = start + size;
        self.byte_pos = self.pool_start;
        self.page_pos = self.pool_end;
        self.byte_count = 0
    }

    // todo!()
    fn add_memory(&mut self, _start: usize, _size: usize) -> AllocResult {
        Err(allocator::AllocError::MemoryOverlap)
    }
}

impl<const PAGE_SIZE: usize> ByteAllocator for EarlyAllocator<PAGE_SIZE> {
    fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>> {
        let size = layout.size();
        let align = layout.align();

        // size == 0 返回 dangling
        if size == 0 {
            return Ok(unsafe { NonNull::new_unchecked(self.byte_pos as *mut u8) });
        }

        // align 必须是 2^n
        if !align.is_power_of_two() {
            return Err(allocator::AllocError::InvalidParam);
        }

        // align
        let byte_pos = align_up(self.byte_pos, align);
        let new_byte_pos = byte_pos + size;
        if new_byte_pos > self.page_pos {
            return Err(allocator::AllocError::NoMemory);
        }
        //
        self.byte_pos = new_byte_pos;
        self.byte_count += 1;

        //
        Ok(unsafe { NonNull::new_unchecked(byte_pos as *mut u8) })
    }

    // When it goes down to ZERO, free bytes-used area.
    fn dealloc(&mut self, _pos: NonNull<u8>, _layout: Layout) {
        if self.byte_count > 0 {
            self.byte_count -= 1;
            if self.byte_count == 0 {
                // 归零
                self.byte_pos = self.pool_start;
            }
        }
    }

    fn total_bytes(&self) -> usize {
        self.pool_end - self.pool_start
    }

    fn used_bytes(&self) -> usize {
        self.byte_pos - self.pool_start
    }

    fn available_bytes(&self) -> usize {
        self.page_pos - self.byte_pos
    }
}

impl<const PAGE_SIZE: usize> PageAllocator for EarlyAllocator<PAGE_SIZE> {
    const PAGE_SIZE: usize = PAGE_SIZE;

    fn alloc_pages(
        &mut self,
        num_pages: usize,
        align_pow2: usize,
    ) -> allocator::AllocResult<usize> {
        if num_pages == 0 || !align_pow2.is_power_of_two() {
            return Err(allocator::AllocError::InvalidParam);
        }

        let alloc_bytes = num_pages * PAGE_SIZE;
        let end_pos = self.page_pos - alloc_bytes;
        let new_page_pos = align_down(end_pos, align_pow2);
        if new_page_pos < self.byte_pos {
            return Err(allocator::AllocError::NoMemory);
        }

        self.page_pos = new_page_pos;

        Ok(new_page_pos)
    }

    // todo!()
    fn dealloc_pages(&mut self, _pos: usize, _num_pages: usize) {}

    fn total_pages(&self) -> usize {
        (self.pool_end - self.pool_start) / PAGE_SIZE
    }

    fn used_pages(&self) -> usize {
        (self.pool_end - self.page_pos) / PAGE_SIZE
    }

    fn available_pages(&self) -> usize {
        (self.page_pos - self.byte_pos) / PAGE_SIZE
    }
}

// from allocator
#[inline]
const fn align_down(pos: usize, align: usize) -> usize {
    pos & !(align - 1)
}
#[inline]
const fn align_up(pos: usize, align: usize) -> usize {
    (pos + align - 1) & !(align - 1)
}
