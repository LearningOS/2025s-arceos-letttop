//! Allocator algorithm in lab.

#![no_std]
#![allow(unused_variables)]

use allocator::{AllocError, AllocResult, BaseAllocator, ByteAllocator};
use core::alloc::Layout;
use core::mem::size_of;
use core::ptr::NonNull;

extern crate axlog as log;

/// SL
/// 2^12 2^11 2^10 2^9 2^8 2^7 2^6 2^5
/// 由于是16B对齐，所以底部分得过细的 实际没有什么意义
///
/// 所有的size都是包括head的

type FlMapType = u8;
const FL_BITS: usize = 3;
const FLLEN: usize = 1 << FL_BITS;
type SlMapType = u8;
const SL_BITS: usize = 3;
const SLLEN: usize = 1 << SL_BITS;
// 最小空闲块32B，即最小分配内存为32-16=16B
const GRANULARITY: usize = 32;
const MIN_BITS: usize = 5;
// 所以对齐就只需要16B
const ALIGN: usize = 16;

/// head of memory
/// align to 16B
#[repr(C, align(16))]
#[derive(Debug, Clone, Copy)]
struct BlockHdr {
    /// The size of the whole memory block, including the header.
    /// size[0] indicates whether the block is used (1 is used)
    /// size[1] indicates whether the block is pool last (1 is tail)
    size_and_flags: usize,
    prev_phys_block: Option<NonNull<BlockHdr>>,
}

#[repr(C, align(16))]
struct UsedBlockHdr {
    common: BlockHdr,
}

/// head of free memory
/// 32B, 16B align
struct FreeBlockHdr {
    common: BlockHdr,
    next_free: Option<NonNull<FreeBlockHdr>>,
    prev_free: Option<NonNull<FreeBlockHdr>>,
}

pub struct LabByteAllocator {
    fl_bitmap: FlMapType,
    sl_bitmap: [SlMapType; FLLEN],
    first_free: [[Option<NonNull<FreeBlockHdr>>; SLLEN]; FLLEN],

    total_size: usize,
    used_size: usize,
}

impl LabByteAllocator {
    /// create a empty allocator
    pub const fn new() -> Self {
        Self {
            fl_bitmap: 0,
            sl_bitmap: [0; FLLEN],
            first_free: [[None; SLLEN]; FLLEN],
            total_size: 0,
            used_size: 0,
        }
    }
}

impl BaseAllocator for LabByteAllocator {
    // only used once
    fn init(&mut self, start: usize, size: usize) {
        log::info!(
            "LabByteAllocator: Initializing with start={:#x}, size={:#x}",
            start,
            size
        );

        *self = Self::new();
        self.add_memory(start, size).expect("init memory failed");
    }
    fn add_memory(&mut self, start: usize, size: usize) -> AllocResult {
        log::info!(
            "LabByteAllocator: Adding memory region start={:#x}, size={:#x}",
            start,
            size
        );

        // 对齐 start 到 16 字节边界
        let align_start = align_up(start, ALIGN);
        let align_end = align_down(start + size, ALIGN);
        let actual_size = if align_end > align_start {
            align_end - align_start
        } else {
            0
        };

        log::debug!(
            "LabByteAllocator: Aligned region start={:#x}, end={:#x}, actual_size={:#x}",
            align_start,
            align_end,
            actual_size
        );

        if align_end < align_start + GRANULARITY {
            log::error!(
                "LabByteAllocator: Memory region too small (actual_size={:#x}, min_required={:#x})",
                actual_size,
                GRANULARITY
            );
            return Err(AllocError::NoMemory);
        }

        self.total_size += align_end - align_start;
        // 在对齐后地址处打一个 FreeBlockHdr，把 size_and_flags、prev_phys_block 等写好
        let hdr_ptr = align_start as *mut FreeBlockHdr;
        unsafe {
            let mut fb = NonNull::new_unchecked(hdr_ptr);
            let bh = &mut fb.as_mut().common;
            bh.set_size(actual_size);
            bh.mark_free();
            bh.mark_tail();
            bh.prev_phys_block = None;

            log::debug!(
                "LabByteAllocator: Initial free block created at {:p}, size={:#x}",
                fb.as_ptr(),
                actual_size
            );

            // 把它链接到 first_free[fl][sl] 上，更新 fl_bitmap/sl_bitmap
            self.insert_block(fb);
        }
        log::info!(
            "LabByteAllocator: Memory region added successfully. Total size now: {:#x}",
            self.total_size
        );
        Ok(())
    }
}

impl ByteAllocator for LabByteAllocator {
    fn alloc(&mut self, layout: Layout) -> AllocResult<NonNull<u8>> {
        log::debug!("LabByteAllocator: alloc request: {:?}", layout);

        // 计算所需块大小
        let size_align = layout.align().max(ALIGN);
        let header_sz = size_of::<UsedBlockHdr>();
        assert_eq!(header_sz, 16);
        let size: usize = (layout.size() + header_sz).max(GRANULARITY);
        let bsize = align_up(size, ALIGN);

        log::debug!(
            "LabByteAllocator: Calculated block_size={:#x} (payload {:#x} + header {:#x}, aligned, min_granularity)",
            bsize, layout.size(), header_sz
        );

        let mut found_block_ptr = match self.find_first_fit_block_indices_ctz(bsize) {
            Some(fb) => fb,
            None => return Err(AllocError::NoMemory),
        };
        unsafe { self.remove_block(found_block_ptr) };

        log::debug!(
            "LabByteAllocator: Removed block {:p} of size {:#x}  for allocation",
            found_block_ptr.as_ptr(),
            unsafe { found_block_ptr.as_ref().common.size() }
        );

        // 判断是否需要分割
        let full_size = unsafe { found_block_ptr.as_ref().common.size() };
        let remain = full_size - bsize;
        if remain >= GRANULARITY {
            log::debug!(
                "LabByteAllocator: Splitting block {:p}. Original size {:#x}, alloc size {:#x}, remaining {:#x}",
                found_block_ptr, full_size, bsize, remain
            );
            unsafe {
                // a) 把当前 block 调整为要分配的大小，并标记已用
                let bh = found_block_ptr.as_mut();
                let was_tail = bh.common.is_tail();

                bh.common.set_size(bsize);
                bh.common.mark_used();
                if was_tail {
                    bh.common.mark_not_tail(); // 分裂后，allocated 块不再是尾
                }

                // b) 在尾部生成新的 FreeBlockHdr
                let new_ptr = (found_block_ptr.as_ptr() as usize + bsize) as *mut FreeBlockHdr;
                let mut new_fb = NonNull::new_unchecked(new_ptr);
                {
                    let nf = new_fb.as_mut();
                    nf.common.set_size(remain);
                    nf.common.mark_free();
                    if was_tail {
                        nf.common.mark_tail(); // 继承 tail
                    } else {
                        nf.common.mark_not_tail();
                    }
                    // 设置前物理块指针
                    nf.common.prev_phys_block = Some(NonNull::new_unchecked(
                        found_block_ptr.as_ptr() as *mut BlockHdr,
                    ));
                }
                // c) 更新新 free 块之后那个块的 prev_phys_block
                if !was_tail {
                    let next_hdr = (new_ptr as usize + remain) as *mut BlockHdr;
                    (*next_hdr).prev_phys_block =
                        Some(NonNull::new_unchecked(new_ptr as *mut BlockHdr));
                }
                // d) 把新块插回 free list
                self.insert_block(new_fb);
            }
            self.used_size += bsize;
        } else {
            unsafe {
                found_block_ptr.as_mut().common.mark_used();
            }
            self.used_size += full_size;
        }

        Ok(unsafe { NonNull::new_unchecked((found_block_ptr.as_ptr() as *mut u8).add(header_sz)) })
    }
    fn dealloc(&mut self, pos: NonNull<u8>, layout: Layout) {
        log::debug!(
            "LabByteAllocator: dealloc request: ptr {:p}, layout {:?}",
            pos,
            layout
        );
        unsafe {
            // 1. 找到 BlockHdr
            let hdr_ptr = (pos.as_ptr() as usize - size_of::<BlockHdr>()) as *mut BlockHdr;
            let mut hdr_nn = NonNull::new_unchecked(hdr_ptr);
            let mut was_tail = hdr_nn.as_ref().is_tail();

            // 2. 先减去原来这块的大小
            let orig_size = hdr_nn.as_ref().size();
            self.used_size -= orig_size;

            // 3. 标记为 free，保留tail标记
            hdr_nn.as_mut().mark_free();
            let mut free_blk = hdr_nn.cast::<FreeBlockHdr>();

            // 4. 尝试与前面的块合并
            if let Some(prev_nn) = hdr_nn.as_ref().prev_phys_block {
                let prev_hdr = prev_nn.as_ptr();
                if (*prev_hdr).is_free() {
                    // 前块是 free，就把它从 free list 抽出，合并
                    let mut prev_fb = prev_nn.cast::<FreeBlockHdr>();
                    self.remove_block(prev_fb);
                    let sum = (*prev_hdr).size() + orig_size;
                    // 更新合并之后的首址和大小
                    (*prev_hdr).set_size(sum);

                    // tail 标记往前传
                    if was_tail {
                        (*prev_hdr).mark_tail();
                    } else {
                        (*prev_hdr).mark_not_tail();
                    }

                    free_blk = NonNull::new_unchecked(prev_hdr as *mut FreeBlockHdr);
                    // 更新 hdr_ptr 为新的合并块
                    hdr_nn = prev_nn;
                }
            }

            // 5. 尝试与后面的块合并
            was_tail = hdr_nn.as_ref().is_tail();
            if !was_tail {
                let cur_ptr = hdr_nn.as_ptr();
                let next_hdr = (cur_ptr as usize + (*cur_ptr).size()) as *mut BlockHdr;

                if (*next_hdr).is_free() {
                    let next_was_tail = (*next_hdr).is_tail();
                    // 后块也是 free，从 free list 抽出
                    let next_fb = NonNull::new_unchecked(next_hdr as *mut FreeBlockHdr);
                    self.remove_block(next_fb);
                    // 合并大小
                    let combined = (*cur_ptr).size() + (*next_hdr).size();
                    (*cur_ptr).set_size(combined);
                    // tail 标记往后传
                    if next_was_tail {
                        (*cur_ptr).mark_tail();
                    } else {
                        (*cur_ptr).mark_not_tail();
                    }
                }
            }

            {
                // 不论是否合并，更新下一个块的 prev_phys_block
                let cur_ptr = hdr_nn.as_ptr();
                let next_hdr = (cur_ptr as usize + (*cur_ptr).size()) as *mut BlockHdr;
                (*next_hdr).prev_phys_block = Some(NonNull::new_unchecked(cur_ptr));
            }
            // 6. 将合并完的块插回 free list
            self.insert_block(free_blk);
        }
    }
    fn total_bytes(&self) -> usize {
        self.total_size
    }
    fn used_bytes(&self) -> usize {
        self.used_size
    }
    fn available_bytes(&self) -> usize {
        self.total_size - self.used_size
    }
}

// 辅助函数s

// 对齐
#[inline]
fn align_down(addr: usize, align: usize) -> usize {
    addr & !(align - 1)
}
#[inline]
fn align_up(addr: usize, align: usize) -> usize {
    (addr + align - 1) & !(align - 1)
}

/// 找到 size 对应的 (fl, sl)
#[inline]
fn mapping(size: usize) -> (usize, usize) {
    // 1) 至少要 MIN_BITS（32B）
    let s = size.max(GRANULARITY);
    // 2) 找到 floor(log2(s))
    let msb = core::mem::size_of::<usize>() * 8 - 1 - s.leading_zeros() as usize;
    // 3) 计算 fl 索引（去掉最小块的 5 位）
    //    并 clamp 到 [0, FLLEN-1]
    let fl = if msb >= MIN_BITS {
        (msb - MIN_BITS).min(FLLEN - 1)
    } else {
        0
    };
    // 4) 本组的起始大小 = 1 << (fl + MIN_BITS)
    let base = 1 << (fl + MIN_BITS);
    //    在组内的偏移
    let offset = s - base;
    //    每份大小 = (1 << (fl + MIN_BITS)) / SLLEN
    //           = 1 << (fl + MIN_BITS - SL_BITS)
    let sl = (offset >> (fl + MIN_BITS - SL_BITS)).min(SLLEN - 1);
    (fl, sl)
}

// 查找空闲块链头的辅助函数
impl LabByteAllocator {
    pub fn find_first_fit_block_indices_ctz(&self, bsize: usize) -> Option<NonNull<FreeBlockHdr>> {
        // 计算起始 fl, sl
        let (start_fl, start_sl) = mapping(bsize);

        // 遍历 fl 索引
        for fl in start_fl..FLLEN {
            // 首个fl时sl要从start_sl开始，其余fl全部从0开始
            let sl_start = if fl == start_fl { start_sl } else { 0 };
            for sl in sl_start..SLLEN {
                let mut curr = self.first_free[fl][sl];
                while let Some(block) = curr {
                    let block_size = unsafe { block.as_ref().common.size() };
                    if block_size >= bsize {
                        return Some(block);
                    }
                    curr = unsafe { block.as_ref().next_free };
                }
            }
        }
        None
    }

    // 查找符合大小的空闲块的辅助函数
    pub fn find_free_block_fit_size() {}
}
// fl_map和sl_map特定位的set和clear
impl LabByteAllocator {
    #[inline]
    fn fl_set(&mut self, f: usize) {
        self.fl_bitmap |= 1 << f;
    }
    #[inline]
    fn fl_clear(&mut self, f: usize) {
        self.fl_bitmap &= !(1 << f);
    }
    #[inline]
    fn sl_set(&mut self, f: usize, s: usize) {
        self.sl_bitmap[f] |= 1 << s;
    }
    #[inline]
    fn sl_clear(&mut self, f: usize, s: usize) {
        self.sl_bitmap[f] &= !(1 << s);
    }
}

// size and flags 的设置
impl BlockHdr {
    #[inline]
    fn is_free(&self) -> bool {
        (self.size_and_flags & 1) == 0
    }
    #[inline]
    fn is_tail(&self) -> bool {
        (self.size_and_flags & 2) != 0
    }
    #[inline]
    fn size(&self) -> usize {
        self.size_and_flags & !0b11
    }
    #[inline]
    fn set_size(&mut self, sz: usize) {
        let flags = self.size_and_flags & 0b11;
        self.size_and_flags = sz | flags;
    }
    #[inline]
    fn mark_free(&mut self) {
        self.size_and_flags &= !1;
    }
    #[inline]
    fn mark_used(&mut self) {
        self.size_and_flags |= 1;
    }
    #[inline]
    fn mark_tail(&mut self) {
        self.size_and_flags |= 2;
    }
    #[inline]
    fn mark_not_tail(&mut self) {
        self.size_and_flags &= !2;
    }
}

// free_block的增删
impl LabByteAllocator {
    unsafe fn insert_block(&mut self, mut b: NonNull<FreeBlockHdr>) {
        let hdr = b.as_mut();
        let sz = hdr.common.size();
        let (fl, sl) = mapping(sz);

        // 插入链头
        hdr.next_free = self.first_free[fl][sl];
        hdr.prev_free = None;
        if let Some(mut old) = self.first_free[fl][sl] {
            old.as_mut().prev_free = Some(b);
        }
        self.first_free[fl][sl] = Some(b);
        // 更新位图
        self.fl_set(fl);
        self.sl_set(fl, sl);
    }

    unsafe fn remove_block(&mut self, mut b: NonNull<FreeBlockHdr>) {
        let hdr = b.as_mut();
        let sz = hdr.common.size();
        let (fl, sl) = mapping(sz);
        log::debug!(
            "LabByteAllocator: remove block: ptr {:p}, size={:#x}, fl={}, sl={}",
            b,
            sz,
            fl,
            sl
        );
        log::debug!(
            "LabByteAllocator: remove block: prev_free={:#?}, next_free={:#?}, first_free[fl][sl]={:#?}",
            hdr.prev_free.map(|p| p.as_ptr() as usize),
            hdr.next_free.map(|p| p.as_ptr() as usize),
            self.first_free[fl][sl].map(|p| p.as_ptr() as usize)
        );
        // 从双向链表摘除
        if let Some(mut p) = hdr.prev_free {
            p.as_mut().next_free = hdr.next_free;
        } else {
            self.first_free[fl][sl] = hdr.next_free;
        }
        if let Some(mut n) = hdr.next_free {
            n.as_mut().prev_free = hdr.prev_free;
        }
        // 清位图
        if self.first_free[fl][sl].is_none() {
            self.sl_clear(fl, sl);
            if self.sl_bitmap[fl] == 0 {
                self.fl_clear(fl);
            }
        }
    }
}

unsafe impl Send for LabByteAllocator {}

#[cfg(test)]
mod tests {
    // 在 no_std 使用 #[test] 需要 std 测试框架
    extern crate std;
    use super::*;

    #[test]
    fn test_struct_sizes_and_alignments() {
        // BlockHdr: 2 * usize = 16 bytes；对齐 16
        assert_eq!(size_of::<BlockHdr>(), 16);
        // FreeBlockHdr: 16 + 8 + 8 = 32 bytes；对齐 32
        assert_eq!(size_of::<FreeBlockHdr>(), 32);
        // UsedBlockHdr: 16 bytes; 对齐32
        assert_eq!(size_of::<UsedBlockHdr>(), 16);

        // LabByteAllocator:
        //  fl_bitmap: u8           -> offset 0
        //  sl_bitmap: [u8; 8]      -> offset 1 .. 9
        //  first_free: 8(ptr) × 8 × 8 = 512 bytes
        // total = 1 + 8 + 7(padding of ptr need) + 512 = 528
        assert_eq!(size_of::<LabByteAllocator>(), 528);
    }

    #[test]
    fn test_align_up_down() {
        // align_down
        assert_eq!(align_down(0x0000, ALIGN), 0x0000);
        assert_eq!(align_down(0x000F, ALIGN), 0x0000);
        assert_eq!(align_down(0x0010, ALIGN), 0x0010);
        assert_eq!(align_down(0x0011, ALIGN), 0x0010);

        // align_up
        assert_eq!(align_up(0x0000, ALIGN), 0x0000);
        assert_eq!(align_up(0x0001, ALIGN), 0x0010);
        assert_eq!(align_up(0x0010, ALIGN), 0x0010);
        assert_eq!(align_up(0x0011, ALIGN), 0x0020);
    }

    #[test]
    fn test_mapping_thresholds() {
        // 按注释：2^12,2^11,…,2^5
        let thresholds = [
            1 << 12, // 4096
            1 << 11, // 2048
            1 << 10, // 1024
            1 << 9,  // 512
            1 << 8,  // 256
            1 << 7,  // 128
            1 << 6,  // 64
            1 << 5,  // 32
        ];
        // 对应的 (fl,sl) 应该是 (7,0),(6,1)…(0,7)
        for (i, &t) in thresholds.iter().enumerate() {
            let (fl, sl) = mapping(t);
            assert_eq!(
                (fl, sl),
                (7 - i, i),
                "size = {}, expect fl={} sl={}, got {:?}",
                t,
                7 - i,
                i,
                (fl, sl)
            );
        }
    }

    #[test]
    fn test_mapping_boundaries() {
        // 验证各组边界
        let cases = [
            (32, (0, 0)), // 2^5
            (63, (0, 7)), // [32,64)
            (64, (1, 0)), // 2^6
            (127, (1, 7)),
            (128, (2, 0)), // 2^7
            (255, (2, 7)),
        ];
        for &(size, expect) in &cases {
            assert_eq!(
                mapping(size),
                expect,
                "size = {}, expect {:?}, got {:?}",
                size,
                expect,
                mapping(size)
            );
        }
    }

    #[test]
    fn test_add_memory_too_small() {
        let mut alloc = LabByteAllocator::new();
        // 整个区间对齐后不够放一个 FreeBlockHdr
        let res = alloc.add_memory(0x1003, size_of::<FreeBlockHdr>() - 1);
        assert!(matches!(res, Err(AllocError::NoMemory)));
    }

    #[test]
    fn test_add_memory_basic() {
        // 1) 用一个固定大小的数组模拟「一大块内存」
        const BUFSZ: usize = 0x2000 + ALIGN;
        // 在栈上开 BUFSZ 字节，避免使用 Vec
        let mut buffer: [u8; BUFSZ] = [0; BUFSZ];
        let base = buffer.as_mut_ptr() as usize;
        // 偏移 3 字节以测试 align_up
        let unaligned = base + 3;

        // 2) 调用 add_memory
        let mut alloc = LabByteAllocator::new();
        alloc.add_memory(unaligned, 0x2000).unwrap();

        // 3) 计算预期的对齐范围和大小
        let astart = align_up(unaligned, ALIGN);
        let aend = align_down(unaligned + 0x2000, ALIGN);
        let size = aend - astart;
        let (fl, sl) = mapping(size);

        // 4) 验证 fl/sl 位图
        assert!((alloc.fl_bitmap & (1 << fl)) != 0, "fl 位应当被置1");
        assert!((alloc.sl_bitmap[fl] & (1 << sl)) != 0, "sl 位应当被置1");

        // 5) 拿到链表头并检查
        let freeopt = alloc.first_free[fl][sl];
        assert!(freeopt.is_some(), "first_free[{},{}] 一定有块", fl, sl);
        let hdr = unsafe { freeopt.unwrap().as_ref() }.common;
        assert_eq!(hdr.size(), size);
        assert!(hdr.is_free());
        assert!(hdr.prev_phys_block.is_none());
    }

    #[test]
    fn test_init_vs_add_memory() {
        // 1) 用一个固定大小的数组模拟「一大块内存」
        const BUFSZ: usize = 0x2000 + ALIGN;
        // 在栈上开 BUFSZ 字节，避免使用 Vec
        let mut buffer: [u8; BUFSZ] = [0; BUFSZ];
        let base = buffer.as_mut_ptr() as usize;
        // 偏移 3 字节以测试 align_up
        let unaligned = base + 3;

        // init 会 reset 并调用 add_memory
        let mut alloc1 = LabByteAllocator::new();
        alloc1.init(unaligned, 0x2000);

        let mut alloc2 = LabByteAllocator::new();
        alloc2.add_memory(unaligned, 0x2000).unwrap();

        // 两者行为等价：fl_bitmap/sl_bitmap/first_free 完全一样
        assert_eq!(alloc1.fl_bitmap, alloc2.fl_bitmap);
        assert_eq!(alloc1.sl_bitmap, alloc2.sl_bitmap);
        assert_eq!(alloc1.first_free, alloc2.first_free);
    }
}
