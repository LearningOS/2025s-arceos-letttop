#![allow(dead_code)]

use axerrno::LinuxError;
use axhal::arch::TrapFrame;
use axhal::trap::{register_trap_handler, PAGE_FAULT, SYSCALL};

const SYS_EXIT: usize = 93;

#[register_trap_handler(SYSCALL)]
fn handle_syscall(tf: &TrapFrame, syscall_num: usize) -> isize {
    ax_println!("handle_syscall ...");
    let ret = match syscall_num {
        SYS_EXIT => {
            ax_println!("[SYS_EXIT]: process is exiting ..");
            axtask::exit(tf.arg0() as _)
        }
        _ => {
            ax_println!("Unimplemented syscall: {}", syscall_num);
            -LinuxError::ENOSYS.code() as _
        }
    };
    ret
}

use axhal::mem::VirtAddr;
use axhal::paging::MappingFlags;
use axtask::TaskExtRef;
#[register_trap_handler(PAGE_FAULT)]
fn handle_page_fault(vaddr: VirtAddr, mut access_flags: MappingFlags, is_user: bool) -> bool {
    if is_user {
        access_flags |= MappingFlags::USER;
    }
    axtask::current()
        .task_ext()
        .aspace
        .lock()
        .handle_page_fault(vaddr, access_flags)
}
