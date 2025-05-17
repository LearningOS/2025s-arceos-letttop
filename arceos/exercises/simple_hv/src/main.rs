#![cfg_attr(feature = "axstd", no_std)]
#![cfg_attr(feature = "axstd", no_main)]
#![feature(asm_const)]
#![feature(riscv_ext_intrinsics)]

extern crate alloc;
#[cfg(feature = "axstd")]
extern crate axstd as std;
#[macro_use]
extern crate axlog;

mod csrs;
mod loader;
mod regs;
mod sbi;
mod task;
mod vcpu;

use crate::regs::GprIndex::{A0, A1};
use axhal::mem::PhysAddr;
use csrs::defs::hstatus;
use csrs::{RiscvCsrTrait, CSR};
use loader::load_vm_image;
use riscv::register::{scause, sstatus, stval};
use sbi::SbiMessage;
use tock_registers::LocalRegisterCopy;
use vcpu::VmCpuRegisters;
use vcpu::_run_guest;

const VM_ENTRY: usize = 0x8020_0000;

#[cfg_attr(feature = "axstd", no_mangle)]
fn main() {
    ax_println!("Hypervisor ...");

    // 虚拟机地址空间
    // A new address space for vm.
    let mut uspace = axmm::new_user_aspace().unwrap();

    // 加载要在虚拟机运行的unikernal操作系统镜像
    // Load vm binary file into address space.
    if let Err(e) = load_vm_image("/sbin/skernel2", &mut uspace) {
        panic!("Cannot load app! {:?}", e);
    }

    // Setup context to prepare to enter guest mode.
    let mut ctx = VmCpuRegisters::default();
    prepare_guest_context(&mut ctx);

    // Setup pagetable for 2nd address mapping.
    let ept_root = uspace.page_table_root();
    prepare_vm_pgtable(ept_root);

    // Kick off vm and wait for it to exit.
    while !run_guest(&mut ctx) {}

    panic!("Hypervisor ok!");
}

fn prepare_vm_pgtable(ept_root: PhysAddr) {
    let hgatp = 8usize << 60 | usize::from(ept_root) >> 12;
    unsafe {
        core::arch::asm!(
            "csrw hgatp, {hgatp}",
            hgatp = in(reg) hgatp,
        );
        core::arch::riscv64::hfence_gvma_all();
    }
}

fn run_guest(ctx: &mut VmCpuRegisters) -> bool {
    unsafe {
        // _run_guest汇编以sret结尾
        // 即在这里会从HS进入VS模式

        _run_guest(ctx);
        // 同时设置了stvec为_guest_exit
        // 即VS模式下的trap handler是_guest_exit
        // 当trap时特权级切换到HS模式
        // 然后_guest_exit会恢复HS的寄存器
        // 最后ret继续运行下一条指令
    }

    // 在HS模式下处理trap
    vmexit_handler(ctx)
}

#[allow(unreachable_code)]
fn vmexit_handler(ctx: &mut VmCpuRegisters) -> bool {
    use scause::{Exception, Trap};

    let scause = scause::read();
    match scause.cause() {
        // VS模式下遇到的syscall，需要处理部分
        Trap::Exception(Exception::VirtualSupervisorEnvCall) => {
            let sbi_msg = SbiMessage::from_regs(ctx.guest_regs.gprs.a_regs()).ok();
            ax_println!("VmExit Reason: VSuperEcall: {:?}", sbi_msg);
            if let Some(msg) = sbi_msg {
                match msg {
                    SbiMessage::Reset(_) => {
                        let a0 = ctx.guest_regs.gprs.reg(A0);
                        let a1 = ctx.guest_regs.gprs.reg(A1);
                        ax_println!("a0 = {:#x}, a1 = {:#x}", a0, a1);
                        assert_eq!(a0, 0x6688);
                        assert_eq!(a1, 0x1234);
                        ax_println!("Shutdown vm normally!");
                        return true;
                    }
                    _ => todo!(),
                }
            } else {
                panic!("bad sbi message! ");
            }
        }
        // 情况1的报错
        // 错在"csrr a1, mhartid"
        // 忽略并增加一条指令
        Trap::Exception(Exception::IllegalInstruction) => {
            ax_println!(
                "Bad instruction: {:#x} sepc: {:#x}",
                stval::read(),
                ctx.guest_regs.sepc
            );
            ctx.guest_regs.gprs.a_regs_mut()[0] = 0x6688;
            ctx.guest_regs.sepc += 4;
        }
        Trap::Exception(Exception::LoadGuestPageFault) => {
            ax_println!(
                "LoadGuestPageFault: stval{:#x} sepc: {:#x}",
                stval::read(),
                ctx.guest_regs.sepc
            );
            ctx.guest_regs.gprs.a_regs_mut()[1] = 0x1234;
            ctx.guest_regs.sepc += 4;
        }
        _ => {
            panic!(
                "Unhandled trap: {:?}, sepc: {:#x}, stval: {:#x}",
                scause.cause(),
                ctx.guest_regs.sepc,
                stval::read()
            );
        }
    }
    false
}

// 设置hstatus寄存器
// 1. 设置Guest bit, 使能返回VS模式
// 2. 设置SPVP bit, 使能在HS访问VS内存
fn prepare_guest_context(ctx: &mut VmCpuRegisters) {
    // Set hstatus
    let mut hstatus =
        LocalRegisterCopy::<usize, hstatus::Register>::new(riscv::register::hstatus::read().bits());
    // Set Guest bit in order to return to guest mode.
    hstatus.modify(hstatus::spv::Guest);
    // Set SPVP bit in order to accessing VS-mode memory from HS-mode.
    hstatus.modify(hstatus::spvp::Supervisor);
    CSR.hstatus.write_value(hstatus.get());
    ctx.guest_regs.hstatus = hstatus.get();

    // Set sstatus in guest mode.
    let mut sstatus = sstatus::read();
    sstatus.set_spp(sstatus::SPP::Supervisor);
    ctx.guest_regs.sstatus = sstatus.bits();
    // Return to entry to start vm.
    ctx.guest_regs.sepc = VM_ENTRY;
}
