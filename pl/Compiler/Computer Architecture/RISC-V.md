# RISC-V
* https://riscv.org/
* [RISC-V Technical Specifications](https://lf-riscv.atlassian.net/wiki/spaces/HOME/pages/16154769/RISC-V+Technical+Specifications)
    * The RISC-V Instruction Set Manual Volume I: Unprivileged ISA
    * The RISC-V Instruction Set Manual Volume II: Privileged Architecture
    * RVA23 Profile
    * RVB23 Profile
    * RISC-V Profiles
    * Non-ISA Specifications ...
    * Compatibility Test Framework ...

RISC-V (pronounced "risk-five") is a new instruction-set architecture (ISA) that was originally designed to support computer architecture research and education, but which we now hope will also become a standard free and open architecture for industry implementations. Our goals in defining RISC-V include:

* A completely open ISA that is freely available to academia and industry.
* A real ISA suitable for direct native hardware implementation, not just simulation or binary translation.
* An ISA that avoids "over-architecting" for a particular microarchitecture style (e.g., microcoded, in-order, decoupled, out-of-order) or implementation technology (e.g., full-custom, ASIC, FPGA), but which allows efficient implementation in any of these.
* An ISA separated into a small base integer ISA, usable by itself as a base for customized accelerators or for educational purposes, and optional standard extensions, to support general-purpose software development.
* Support for the revised 2008 IEEE-754 floating-point standard. (ANSI/IEEE Std 754-2008, IEEE Standard for Floating-Point Arithmetic, 2008)
* An ISA supporting extensive ISA extensions and specialized variants.
* Both 32-bit and 64-bit address space variants for applications, operating system kernels, and hardware implementations.
* An ISA with support for highly parallel multicore or manycore implementations, including heterogeneous multiprocessors. 
* Optional variable-length instructions to both expand available instruction encoding space and to support an optional dense instruction encoding for improved performance, static code size, and energy efficiency. 
* A fully virtualizable ISA to ease hypervisor development. 
* An ISA that simplifies experiments with new privileged architecture designs.


# RISC-V Assembly Programming
* Borin, Edson. An Introduction to Assembly Programming with RISC-V. 2021
  * [RISC-V Assembly Learn Environment(ALE)](https://riscv-programming.org/simulator.html)

# See Also
* Patterson, David / Waterman, Andrew. **The RISC-V Reader: An Open Architecture Atlas**. 2017, 1. edition.
