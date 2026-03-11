# Compiler
* https://en.wikipedia.org/wiki/Compiler

> In computing, a compiler is a computer program that translates computer code written in one programming language (the source language) into another language (the target language). The name "compiler" is primarily used for programs that translate source code from a high-level programming language to a low-level programming language (e.g. assembly language, object code, or machine code) to create an executable program

books
* Aho, Alfred V. / Ullman, Jeffrey D. **The Theory of Parsing, Translation, and Compiling**. 1972. Prentice-Hall, Inc.
* Aho, Alfred V. / Lam, Monica S. / Sethi, Ravi / Ullman, Jeffrey D. **Compilers: Principles, Techniques, and Tools**. 2007, 2. edition. Pearson. - 龙书
* Srikant, Y. N. / Shankar, Priti. **The Compiler Design Handbook: Optimizations and Machine Code Generation**. 2007, 2. edition. CRC Press.
* Cooper, Keith D. / Torczon, Linda. **Engineering a Compiler**. 2012, 2. edition. Elsevier.

# AST: Abstract Syntax Tree

# Ad Hoc Syntax-Directed Translation

# Attribute-Grammar Framework

# BNF: Backus-Naur Form, 巴科斯范式

* [more](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form)

# Bottom-Up Parsing

# Code Shape

# Compiler Structure

* Input: source program
* Output: target program
* Components
  * Front End
    * Scanner
    * Parser
  * Optimizer: an IR-to-IR transformer.
  * Back End
    * Instruction Selection
    * Instruction Scheduling
    * Register Allocation
* Data Structure
  * IR

# Computer Architecture
* [Computer Architecture](./Computer%20Architecture//Computer%20Architecture.md)

# CFG: Context-Free Grammar

# DFA

# Data-Flow Analysis

# GC: Garbage Collection

# Grammar, 文法

# Instruction Scheduling

**Instruction scheduling** aims to reorder the operations in a procedure to reduce its running time.

approaches:

* Greedy List Scheduling

# Instruction Selection

The process of mapping IR operations into target machine operations is calledd **instruction selection**.

approaches:

* Tree-Pattern Matching
* Peephole Optimization

# IR: Intermediate Representation

# LL

# LR

# NFA

# Optimization

# Parse Tree

# Parser

# Procedure

# Register Allocation

Hardware registers are constrained resources, compilers usually include a pass that allocation and assign registers to program values.

approaches:

* Graph Coloring

# Regular Expression

# Scalar Optimization

# Scanner

# SSA: Static Single-Assignment

# Symbol Table

# Syntax

# Top-Down Parsing

# Type Inference

# Type System