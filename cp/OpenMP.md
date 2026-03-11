# OpenMP: Open Multi-Processing
* https://www.openmp.org/
* [Specifications](https://www.openmp.org/specifications/)
  * [OpenMP 4.5 Reference Guide - C/C++](https://www.openmp.org/wp-content/uploads/OpenMP-4.5-1115-CPP-web.pdf): 指令和构造, 运行时库例程, 子句, 环境变量, ICV(Internal Control Variables, 内部控制变量)的环境变量值
* [OpemMP Compilers & Tools](https://www.openmp.org/resources/openmp-compilers-tools/)
  * [GNU Offloading and Multi-Processing Project (GOMP)](https://gcc.gnu.org/projects/gomp/): 选项`-fopenmp`, `-fopenmp-simd`

> What is OpenMP(Open Multi-Processing)?
>
> OpenMP is a specification for a set of compiler directives, library routines, and environment variables that can be used to specify high-level parallelism in Fortran and C/C++ programs.

actions
* [OpenMP.ipynb](./OpenMP.ipynb)

# Terminology

* `_OPENMP`: OpenMP的预处理器宏.
* `#pragma omp`指令: OpenMP预处理器指令.
* `omp.h`: OpenMP的头文件.
* Barrier: 栅栏.
  * Implicit barrier: 隐式栅栏. 结束执行`parallel`块的线程会等待team中其它线程执行完成.
  * Explicit barrier: 显式栅栏.
* Clause: 子句.
  * `reduction`: 规约.
    * Reduction operator: 规约操作符.
    * Reduction variable: 规约变量.
  * `default(none)`: 需要显式设置变量的作用域.
  * `private`: 变量私有作用域.
  * `shared`: 变量共享作用域.
  * `schedule`: 调度循环.
* Data dependency: 数据依赖
* Directive: 指令.
  * `atomic`: 原子指令.
  * `barrier`: 栅栏指令.
  * `critical`: 关键区域指令.
  * `for`: 在已存在的team中并行化for循环.
  * `parallel`: 并行执行指令.
  * `parallel for`: 并行循环指令.
  * `single`: 使用单个线程执行任务的指令.
  * `task`: 任务指令.
  * `taskwait`: 等待子任务完成的指令.
* Directives-based shared-memory API: 基于指令的共享内存API.
* Lock: 锁
  * Simple lock: 简单锁.
  * Nested lock: 嵌套锁.
* Loop-carried dependence: 循环产生的依赖.
* Scheduling loops: 调度循环, 将循环中迭代指派给线程.
* Scope of variable: 变量的作用域. 在OpenMP中, 变量的作用域引用了可以访问`parallel`块中的线程集合.
  * Private scope: 私有作用域.
  * Shared scope: 共享作用域.
* Structured block: 结构化块. 单个C语句或复合C语句, 只有单个入口和单个出口, 但允许调用`exit`函数.
* Tasking: 任务化.
* Team: OpenMP中执行`parallel`块的线程集合.
* Thread: thread of execution, 执行线程.

# 变量作用域

* 在`parallel`块之前声明的变量的默认作用域是共享的.
* 在`parallel`块中调用的函数中声明的变量作用域是私有的.
* 修改默认作用域的子句: `deault`, `private`, `shared`.

Tasking:

* 任务中的变量默认作用域是私有的.

# See Also
* [GCC Wiki - OpenMP](https://gcc.gnu.org/wiki/openmp)
* [ACENET workshop on OpenMP](https://acenet-arc.github.io/ACENET_Summer_School_OpenMP/)