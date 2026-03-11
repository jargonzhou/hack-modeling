# Concurrent and Parallel
* [Concurrent_Parallel.ipynb](./Concurrent_Parallel.ipynb)

books
* Breshears, Clay. **The Art of Concurrency**. 2009. O’Reilly.
* aipp: Pacheco, Peter / Malensek, Matthew. **An Introduction to Parallel Programming**. 2021, 2. edition. Morgan Kaufmann.
* tamp: Herlihy, Maurice / Shavit, Nir / Luchangco, Victor / Spear, Michael. **The Art of Multiprocessor Programming**. 2021, 2. edition. Morgan Kaufmann.
* Bobrov, Kirill. **Grokking Concurrency**. 2023. Manning.
* Manna, Z. & Pnueli, A. **The Temporal Logic of Reactive and Concurrent Systems**. Springer Scienee+Business. Media, 1992.
* Ben, M. **Principles of concurrent and distributed programming**. 2006, 2. edition. Addison-Wesley.
	* 并发程序验证(verification), code in Ada, Promela.


actions
* [Pthreads.ipynb](./Pthreads.ipynb)
* [OpenMP.ipynb](./OpenMP.ipynb)
* [MPI.ipynb](./MPI.ipynb)
* [CUDA.ipynb](./CUDA.ipynb)
* [Java Concurrency](./Java%20Concurrency.ipynb)
* [Python asyncio.ipynb](./Python%20asyncio.ipynb)
* [performance.ipynb](./performance.ipynb)
* [Erlang](./Erlang/Erlang.md)

# Abstraction

## Process Algebras

CCS (Calculus of Communicating Systems):
* Milner, R., A Calculus for Communicating Systems, Lecture Notes in Computer Science, Vol. 92, Springer, 1980.
* Milner, R., Communication and Concurrency, Prentice Hall, 1989.

CSP (Communicating Sequential Process):
* Hoare C.A.R., **Communicating Sequential Processes**, Prentice- Hall, 1985, 256 pages, ISBN 0-13-153271-5. [http://www.usingcsp.com/cspbook.pdf](http://www.usingcsp.com/cspbook.pdf).
* **Theory of Concurrency** page of Oxford: [https://www.cs.ox.ac.uk/activities/concurrency/research/theory/](https://www.cs.ox.ac.uk/activities/concurrency/research/theory/)
* A.W. Roscoe. **The Theory and Practice of Concurrency**, Prentice-Hall: 2005.

## STM(Software Transactional Memory)

* [more - wikipedia](https://en.wikipedia.org/wiki/Software_transactional_memory): ex Clojure Refs

# Temporal Logic

# Verification

# Parallel Programming

> Parallel computing is a type of computation in which many calculations or processes are carried out simultaneously. Large problems can often be divided into smaller ones, which can then be solved at the same time. There are several different forms of parallel computing: bit-level, instruction-level, data, and task parallelism. Parallelism has long been employed in high-performance computing, but has gained broader interest due to the physical constraints preventing frequency scaling. As power consumption (and consequently heat generation) by computers has become a concern in recent years, parallel computing has become the dominant paradigm in computer architecture, mainly in the form of multi-core processors.

Terminology
* CUDA: Compute Unified Device Architecture.
* Distributed-memory programming: 分布式内存编程.
* HPC: high performance computing, 高性能计算.
* ILP: instruction level parallelism, 指令级并行.
* MIMD: 多指令多数据.
* OpenCL: Open Computing Language.
* parallel: 并行.
* Share-memory programming: 共享内存编程.
* SIMD: 单指令多数据.
* SPMD: 单程序多数据.

Books:

* James Reinders, Jim Jeffers. **High Performance Parallelism Pearls: Multicore and Many-core Programming Approaches**. Morgan Kaufmann. 2015.
* McKenney, Paul E. **Is Parallel Programming Hard, And, If So, What Can You Do About It?**. 2017.
* Pacheco, Peter / Malensek, Matthew. **An Introduction to Parallel Programming**. 2021, 2. edition. Morgan Kaufmann.
* Robey, Robert / Zamora, Yuliana. **Parallel and High Performance Computing**. 2021. Manning.

Model and Tools:

* [Parallel programming model - wikipedia](https://en.wikipedia.org/wiki/Parallel_programming_model)
* Kasim, Henry / March, Verdi / Zhang, Rita / See, Simon. **Survey on Parallel Programming Model**. 2008. IFIP International Federation for Information Processing.
  - 模型评估条件: (i) system architecture, (ii) programming methodologies, (iii) worker management, (iv) workload partitioning scheme, (v) task-to-worker mapping, (vi) synchronization, (vii) communication model.
  - 模型: Pthreads, OpenMP, MPI, UPC, Fortress, CUDA.
* Diaz, Javier / Munoz-Caro, Camelia / Nino, Alfonso. **A survey of parallel programming models and tools in the multi and many-core era**. 2012. IEEE Transactions on parallel and distributed systems , Vol. 23, No. 8. IEEE. p. 1369-1386.
  - 并行编程模型分类:
    - pure parallel models: Pthreads, OpenMP, MPI.
    - heterogeneous parallel programming models: CUDA, OpenCL, DirectCompute(Microsoft), Array Building Blocks(Intel).
    - Partitioned Global Address Space(PGAS) model
    - hybrid, shared-distributed memory + GPU models
  - 支持并行的语言: Java, High Performance Fortran(HPF), Cilk, Z-level Programming Language(ZPL), Erlang, Glasgow parallel Haskell(GpH)

actions - Windows WSL
* `MPI.ipynb`
* `Pthreads.ipynb`
* `OpenMP.ipynb`
* `CUDA.ipynb`: NO NVIDIA GPU currently.


# See Also
* Coffman, Edward G. Jr.; Elphick, Michael J.; Shoshani, Arie. **System Deadlocks**. 1971. - Coffman conditions, [Deadlock (computer science) - wikipedia](https://en.wikipedia.org/wiki/Deadlock_(computer_science))
* C. A. R. Hoare. [Communicating Sequential Processes](https://dl.acm.org/doi/pdf/10.1145/359576.359585), 1978.
