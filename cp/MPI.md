# MPI
* https://www.mpi-forum.org/
* [Open MPI](https://www.open-mpi.org/)
  * [FAQ](https://www.open-mpi.org/faq/?category=running#simple-spmd-run): such as running on multiple nodes
* [MPI Testing Tool](https://github.com/open-mpi/mtt)

> MPI (Message-Passing Interface) is a message-passing library interface specification.

nooks:
* [Using MPI and Using Advanced MPI](http://wgropp.cs.illinois.edu/usingmpiweb/)

actions
* [](./MPI.ipynb)

# Terminology

* communication: 通信
  * broadcast: 广播.
  * collective communication: 集体通信.
  * gather: 收集.
  * point-to-point communication: 点对点通信.
  * scatter: 分散.
* communicator: 通信器.
* derived datatype: 衍生的数据类型.

# Implementation

## Open MPI

* [Home](https://www.open-mpi.org/)

The Open MPI Project is an open source Message Passing Interface implementation that is developed and maintained by a consortium of academic, research, and industry partners. Open MPI is therefore able to combine the expertise, technologies, and resources from all across the High Performance Computing community in order to build the best MPI library available. Open MPI offers advantages for system and software vendors, application developers and computer science researchers.

Features implemented or in short-term development for Open MPI include:

* Full MPI-3.1 standards conformance
* Thread safety and concurrency
* Dynamic process spawning
* Network and process fault tolerance
* Support network heterogeneity
* Single library supports all networks
* Run-time instrumentation
* Many job schedulers supported
* Many OS's supported (32 and 64 bit)
* Production quality software
* High performance on all platforms
* Portable and maintainable
* Tunable by installers and end-users
* Component-based design, documented APIs
* Active, responsive mailing list
* Open source license based on the BSD license

## MPICH

* [Home](https://www.mpich.org/)

MPICH is a high performance and widely portable implementation of the Message Passing Interface (MPI) standard.

## Microsoft MPI

* [Code](https://github.com/Microsoft/Microsoft-MPI)

Microsoft MPI (MS-MPI) is a Microsoft implementation of the Message Passing Interface standard for developing and running parallel applications on the Windows platform.
