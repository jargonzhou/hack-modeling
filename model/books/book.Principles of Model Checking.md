# Principles of Model Checking
* Christel Baier, Joost-Pieter Katoen. **Principles of Model Checking**. MIT Press: 2008.


# 1 System Verification
## 1.1 Model Checking
## 1.2 Characteristics ofModel Checking
### 1.2.1 TheModel-Checking Process
### 1.2.2 Strengths and Weaknesses

# 2 Modelling Concurrent Systems
## 2.1 Transition Systems
### 2.1.1 Executions
### 2.1.2 Modeling Hardware and Software Systems
## 2.2 Parallelism and Communication
### 2.2.1 Concurrency and Interleaving
### 2.2.2 Communication via Shared Variables
### 2.2.3 Handshaking
### 2.2.4 Channel Systems
### 2.2.5 NanoPromela
### 2.2.6 Synchronous Parallelism
## 2.3 The State-Space Explosion Problem

# 3 Linear-Time Properties
## 3.1 Deadlock
## 3.2 Linear-Time Behavior
### 3.2.1 Paths and State Graph
### 3.2.2 Traces
### 3.2.3 Linear-Time Properties
### 3.2.4 Trace Equivalence and Linear-Time Properties
## 3.3 Safety Properties and Invariants
### 3.3.1 Invariants
### 3.3.2 Safety Properties
### 3.3.3 Trace Equivalence and Safety Properties
## 3.4 Liveness Properties
### 3.4.1 Liveness Properties
### 3.4.2 Safety vsLiveness Properties
## 3.5 Fairness
### 3.5.1 Fairness Constraints
### 3.5.2 Fairness Strategies
### 3.5.3 Fairness and Safety

# 4 Regular Properties
## 4.1 Automata on FiniteWords
## 4.2 Model-Checking Regular Safety Properties
### 4.2.1 Regular Safety Properties
### 4.2.2 Verifying Regular Safety Properties
## 4.3 Automata on Infinite Words
### 4.3.1 ω-Regular Languages and Properties
### 4.3.2 Nondeterministic Buchi Automata
### 4.3.3 Deterministic Buchi Automata
### 4.3.4 Generalized Buchi Automata
## 4.4 Model-Checking ω-Regular Properties
### 4.4.1 Persistence Properties and Product
### 4.4.2 Nested Depth-First Search

# 5 Linear Temporal Logic
## 5.1 Linear Temporal Logic
### 5.1.1 Syntax
### 5.1.2 Semantics
### 5.1.3 Specifying Properties
### 5.1.4 Equivalence of LTL Formulae
### 5.1.5 Weak Until, Release, and Positive Normal Form
### 5.1.6 Fairness in LTL
## 5.2 Automata-Based LTLModel Checking .270
### 5.2.1 Complexity of the LTLModel-Checking Problem
### 5.2.2 LTL Satisfiability and Validity Checking


# 6 Computation Tree Logic
## 6.1 Introduction
## 6.2 Computation Tree Logic
### 6.2.1 Syntax
### 6.2.2 Semantics
### 6.2.3 Equivalence of CTL Formulae
### 6.2.4 Normal Forms for CTL
## 6.3 Expressiveness of CTL vsLTL
## 6.4 CTLModel Checking
### 6.4.1 Basic Algorithm
### 6.4.2 The Until and Existential Always Operator
### 6.4.3 Time and Space Complexity
## 6.5 Fairness in CTL
## 6.6 Counterexamples andWitnesses
### 6.6.1 Counterexamples in CTL
### 6.6.2 Counterexamples andWitnesses in CTL with Fairness
## 6.7 Symbolic CTLModel Checking
### 6.7.1 Switching Functions
### 6.7.2 Encoding Transition Systems by Switching Functions
### 6.7.3 Ordered Binary Decision Diagrams
### 6.7.4 Implementation of ROBDD-Based Algorithms
## 6.8 CTL∗
### 6.8.1 Logic, Expressiveness, and Equivalence
### 6.8.2 CTL∗ Model Checking

# 7 Equivalences and Abstraction
## 7.1 Bisimulation
### 7.1.1 Bisimulation Quotient
### 7.1.2 Action-Based Bisimulation
## 7.2 Bisimulation and CTL∗ Equivalence
## 7.3 Bisimulation-Quotienting Algorithms
### 7.3.1 Determining the Initial Partition
### 7.3.2 Refining Partitions
### 7.3.3 A First Partition Refinement Algorithm
### 7.3.4 An Efficiency Improvement
### 7.3.5 Equivalence Checking of Transition Systems
## 7.4 Simulation Relations
### 7.4.1 Simulation Equivalence
### 7.4.2 Bisimulation, Simulation, and Trace Equivalence
## 7.5 Simulation and ∀CTL∗ Equivalence
## 7.6 Simulation-Quotienting Algorithms
## 7.7 Stutter Linear-Time Relations
### 7.7.1 Stutter Trace Equivalence
### 7.7.2 Stutter Trace and LTL Equivalence
## 7.8 Stutter Bisimulation
### 7.8.1 Divergence-Sensitive Stutter Bisimulation
### 7.8.2 Normed Bisimulation
### 7.8.3 Stutter Bisimulation and CTL∗ Equivalence
### 7.8.4 Stutter Bisimulation Quotienting


# 8 Partial Order Reduction
## 8.1 Independence of Actions
## 8.2 The Linear-Time Ample Set Approach
### 8.2.1 Ample Set Constraints
### 8.2.2 Dynamic Partial Order Reduction
### 8.2.3 Computing Ample Sets
### 8.2.4 Static Partial Order Reduction
## 8.3 The Branching-Time Ample Set Approach

# 9 Timed Automata
## 9.1 Timed Automata
### 9.1.1 Semantics
### 9.1.2 Time Divergence, Timelock, and Zenoness
## 9.2 Timed Computation Tree Logic
## 9.3 TCTL Model Checking
### 9.3.1 Eliminating Timing Parameters
### 9.3.2 Region Transition Systems
### 9.3.3 The TCTL Model-Checking Algorithm


# 10 Probabilistic Systems
## 10.1 Markov Chains
### 10.1.1 Reachability Probabilities
### 10.1.2 Qualitative Properties
## 10.2 Probabilistic Computation Tree Logic
### 10.2.1 PCTLModel Checking
### 10.2.2 The Qualitative Fragment of PCTL
## 10.3 Linear-Time Properties
## 10.4 PCTL∗ and Probabilistic Bisimulation
### 10.4.1 PCTL∗
### 10.4.2 Probabilistic Bisimulation
## 10.5 Markov Chains with Costs
### 10.5.1 Cost-Bounded Reachability
### 10.5.2 Long-Run Properties
## 10.6 Markov Decision Processes
### 10.6.1 Reachability Probabilities
### 10.6.2 PCTLModel Checking
### 10.6.3 Limiting Properties
### 10.6.4 Linear-Time Properties and PCTL∗
### 10.6.5 Fairness

# A Appendix: Preliminaries
## A.1 Frequently Used Symbols and Notations
## A.2 Formal Languages
## A.3 Propositional Logic
## A.4 Graphs
## A.5 Computational Complexity
