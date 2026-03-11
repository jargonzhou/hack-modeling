# Introduction to Automata Theory, Languages, and Computation

action: `JFLAP/iatlc`

# 1 Automata: The Methods and the Madness

## 1.1 Why Study Automata Theory?
### 1.1.1 Introduction to Finite Automata
### 1.1.2 Structural Representations
### 1.1.3 Automata and Complexity

## 1.2 Introduction to Formal Proof
### 1.2.1 Deductive Proofs
### 1.2.2 Reduction to Definitions
### 1.2.3 Other Theorem Forms
### 1.2.4 Theorems That Appear Not to Be If-Then Statements

## 1.3 Additional Forms of Proof
### 1.3.1 Proving Equivalences About Sets
### 1.3.2 The Contrapositive
### 1.3.3 Proof by Contradiction
### 1.3.4 Counterexamples

## 1.4 Inductive Proofs
### 1.4.1 Inductions on Integers
### 1.4.2 More General Forms of Integer Inductions
### 1.4.3 Structural Inductions
### 1.4.4 Mutual Inductions

## 1.5 The Central Concepts of Automata Theory
### 1.5.1 Alphabets
### 1.5.2 Strings
### 1.5.3 Languages
### 1.5.4 Problems

# 2 Finite Automata

## 2.1 An Informal Picture of Finite Automata
### 2.1.1 The Ground Rules
### 2.1.2 The Protocol
### 2.1.3 Enabling the Automata to Ignore Actions
### 2.1.4 The Entire System as an Automaton
### 2.1.5 Using the Product Automaton to Validate the Protocol

## 2.2 Deterministic Finite Automata
### 2.2.1 Definition of a Deterministic Finite Automaton

$A = (Q, \Sigma, \delta, q_{0}, F)$

A deterministic finite automaton consists of 

1. $Q$: a finite set of **states**.
2. $\Sigma$: a finite set of **input symbols**.
3. $\delta$: a **transition function** that takes as arguments as a state and an input symbol and returens a state. $\delta(q, a)$ is that state $p$ such that there is an arc labeled symbol $a$ from state $q$ to $p$.
4. a **start state** $q_{0}$, one of the states in $Q$.
5. $F$: a set of **final** or **accepting** states. The set $F$ is a subset of $Q$.

### 2.2.2 How a DFA Processes Strings
### 2.2.3 Simpler Notations for DFA's

There are 2 preferred notations for describing automata:

1. A **transition diagram**,
2. A **transition table**, which is a tabular listing of the $\delta$ function, which by implication tells us the set of states and the input alphabet.

A transition diagram for a DFA $A = (Q, \Sigma, \delta, q_{0}, F)$ is a graph defined as follows:

a) For each state in $Q$, there is a node.

b) For each state $q$ in $Q$ and each input symbol $a$ in $\Sigma$, let $\delta(q, a) = p$.
Then the transition diagram has an arc from node $q$ to node $p$, labeled $a$.
If there are several input symbols that cause transition from $q$ to $p$, then the transition diagram can have one arc, labelled by the list of these symbols.

c) There is an arrow into the start state $q_{0}$, labeled **Start**.
This arrow does not originate at any node.

d) Nodes corresponding to accepting states (those in $F$) are marked by a double circle.
States not in $F$ have a single circle.

### 2.2.4 Extending the Transition Function to Strings

$\delta$ is the transition function, the extended transition function $\hat{\delta}$ is a fuction that takes a state $q$ and a string $w$ and returns a state $p$ - the state that the automaton reaches when starting in state $q$ and processing the sequence of inputs $w$.

We define $\hat{\delta}$ by induction on the length of the input string:

- **BASIC**: $\hat{\delta}(q, \epsilon) = q$. That is, if we are in state $q$ and read no inputs, then we are still in state $q$.
- **INDUCTION**: Suppose $w$ is a string of the form $xa$, that is, $a$ is the last symbol of $w$, and $x$ is the string consisting of all but the last symbol. For example, $w = 1101$ is broken into $x = 110$ and $a = 1$. Then $\hat{\delta}(q, w) = \delta(\hat{\delta}(q, x), a)$.


### 2.2.5 The Language of a DFA

The **language** of a DFA $A = (Q, \Sigma, \delta, q_{0}, F)$ is denoted by $L(A)$:

$$
L(A) = \left \{ w \mid \hat{\delta}(q_{0}, w) \ is \ in \ F \right \}
$$

That is, the language of $A$ is the set of strings $w$ that take the start state $q_{0}$ to one of the accepting states.

If $L$ is $L(A)$ for some DFA $A$, then we say $L$ is a **regular language**.

## 2.3 Nondeterministic Finite Automata
### 2.3.1 An Informal View of Nondeterministic Finite Automata
### 2.3.2 Definition of Nondeterministic Finite Automata
### 2.3.3 The Extended Transition Function
### 2.3.4 The Language of an NFA
### 2.3.5 Equivalence of Deterministic and Nondeterministic Finite Automata
### 2.3.6 A Bad Case for the Subset Construction

## 2.4 An Application: Text Search
### 2.4.1 Finding Strings in Text
### 2.4.2 Nondeterministic Finite Automata for Text Search
### 2.4.3 A DFA to Recognize a Set of Keywords

## 2.5 Finite Automata With Epsilon-Transitions
### 2.5.1 Uses of \epsilon -Transitions
### 2.5.2 The Formal Notation for an \epsilon -NFA
### 2.5.3 Epsilon-Closures
### 2.5.4 Extended Transitions and Languages for \epsilon -NFA's
### 2.5.5 Eliminating \epsilon -Transitions


# 3 Regular Expressions and Languages
## 3.1 Regular Expressions
### 3.1.1 The Operators of Regular Expressions
### 3.1.2 Building Regular Expressions
### 3.1.3 Precedence of Regular-Expression Operators
## 3.2 Finite Automata and Regular Expressions
### 3.2.1 From DFA's to Regular Expressions
### 3.2.2 Converting DFA's to Regular Expressions by Eliminating States
### 3.2.3 Converting Regular Expressions to Automata
## 3.3 Applications of Regular Expressions
### 3.3.1 Regular Expressions in UNIX
### 3.3.2 Lexical Analysis
### 3.3.3 Finding Patterns in Text
## 3.4 Algebraic Laws for Regular Expressions
### 3.4.1 Associativity and Commutativity
### 3.4.2 Identities and Annihilators
### 3.4.3 Distributive Laws
### 3.4.4 The Idempotent Law
### 3.4.5 Laws Involving Closures
### 3.4.6 Discovering Laws for Regular Expressions
### 3.4.7 The Test for a Regular-Expression Algebraic Law

# 4 Properties of Regular Languages
## 4.1 Proving Languages Not to Be Regular
### 4.1.1 The Pumping Lemma for Regular Languages
### 4.1.2 Applications of the Pumping Lemma
## 4.2 Closure Properties of Regular Languages
### 4.2.1 Closure of Regular Languages Under Boolean Operations
### 4.2.2 Reversal
### 4.2.3 Homomorphisms
### 4.2.4 Inverse Homomorphisms
## 4.3 Decision Properties of Regular Languages
### 4.3.1 Converting Among Representations
### 4.3.2 Testing Emptiness of Regular Languages
### 4.3.3 Testing Membership in a Regular Language
## 4.4 Equivalence and Minimization of Automata
### 4.4.1 Testing Equivalence of States
### 4.4.2 Testing Equivalence of Regular Languages
### 4.4.3 Minimization of DFA's
### 4.4.4 Why the Minimized DFA Can't Be Beaten

# 5 Context-Free Grammars and Languages
## 5.1 Context-Free Grammars
### 5.1.1 An Informal Example
### 5.1.2 Definition of Context-Free Grammars
### 5.1.3 Derivations Using a Grammar
### 5.1.4 Leftmost and Rightmost Derivations
### 5.1.5 The Language of a Grammar
### 5.1.6 Sentential Forms
## 5.2 Parse Trees
### 5.2.1 Constructing Parse Trees
### 5.2.2 The Yield of a Parse Tree
### 5.2.3 Inference, Derivations, and Parse Trees
### 5.2.4 From Inferences to Trees
### 5.2.5 From Trees to Derivations
### 5.2.6 From Derivations to Recursive Inferences
## 5.3 Applications of Context-Free Grammars
### 5.3.1 Parsers
### 5.3.2 The YACC Parser-Generator
### 5.3.3 Markup Languages
### 5.3.4 XML and Document-Type Definitions
## 5.4 Ambiguity in Grammars and Languages
### 5.4.1 Ambiguous Grammars
### 5.4.2 Removing Ambiguity From Grammars
### 5.4.3 Leftmost Derivations as a Way to Express Ambiguity
### 5.4.4 Inherent Ambiguity

# 6 Pushdown Automata
## 6.1 Definition of the Pushdown Automaton
### 6.1.1 Informal Introduction
### 6.1.2 The Formal Definition of Pushdown Automata
### 6.1.3 A Graphical Notation for PDA's
### 6.1.4 Instantaneous Descriptions of a PDA
## 6.2 The Languages of a PDA
### 6.2.1 Acceptance by Final State
### 6.2.2 Acceptance by Empty Stack
### 6.2.3 From Empty Stack to Final State
### 6.2.4 From Final State to Empty Stack
## 6.3 Equivalence of PDA's and CFG's
### 6.3.1 From Grammars to Pushdown Automata
### 6.3.2 From PDA's to Grammars
## 6.4 Deterministic Pushdown Automata
### 6.4.1 Definition of a Deterministic PDA
### 6.4.2 Regular Languages and Deterministic PDA's
### 6.4.3 DPDA's and Context-Free Languages
### 6.4.4 DPDA's and Ambiguous Grammars

# 7 Properties of Context-Free Languages
## 7.1 Normal Forms for Context-Free Grammars
### 7.1.1 Eliminating Useless Symbols
### 7.1.2 Computing the Generating and Reachable Symbols
### 7.1.3 Eliminating \epsilon -Productions
### 7.1.4 Eliminating Unit Productions
### 7.1.5 Chomsky Normal Form
## 7.2 The Pumping Lemma for Context-Free Languages
### 7.2.1 The Size of Parse Trees
### 7.2.2 Statement of the Pumping Lemma
### 7.2.3 Applications of the Pumping Lemma for CFL's
## 7.3 Closure Properties of Context-Free Languages
### 7.3.1 Substitutions
### 7.3.2 Applications of the Substitution Theorem
### 7.3.3 Reversal
### 7.3.4 Intersection With a Regular Language
### 7.3.5 Inverse Homomorphism
## 7.4 Decision Properties of CFL's
### 7.4.1 Complexity of Converting Among CFG's and PDA's
### 7.4.2 Running Time of Conversion to Chomsky Normal Form
### 7.4.3 Testing Emptiness of CFL's
### 7.4.4 Testing Membership in a CFL
### 7.4.5 Preview of Undecidable CFL Problems

# 8 Introduction to Turing Machines
## 8.1 Problems That Computers Cannot Solve
### 8.1.1 Programs that Print ``Hello, World''
### 8.1.2 The Hypothetical ``Hello, World'' Tester
### 8.1.3 Reducing One Problem to Another
## 8.2 The Turing Machine
### 8.2.1 The Quest to Decide All Mathematical Questions
### 8.2.2 Notation for the Turing Machine
### 8.2.3 Instantaneous Descriptions for Turing Machines
### 8.2.4 Transition Diagrams for Turing Machines
### 8.2.5 The Language of a Turing Machine
### 8.2.6 Turing Machines and Halting
## 8.3 Programming Techniques for Turing Machines
### 8.3.1 Storage in the State
### 8.3.2 Multiple Tracks
### 8.3.3 Subroutines
## 8.4 Extensions to the Basic Turing Machine
### 8.4.1 Multitape Turing Machines
### 8.4.2 Equivalence of One-Tape and Multitape TM's
### 8.4.3 Running Time and the Many-Tapes-to-One Construction
### 8.4.4 Nondeterministic Turing Machines
## 8.5 Restricted Turing Machines
### 8.5.1 Turing Machines With Semi-infinite Tapes
### 8.5.2 Multistack Machines
### 8.5.3 Counter Machines
### 8.5.4 The Power of Counter Machines
## 8.6 Turing Machines and Computers
### 8.6.1 Simulating a Turing Machine by Computer
### 8.6.2 Simulating a Computer by a Turing Machine
### 8.6.3 Comparing the Running Times of Computers and Turing Machines

# 9 Undecidability
## 9.1 A Language That Is Not Recursively Enumerable
### 9.1.1 Enumerating the Binary Strings
### 9.1.2 Codes for Turing Machines
### 9.1.3 The Diagonalization Language
### 9.1.4 Proof That L_d Is Not Recursively Enumerable
## 9.2 An Undecidable Problem That Is RE
### 9.2.1 Recursive Languages
### 9.2.2 Complements of Recursive and RE languages
### 9.2.3 The Universal Language
### 9.2.4 Undecidability of the Universal Language
## 9.3 Undecidable Problems About Turing Machines
### 9.3.1 Reductions
### 9.3.2 Turing Machines That Accept the Empty Language
### 9.3.3 Rice's Theorem and Properties of the RE Languages
### 9.3.4 Problems about Turing-Machine Specifications
## 9.4 Post's Correspondence Problem
### 9.4.1 Definition of Post's Correspondence Problem
### 9.4.2 The ``Modified'' PCP
### 9.4.3 Completion of the Proof of PCP Undecidability
## 9.5 Other Undecidable Problems
### 9.5.1 Problems About Programs
### 9.5.2 Undecidability of Ambiguity for CFG's
### 9.5.3 The Complement of a List Language

# 10 Intractable Problems
## 10.1 The Classes P and NP
### 10.1.1 Problems Solvable in Polynomial Time
### 10.1.2 An Example: Kruskal's Algorithm
### 10.1.3 Nondeterministic Polynomial Time
### 10.1.4 An NP Example: The Traveling Salesman Problem
### 10.1.5 Polynomial-Time Reductions
### 10.1.6 NP-Complete Problems
## 10.2 An NP-Complete Problem
### 10.2.1 The Satisfiability Problem
### 10.2.2 Representing SAT Instances
### 10.2.3 NP-Completeness of the SAT Problem
## 10.3 A Restricted Satisfiability Problem
### 10.3.1 Normal Forms for Boolean Expressions
### 10.3.2 Converting Expressions to CNF
### 10.3.3 NP-Completeness of CSAT
### 10.3.4 NP-Completeness of 3SAT
## 10.4 Additional NP-Complete Problems
### 10.4.1 Describing NP-complete Problems
### 10.4.2 The Problem of Independent Sets
### 10.4.3 The Node-Cover Problem
### 10.4.4 The Directed Hamilton-Circuit Problem
### 10.4.5 Undirected Hamilton Circuits and the TSP
### 10.4.6 Summary of NP-Complete Problems

# 11 Additional Classes of Problems
## 11.1 Complements of Languages in NP
### 11.1.1 The Class of Languages Co-NP
### 11.1.2 NP-Complete Problems and Co-NP
## 11.2 Problems Solvable in Polynomial Space
### 11.2.1 Polynomial-Space Turing Machines
### 11.2.2 Relationship of PS and NPS to Previously Defined Classes
### 11.2.3 Deterministic and Nondeterministic Polynomial Space
## 11.3 A Problem That Is Complete for PS
### 11.3.1 PS-Completeness
### 11.3.2 Quantified Boolean Formulas
### 11.3.3 Evaluating Quantified Boolean Formulas
### 11.3.4 PS-Completeness of the QBF Problem
## 11.4 Language Classes Based on Randomization
### 11.4.1 Quicksort: an Example of a Randomized Algorithm
### 11.4.2 A Turing-Machine Model Using Randomization
### 11.4.3 The Language of a Randomized Turing Machine
### 11.4.4 The Class RP
### 11.4.5 Recognizing Languages in RP
### 11.4.6 The Class ZPP
### 11.4.7 Relationship Between RP and ZPP
### 11.4.8 Relationships to the Classes P and NP
## 11.5 The Complexity of Primality Testing
### 11.5.1 The Importance of Testing Primality
### 11.5.2 Introduction to Modular Arithmetic
### 11.5.3 The Complexity of Modular-Arithmetic Computations
### 11.5.4 Random-Polynomial Primality Testing
### 11.5.5 Nondeterministic Primality Tests
