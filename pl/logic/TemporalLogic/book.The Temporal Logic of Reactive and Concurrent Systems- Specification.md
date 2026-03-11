# The Temporal Logic of Reactive and Concurrent Systems: Specification
* Zahar Manna, Amir Pnueli. **The Temporal Logic of Reactive and Concurrent Systems: Specification**. Springer-Verlag: 1992.

- Part I. Models of Concurrency: 1-2
- Part II: Specifications: 3-4

# 1 Basic Models

**transformational program**

**reactive program**

## 1.1 The Generic Model

### 1.1.1 The Underlying Language

- $\mathcal{V}$ - Vocabulary

The vocabluary consists of a countable set of typed variables.

The **type** of each variable indicates the **domain** over which the variable ranges, e.g., a *data variable* may range over the natural numbers, and a *control variable* that refers to the progress of the program may range over a finite set of locations.

We partition the variabels into rigid and flexible variables.
A *rigid variable* must have the same value in all states of a computation,
while a *flexible variable* may assume different values in different states.
All the data and control variables in the program will be flexible.
We will use rigid variables mainly for specification purpose in order to compare the values assumed by a flexible variable in different states.

- $\mathcal{E}$ - Expressions

Expressions are constructed from the variables of $\mathcal{V}$ and
constants (such as $0$, $\Lambda$ (empty list), $\phi$ (empty set))
to which
functions (such as $+$, $\bullet$ (appending an element to a list), $\cup$) and
predicates (such as $>$, $\texttt{null}$ (a list is empty), $\subseteq$)
over the appropriate domains (such as integers, lists and sets) are applied.

Expressions whose values range over the boolean domain $\{\texttt{T}, \texttt{F}\}$ are called **boolean expressions**.

> [!example] "Expressions"

$$
\begin{array}{l}
& x + 3y \\
& hd(u) \bullet tl(v) \\
& A \cup B \\
& \neg (x > y) \wedge \bigl ( (z = 0) \vee (u \subseteq v) \bigr )
\end{array}
$$

- $\mathcal{A}$ - Assertions

Assertions are constructed out of boolean expressions using boolean connectives and quantification ($\forall$, $\exists$)

> [!example] "Assertions"

$$
\forall x: \left [ (x > 0) \rightarrow \exists y: (x = y \cdot y) \right]
$$

- $\mathcal{I}$ - Interpretations

An interpretation $\mathit{I} \in \mathcal{I}$ of a set of typed variables $\mathit{V} \subseteq \mathcal{V}$
is a mapping that assigns to each varibale $y \in \mathit{V}$ a value $\mathit{I}[y]$ in the domain of $y$.

The assignment of values to variables provided by $\mathit{I}$ is uniquely extended to an assignment of values to expressions and assertions in the following way:

For an expression $e$, denote by $\mathit{I}[e]$ the value obtained by evaluating $e$, using the value $\mathit{I}[y]$ for each variable $y$ appearing in $e$.

In the case that $\varphi$ is a boolean expression or more generally, an assertion, then $\mathit{I}[\varphi] \in \{ \texttt{F}, \texttt{T} \}$.
If $\mathit{I}[\varphi] = \texttt{T}$, we say that $\mathit{I}$ **satisfies** $\varphi$ and write $\mathit{I} \vDash \varphi$.

> [!example] "Interpretations"

If $\mathit{I}$ is given by $\mathit{I}: \left < x: 1, y: 2, z: 3 \right >$, then $\mathit{I}[y] = 2$ and $\mathit{I}[x + y \cdot z] = 7$.

In the case that $\varphi$ is an assertion that contains quantifiers, interpretation $\mathit{I}$ need only provide values for the free variables of $\varphi$ in order to determine whether $\mathit{I} \vDash \varphi$ holds.

An interpretation $\mathit{I}$ can also be applied to a list of expressions $( e_{1}, \cdots, e_{n} )$, yielding a list of values $\mathit{I}[( e_{1}, \cdots, e_{n} )] = (\mathit{I}[e_{1}], \cdots, \mathit{I}[e_{n}])$.

### 1.1.2 Basic Transition System

A basic transition system $\left < \Pi, \Sigma, \mathcal{T}, \Theta \right >$, intended to represent a reactive program, is given by the following components:

- $\Pi = \{ u_{1}, \cdots, u_{n} \} \subseteq \mathcal{V}$ - A finite set of flexible state variabels

Some of these flexible variabels represent *data varibales*, which are explicitly declared and manipulated by statements in the program.
Other variables are *control variables*, which represent progress in the execution of the program by indicating, for example, locations in the program or statements about to be executed.

- $\Sigma$ - A set of states

Each state $s$ in $\Sigma$ is an interpretation of $\Pi$, assigning to each variable $u$ in $\Pi$ a value over its domain, which we denote by $s[u]$.
A state $s$ that satisfies an assertion $\varphi$, i.e. $s \vDash \varphi$, is sometimes referred to as a $\varphi$-state.

- $\mathcal{T}$ - A finite set of transitions

Each transition $\tau$ in $\mathcal{T}$ represents *a state-transforming action of the system*
and is defined as function $\tau: \Sigma \rightarrow 2^{\Sigma}$ that maps a state $s$ in $\Sigma$ into the (possibly empty) set of states $\tau(s)$ that can be obtained by applying action $\tau$ to state $s$.
Each state $s'$ in $\tau(s)$ is defined to be a $\tau$-successor of $s$.
It is required that one of the transitions, $\tau_{\mathit{I}}$, called the *idling transition*, is an identity function, i.e., $\tau_{\mathit{I}}(s) = \{ s \}$ for every state $s$.

- $\Theta$ - An initial condition

This assertion characterizes the states at which execution of the programin can begin.
A state satisfying $\Theta$, i.e., $s \vDash \Theta$, is called an *initial state*.

### 1.1.3 The Transition Relation $\rho_{\tau}$

### 1.1.4 Enabled and Disabled Transitions

### 1.1.5 Idling and Diligent Transitions

### 1.1.6 Computations

### 1.1.7 Concrete Models

The **diagram language**

The **text language**

## 1.2 Model l: Transition Diagrams

In the transition-diagram langugae, a **program** $P$ has the following form:

$$
P :: \left [\texttt{declaration} \right] \left [ P_{1} \| \cdots \| P_{m} \right]
$$

where $P_{1}, \cdots, P_{m}, m \ge 1$, are **processes**.

The program refers to a set of data variables $Y = \left\{ y_{1}, \cdots, y_{n} \right\}, n \ge 1$, which are declared at the head of the program and are accessible to all the processes for reference and modification.

### 1.2.1 Declarations

$$
\texttt{mode} \ \texttt{variable}, \cdots, \texttt{variable}: \texttt{type} \ \textbf{where} \ \varphi_{i}
$$

$\texttt{mode}$: 

- $\textbf{in}$:
- $\textbf{local}$:
- $\textbf{out}$:

$\texttt{type}$:

- basic types: **integer**, **character**, ...
- structured types: **array**, **list**, **set**, ...


> [!example] "Transition Diagrams Program"

declaration:

$$
\begin{array}{ll}
& \textbf{in} \ k,n             &: \textbf{integer} \ \textbf{where} \ 0 \le k \le n \\
& \textbf{local} \ y_{1}, y_{2} &: \textbf{integer} \ \textbf{where} \ y_{1} = n \wedge y_{1} = 1 \\
& \textbf{out} \ b              &: \textbf{integer} \ \textbf{where} \ b = 1
\end{array}
$$

data precondition:

$$
\varphi : 0 \le k \le n 
\ \wedge \ y_{1} = n 
\ \wedge \ y_{2} = 1 
\ \wedge \ b = 1
$$

program:

$$
P :: \left [\texttt{declaration} \ \textbf{where} \ \varphi \right] \left [ P_{1} \| \cdots \| P_{m} \right] 
$$

### 1.2.2 Processes

Each process $P_{i}, i = 1, \cdots, m$, is represented by a transition diagram, which is a directed graph.

The nodes in the diagram are referred to as **locations**.
The locations of process $P_{i}$ are usually called $\ell_{0}^{i}, \ell_{1}^{i}, \cdots, \ell_{t_{i}}^{i}$.

The edges in the diagram for each process are labeled with (atomic) **instructions**, which have the form of a **guarded assignment** $c \rightarrow \left[ \bar{y} := \bar{e} \right]$,
in which $c$ is a boolean expression called the guard of the instruction, $\bar{y} = (y_{1}, \cdots, y_{k})$ is a list of data variables, and $\bar{e} = (e_{1}, \cdots, e_{k})$ a list of expressions.
The instructions labeling edges in a process are called the **instructions** of the process.

Within this set of instructions, communication between the processes is managed via **shared variables**, i.e., one process writing a value into a variable, which another process later reads.

To describe the full state of a program, we need, in addition to the data variables, control variables $\pi_{1}, \cdots, \pi_{m}$.
Each $\pi_{i}$ points to the current location of control within process $P_{i}$. This is where $P_{i}$ looks for the next instruction to be performed.
Each $\pi_{i}$ ranges over $L_{i}$, the set of locations belonging to $P_{i}$.

### 1.2.3 Diagrams as Basic Transition Systems

We now identity the four components of a basic transition system:

- State Variables $\Pi$
- States $\Sigma$
- Transitions $\mathcal{T}$
- Initial Condition $\Theta$

### 1.2.4 Representing Concurrency by Interleaving

An execution of a program that contains two parallel processes is represented by *interleaved* execution of the atomic instructions of the participating processes.

### 1.2.5 Scheduling

We refer to the choice of the enabled transition to be executed next as **scheduling**.
A sequence of choices that leads to a complete computation is called a **schedule**.

## 1.3 Model 2: Shared-Variables Text

### 1.3.1 Simple Statements

- Skip: $\textbf{skip}$
- Assignment: $\overline{y} := \overline{e}$
- Await: $\textbf{await} \ c$

### 1.3.2 Compound Statements

- Conditional: $\textbf{if} \ c \ \textbf{then} \ S_{1} \ \textbf{else} \ S_{2}$, $\textbf{if} \ c \ \textbf{then} \ S_{1}$
- Concatenation: $S_{1} ; S_{2}$, $S_{1} ; S_{2} ; \cdots ; S_{n}$, $\textbf{when} \ c \ \textbf{do} \ S$
- Selection: $S_{1} \ \textbf{or} \ S_{2}$, $\textbf{OR}_{i=1}^{n} S_{i}$
- Cooperation: $S_{1} \parallel S_{2}$, $\parallel_{i=1}^{n} S_{i}$
- While: $\textbf{while} \ c \ \textbf{do} \ S$
- Block: $[local \ declaration ; S]$

### 1.3.3 Programs

$P :: \bigl [ declaration ; [P_{1} :: S_{1} \parallel \cdots \parallel P_{m} :: S_{m}] \bigr ]$

$declaration$: 

$mode \ variable, \cdots, varibale : \ type \ \textbf{where} \ \varphi$

$mode \in \{\textbf{in}, \textbf{local}, \textbf{out}\}$

### 1.3.4 Labels in Text Programs

Fig. 1.5. A fully labeled GCD program.

Fig. 1.6 Structure tree of the GCD program.

In principle, we consider each program to be fully labeled and denote the pre-label and post-label of statement $S$ by $pre(S)$ and $post(S)$, respectively.

### 1.3.5 The Label Equivalence Relation

We define a label equivalence relation $\sim_{L}$ by the following rules: ...


### 1.3.6 Locations in the Text Language

We define a location in the text language to be an equivalence class of labels with respect to the label equivalence relation $\sim_{L}$.

## 1.4 Semantics of Shared-Variables Text

identify the components of a basic transition system in text programs.

### 1.4.1 State Variables and States
### 1.4.2 Transitions

The set of transitions associated with a statement $S$ is denoted by $trans(S)$.

### 1.4.3 The Initial Condition
### 1.4.4 Computation
### 1.4.5 Subscripted Variables

## 1.5 Structural Relations Between Statements

### 1.5.1 Substatements

For statements $S$ and $S'$, $S$ is defined to be a **substatement** of $S'$, denoted by $S \preccurlyeq S'$,
if either $S = S'$ or $S$ is a substatement of one of the children of $S'$.
We also say that $S'$ is an **ancestor** of $S$ and that $S$ is a **descendant** of $S'$.

A statement $S_{1}$ is said to be **at the front** of a statement $S_{2}$ if $S_{1} \preccurlyeq S_{2}$ and $pre(S_{1}) \sim_{L} pre(S_{2})$.

A statement $S$ is defined to be a **common ancestor** of statements $S_{1}$ and $S_{2}$ if $S_{1} \preccurlyeq S$ and $S_{2} \preccurlyeq S$.

A statement $S$ is the **least common ancestor (lca)** of $S_{1}$ and $S_{2}$ if

a. $S$ is a common ancestor of $S_{1}$ and $S_{2}$ and <br/>
b. For any other common ancestor $S'$ of $S_{1}$ and $S_{2}$, $S \preccurlyeq S'$

> [!example] "Least common ancestor"

$\bigl [ S_{1} ; [S_{2} \parallel S_{3}]; S_{4} \bigr ] \parallel S_{5}$

- the lca of $S_{2}$ and $S_{3}$ is $[S_{2} \parallel S_{3}]$
- the lca of $S_{2}$ and $S_{4}$ is $\bigl [ S_{1} ; [S_{2} \parallel S_{3}]; S_{4} \bigr ]$
- the lca of $S_{2}$ and $S_{5}$ is $\bigl [ S_{1} ; [S_{2} \parallel S_{3}]; S_{4} \bigr ] \parallel S_{5}$

### 1.5.2 The State Predicates at, after and in

control predicates:

- $at\_\ell$
- $at\_S$
- $after\_S$, $after\_\ell$
- $in\_S$, $in\_\ell$

### 1.5.3 Enabledness of a Statement

For each transition $\tau \in trans(S)$ associated with the statement $S$, let $C_{\tau}$ be the enabling condition of $\tau$.
That is, we assume that the transition relation of $\tau$ has the presentation $\rho_{\tau}: C_{\tau} \wedge (\overline{y}' = \overline{e})$.
Then, enabledness of the statement $S$ can be expressed by $enabled(S): \bigvee_{\tau \in trans(S)} C_{\tau}$.

### 1.5.4 Processes and Parallel Statements

nested parallelism, example: $P :: \Bigl [ declaration ; \bigl [  [S_{1} ; [S_{2} \parallel S_{3}]; S_{4} \parallel S_{5} \bigr ] \Bigr ]$

Two statements $S'$ and $S''$ in a program $P$ are defined to be (syntactically) **parallel** in $P$
if the least common ancestor of $S'$ and $S''$ is a cooperation statement that is difference from both $S'$ and $S''$.

### 1.5.5 Competing Statements

## 1.6 Behavioral Equivalence

### 1.6.1 First Approximation
### 1.6.2 Observable and Reduced Behaviors
### 1.6.3 Equivalence of Transition Systems
### 1.6.4 Congruence of Statements
### 1.6.5 Examples
### 1.6.6 Implementation Versus Emulation

## 1.7 Grouped Statements

### 1.7.1 The Grouped Statement
### 1.7.2 The Transition Associated with a Grouped Statement


## 1.8 Semaphore Statements

### 1.8.1 The Need for Semaphores
### 1.8.2 Semaphore Statements
### 1.8.3 Use of Semaphores for Mutual Exclusion
### 1.8.4 Other Uses of Semaphores

## 1.9 Region Statements

### 1.9.1 Comparing Semaphores to Region Statements
### 1.9.2 Synchronization Within Selection Statements

## 1.10 Model 3: Message-Passing Text

### 1.10.1 Communication Statements
### 1.10.2 Buffering Capability
### 1.10.3 Examples
### 1.10.4 Conditional Communication Statements
### 1.10.5 Comparison of the Synchronous and Asynchronous Models
### 1.10.6 A Fair Server

## 1.11 Model 4: Petri Nets

### 1.11.1 Nets
### 1.11.2 Marking
### 1.11.3 Graphical Representation
### 1.11.4 Firing
### 1.11.5 Petri Systems
### 1.11.6 Examples

## 1.12 Problems

## 1.13 Bibliographic Notes

# 2 Modeling Real Concurrency
> [!note] "Interference"
> 
> Concurrency is represented by **interleaving** in the generic model in this book.
> Two parallel processes never execute their statements at precisely the same instant, but tak turns in executing atomic transitions.
> Formally, when one of them executes an atomic execution, the other is inactive.
> This model of computation is very convenient for the formalization, analysis, and manipulation of concurrent programs.
> 
> In actual concurrent systems, which are usually composed of several independent processors, each them executing a program of its own, the execution of statements in different processors usually overlaps rather than interleaves.
> We refer to this behavior as **overlapped execution**.

> [!note] "Independent Progress"
> 
> The problem of **independent progress** is that, in an overlapped execution, the computation of each process keeps advancing, since each processor is independently responsible for its own progress.

## 2.1 Interleaving and Concurrency
### 2.1.1 Overlapped Execution

Fig. 2.1 Program A1.

$$
\textbf{out} \ y: \ \textbf{integer} \ \textbf{where} \ y = 1 \\
P_{1} :: [\ell_{0}: y := y + 1 :\widehat{\ell_{0}}] \parallel P_{2} :: [m_{0}: y := y - 1 :\widehat{m_{0}}]
$$


### 2.1.2 Interleaved Computation
### 2.1.3 Finer Granularity

## 2.2 Limiting the Critical References
### 2.2.1 Critical References
### 2.2.2 The LCR Restriction for Statements
### 2.2.3 LCR Programs
### 2.2.4 Extra Protection is Needed
### 2.2.5 Every Program Has an LCR Refinement
### 2.2.6 Every Program Has an LCR Equivalent
### 2.2.7 Semantically Critical References
### 2.2.8 Merging Statements
### 2.2.9 With Statement

## 2.3 Justice (Weak Fairness)
### 2.3.1 The Need for Fairness
### 2.3.2 Unfair Computations
### 2.3.3 Justice
### 2.3.4 Justice Requirements

## 2.4 Implications of the Justice Requirements
### 2.4.1 Fairness in Selection is Not Guaranteed
### 2.4.2 Transition Versus Process Justice
### 2.4.3 Scheduling for Justice
### 2.4.4 Justice Cannot Be Measured
### 2.4.5 Unjust Transitions

## 2.5 Compassion (Strong Fairness)
### 2.5.1 Justice is Not Enough
### 2.5.2 Compassion Requirement
### 2.5.3 Scheduling for Compassion

## 2.6 Synchronization Statements

## 2.7 Communication Statements
### 2.7.1 Mutual Exclusion by Synchronous Communication
### 2.7.2 Mutual Exclusion by Asynchronous Communication

## 2.8 Summary: Fair Transition Systems

## 2.9 Fairness in Petri Nets
### 2.9.1 Justice
### 2.9.2 Compassion for Nonunary Net-Transitions
### 2.9.3 Mutual Exclusion

## 2.10 Semantic Considerations of Fairness
### 2.10.1 Fairness Prevents Finite Distinguishability
### 2.10.2 Fairness and Random Choice

## 2.11 Problems
## 2.12 Bibliographic Notes



# 3 Temporal Logic
## 3.1 State Formulas
## 3.2 Temporal Formulas: Future Operators
## 3.3 Temporal Formulas: Past Operators
## 3.4 Basic Properties of the Temporal Operators
## 3.5 A Proof System
## 3.6 Axioms for a Proof System
## 3.7 Basic Inference Rules
## 3.8 Derived Inference Rules
## 3.9 Equality and Quantifiers
## 3.10 From General Validity to Program Validity Problems
## 3.11 Bibliographic Notes


# 4 Properties of Programs
## 4.1 The Local Language
## 4.2 The Classification of Properties
## 4.3 Examples of Safety: State Invariances
## 4.4 Examples of Safety: Past Invariances
## 4.5 Examples of Progress Properties: From Guarantee to Reactivity
## 4.6 Example: A Resource Allocator
## 4.7 Expressivity of the Specification Language
## 4.8 Specification of Reactive Modules
## 4.9 Composing Modular Specifications Problems
## 4.10 Bibliographic Notes


# References

- Abadi, M. and Z. Manna [1989]. Temporal logic programming. J. Symb. Comp., 8(3):277-295.
- Abadi, M. and Z. Manna [1990]. Nonclausal deduction in first-order temporal logic. J. ACM, 37(2):279-317.
- Allen, J.F. [1984]. Towards a general theory of action and time. Artificial Intelligence, 23(2):123-154.
- Alpern, B. and F.B. Schneider [1985]. Defining liveness. Inf. Proc. Letters, 21(4):181-185.
- Alpern, B. and F.B. Schneider [1987]. Recognizing safety and liveness. Distributed Computing, 2:117-126.
- Alur, R., T. Feder, and T.A. Henzinger [1991]. The benefits of relaxing punctuality. In Proc. of the 10th Annual ACM Symp. on Princ. of Dist. Compo
- Alur, R. and T.A. Henzinger [1989]. A really temporal logic. Proc. 30th IEEE Symp. on Found. of Compo Sci., 164-169, 1989.
- Alur, R. and T.A. Henzinger [1990]. Real-time logics: Complexity and expressiveness. Proc. 5th IEEE Symp. on Logic in Compo Sci., 492-40l.
- Andrews, G.R. and F.B. Schneider [1983]. Concepts and notations for concurrent programming. ACM Compo Surveys, 15(1):3-43.
- Apt, K.R., N. Francez, and S. Katz [1988]. Appraising fairness in languages for distributed programming. Distributed Computing, 2:226-24l.
- Apt, K.R., N. Francez, and W.-P. de Roever [1980]. A proof system for communicating sequential processes. ACM Trans. on Prog. Lang. and Sys., 2:359-385.
- Apt, K.R. and E.R. Olderog [1983]. Proof rules and transformation dealing with fairness. Sci. Compo Prog., 3:65-100.
- Apt, K.R. and G.D. Plotkin [1986]. Countable nondeterminism and random assignment. J. ACM, 33(4):724-767.
- Arnold, A. [1983]. Topological characterizations of infinite behaviors of transition systems. Proc. 10th Int. Colloq. Lang. Prog. Lec. Notes in Compo Sci. 154, Springer-Verlag, Berlin, 28-38.
- Arnold, A. [1985]. A syntactic congruence for rational w-languages. Theor. Compo Sci. 39:333-335.
- Bacon, J. [1980]. Substance and first-order quantification over individualconcepts. J. Symb. Logic, 45:193-203.
- Bandinet, M. [1989]. Temporal logic programming is complete and expressive. Proc. 16th ACM Symp. on Princ. of Prog. Lang., 267-28l.
- Banieqbal, B. and H. Barringer [1986]. A study of an extended temporal logic and a temporal fixed point calculus. Tech. Report UMCS-86-10-2, Univ. of Manchester.
- Barringer, H., R. Kuiper, and A. Pnueli [1984]. Now you may compose temporal logic specifications. Proc. 16th ACM Symp. on Theory of Comp., 51-63.
- Barringer, H., R. Kuiper, and A. Pnueli [1985]. A compositional temporal approach to a eSP-like language. In Formal Models of Progmmming, E.J. Neuhold and G. Chroust (editors), IFIP, North-Holland, 207-227.
- Barringer, H., R. Kuiper, and A. Pnueli [1986]. A really abstract concurrent model and its temporal logic. Proc. 13th ACM Symp. on Princ. of Prog. Lang., 173-183.
- Baudinet, M. [1989]. Logic Progmmming Semantics: Techniques and Applications. Ph.D. Thesis, Computer Science Dept., Stanford Univ., Stanford, CA.
- Ben-Ari, M. [1990]. Principles of Concurrent Progmmming, Prentice-Hall, London. 
- Ben-Ari, M., Z. Manna, and A. Pnueli [1981]. The temporal logic of branching time. Proc. 8th ACM Symp. on Princ. of Prog. Lang., Williamsburg, VA, 164-176. Also Acta Informatica, 20(3):207-26, 1983.
- Bernstein, A.J. [1966]. Analysis of programs for parallel processing. IEEE Trans. on Electronic Computers, EC-15(5):757-763.
- Best, E. [1984]. Fairness and conspiracies. Inj. Proc. Letters, 18:215-220.
- Best, E. and C. Lengauer [1989]. Semantic independence. Sci. Compo Prog., 13(1):23-50.
- Biichi, J.R. [1960]. Weak second order arithmetic and finite automata. Zeitschrijt fur Math. Log. und Grundl. der Math., 6:66-92.
- Burgess, J.P. [1982]. Axioms for tense logic II: time periods. Notre Dame J. of Formal Logic, 23(4):375-383.
- Burgess, J.P. and Y. Gurevich [1985]. The decision problem for linear temporal logic. Notre Dame J. of Formal Logic, 26(2):115-128.
- Campbell, R.H. and A.N. Habermann [1974]. The specification of process synchronization by path expressions. In Proc. Int. Symp. on Operating Systems, Rocquencourt. Lee. Notes in Compo Sci. 16, Springer-Verlag, Berlin, 89-102.
- Chandy, K.M. and J. Misra [1988]. Parallel Program Design. Addison-Wesley.
- Chellas, B.F. [1980]. Modal Logic: An Introduction, Cambridge Univ. Press.
- Clarke, E.M. and E.A. Emerson [1981]. Design and synthesis of synchronization skeletons using branching time temporal logic. In Proc. IBM Workshop on Logics of Programs. Lee. Notes in Compo Sci. 131, Springer-Verlag, Berlin, 52-71.
- Clarke, E.M., E.A. Emerson, and A.P. Sistla [1986]. Automatic verification of finite state concurrent systems using temporal logic specifications. A CM Trans. on Prog. Lang. and Sys., 8(2):244-263.
- Costa, G. and C. Stirling [1984]. A fair calculus of communicationg systems. Acta Informatica, 21:417-441.
- Courtois, P.J., F. Heymans, and D.L. Parnas [1971]. Concurrent control with "readers" and "writers." Comm. ACM, 14{1O):667-668.
- Darondeau, P. [1985]. About fair asynchrony. Theor. Compo Sci., 37:305-336.
- de Bruijn, N.G. [1967]. Additional comments on a problem in concurrent programming control. Comm. ACM, 8(9):137-138.
- Dijkstra, E.W. [1965]. Solution of a problem in concurrent programming control. Comm. ACM 8(9):569.
- Dijkstra, E.W. [1968]. Cooperating sequential processes. In Programming Languages, F. Genuys (editor), Academic Press, New York, 43-112.
- Dijkstra, E.W. [1971]. Hierarchical ordering of sequential processes. Acta Informatica, 1:115-138.
- Dijkstra, E.W. [1975]. Guarded commands, nondeterminancy, and formal derivation of programs. Comm. ACM 18(8):453-457.
- Dijkstra, E.W. [1976]. A Discipline of Programming. Prentice-Hall, Engelwood Clifs, NJ.
- Emerson, E.A. [1989]. Temporal and modal logic. In Handbook of Theoretical Computer Science, J. van Leeuwen (editor), North-Holland, Amsterdam, 995-1072.
- Emerson, E.A. and E.M. Clarke [1981]. Characterizing correctness properties of parallel programs as fixpoints. In Proc. 7th Int. Colloq. Aut. Lang. Prog. Lee. Notes in Compo Sci. 85, Springer-Verlag, Berlin, 169-181.
- Emerson, E.A. and E.M. Clarke [1982]. Using branching time temporal logic to synthesize synchronization skeletons. Sci. Compo Prog., 2:241-266.
- Emerson, E.A. and J.Y. Halpern [1985]. Decision procedures and expressiveness in the temporal logic of branching time. J. Compo Sys. Sci., 30(1):1-24.
- Emerson, E.A. and J.Y. Halpern [1986]. 'Sometimes' and 'not never' revisited: On branching time versus linear time. J. ACM, 33:151-178.
- Emerson, E.A. and C.B. Jutla [1988]. The complexity of tree automata and logic of programs. Proc. 29th IEEE Symp. on Found. of Compo Sci., 328-337. 
- Emerson, E.A., A.K. Mok, A.P. Sistla, and J. Strinivasan [1991]. Quantitative temporal reasoning. Computer-Aided Verification 90, Series in Discrete Mathematics and Theoretical Computer Science, Vol. 3, ACM/ AMS, Providence, 136-145.
- Emerson, E.A. and A.P. Sistla [1984]. Deciding full branching time logic. Info. and Cont., 61:175-201.
- Francez, N. [1986]. Fairness. Springer-Verlag, New York.
- Francez, N. and A. Pnueli [1978]. A proof method for cyclic programs. Acta Informatica, 9:133-157.
- Fujita, M., S. Kono, H. Tanaka, and T. Moto-oka [1986]. Tokio: logic programming language based on temporal logic. In Proc. 3rd Int. Congo Logic Prog., E. Shapiro (editor). Lec. Notes Compo Sci. 225, Springer-Verlag, 695-709.
- Gabbay, D. [1976]. Investigations in Modal and Tense Logics with Applications to Problems in Philosophy and Linguistics. Reidel, Dordrecht, Holland.
- Gabbay, D., A. Pnueli, S. Shelah, and J. Stavi [1980a]. On the temporal analysis of fairness. Proc. 7th ACM Symp. on Princ. of Prog. Lang., 163-173.
- Gabbay, D., A. Pnueli, S. Shelah, and Y. Stavi [1980b]. Completeness results for the future fragment of temporal logic. Manuscript.
- Galton, A. [1987]. Temporal logic and computer science: an overview. In Temporal Logics and Their Applications, A. Galton (editor). Academic Press, London, 1-52.
- Garson, J.W. [1984]. Quantification in modal logic. In Handbook of Philosophical Logic, Vol. II, D. Gabbay and F. Guenthner (editors), Reidel, 249-307.
- Goldblatt, R. [1987]. Logics of time and computation. CSLI Lecture Notes 7, CSLI, Stanford Univ., Stanford.
- Gries, D. [1981]. The Science of Programming. Springer-Verlag, New-York.
- Hailpern, B.T. [1982]. Verifying Concurrent Processes Using Temporal Logic. Lec. Notes in Compo Sci. 129., Springer-Verlag, Berlin.
- Hailpern, B.T. and S.S. Owicki [1983]. Modular verification of computer communication protocols. IEEE Trans. on Comm., COM-31, 1:56-68.
- Halpern, J., Z. Manna, and B. Moszkowski [1983]. A hardware semantics based on temporal intervals. Proc. 10th Int. Colloq. Aut. Lang. and Prog. Lec. Notes in Compo Sci. 154, Springer-Verlag, Berlin, 278-29l.
- Harel, D. [1986]. Effective transformations on infinite trees, with applications to high undecidability, dominoes, and fairness. J. ACM, 33(1):224-248.
- Harel, D. [1987]. Statecharts: A visual formalism for complex systems. Sci. Compo Prog., 8:231-274.
- Harel, E., O. Lichtenstein and A. Pnueli [1990]. Explicit clock temporal logic. Proc. 5th IEEE Symp. on Logic in Compo Sci., 402-413.
- Henzinger, T., Z. Manna, and A. Pnueli [1991]. Temporal proof methodologies for real-time systems. Proc. 18th ACM Symp. on Princ. of Prog. Lang., 353-366.
- Hoare, C.A.R. [1969]. An axiomatic basis for computer programming. Comm. ACM, 12(10):576-580.
- Hoare, C.A.R. [1974]. Monitors: An operating system structuring concept. Comm. ACM, 17(10):549-557.
- Hoare, C.A.R. [1978]. Communicating sequential processes. Comm. ACM, 21(8):666-677.
- Hoare, C.A.R. [1984]. Communicating Sequential Processes, Prentice-Hall, London.
- Hoogeboom, H.J. and G. Rozenberg [1986]. Infinitary languages: Basic theory and applications to concurrent systems. In Current Trends in Concurrency, J.W. de Bakker, W.-P. de Roever and G. Rozenberg (editors). Lec. Notes in Compo Sci. 224, Springer-Verlag, Berlin, 266-342.
- Hooman, J. and W.-P. de Roever [1986]. The quest goes on: A survey of proofsystems for partial correctness of csp. In Current Trends in Concurrency, J.W. de Bakker, W.-P. de Roever and G. Rozenberg (editors). Lec. Notes in Compo Sci. 224, Springer-Verlag, Berlin, 343-395.
- Hughes, G.E. and M.J. Cresswell [1968]. An Introduction to Modal Logic. Methuen, New York.
- Jonsson, B. [1987]. Modular verification of asynchronous networks. Proc. 6th ACM Symp. on Prine. of Dist. Comp., 152-166.
- Kahn, G. [1974]. The semantics of a simple language for parallel programming. In Proc. IFIP Congress 74, North-Holland, Amsterdam, 471-475.
- Kaminski, M. [1985]. A classification of w-regular languages. Theor. Compo Sci., 36:217-220.
- Kamp, J.A.W. [1968]. Tense Logic and the Theory of Linear Order. Ph.D. Thesis, Michigan State Univ.
- Katz, S. and D. Peled [1987]. Interleaving set temporal logic. Proe. 6th ACM Symp. on Prine. of Dist. Comp., 178-190.
- Keller, RM. [1976]. Formal verification of parallel programs. Comm. ACM, 19(7) :371-384.
- Knuth, D.E. [1966]. Additional commments on a problem in concurrent program control. Comm. ACM, 9(5):32l.
- Koymans, R [1987]. Specifying mesage buffers requires extending temporal logic. Proe. 6th ACM Symp. on Prine. of Dist. Comp., 191-204.
- Koymans, R and W.-P. de Roever [1983]. Examples of a real-time temporal logic specification. In The Analysis of Concurrent Systems, M.l. Jackson and M.J. Wray (editors). Lec. Notes in Compo Sci. 207, Springer-Verlag, Berlin, 231-252.
- Koymans, R, J. Vytopyl, and W.-P. de Roever [1983]. Real-time programming and asynchronous message passing. Proc. 2nd ACM Symp. on Princ. of Dist. Comp., 187-197.
- Kozen, D. [1983]. Results on the propositional j.£-calculus. Theor. Compo Sci., 27:333-354.
- Kripke, S.A. [1963]. Semantical analysis of modal logic I: normal propositional calculi. Z. Math. Logik Grund. Math. 9:67-96.
- Kroger, F. [1977]. LAR: A logic of algorithmic reasoning. Acta Informatica, 8:243-246.
- Kwiatkowska, M.Z. [1989]. Event fairness and noninterleaving concurrency. Formal Aspects of Computing 1(3):213-228.
- Ladner, RE. [1977]. Applications of model-theoretic games to discrete linear orders and finite automata. Inform. and Cont. 33:281-303.
- Lamport, L. [1974]. A new solution of Dijkstra's concurrent programming problem. Comm. ACM, 17(8):453-455.
- Lamport, L. [1976]. The synchronization of independent processes. Acta Informatica, 7(1):15-34.
- Lamport, L. [1977]. Proving the correctness of multiprocess programs. IEEE Trans. on Software Eng., SE-3(2):125-143.
- Lamport, L. [1980a]. Sometimes is sometimes "not never" - on the temporal logic of programs. Proc. 7th ACM Symp. on Princ. of Prog. Lang., 174-185.
- Lamport, L. [1980b]. The 'Hoare logic' of concurrent programs. Acta Informatica, 14(1):21-37.
- Lamport, L. [1983a]. Specifying concurrent program modules. ACM Trans. on Prog. Lang. and Sys., 5(2):190-222.
- Lamport, L. [1983b]. What good is temporal logic. In Proc. IFIP 9th World Congress, R.E.A. Mason (editor), North-Holland, 657-668.
- Lamport, L. [1985a]. Basic concepts. In Distributed Systems - Methods and Tools for Specification. Lec. Notes in Compo Sci. 190, Springer-Verlag, Berlin, 19-30.
- Lamport, L. [1985b]. What it means for a concurrent program to satisfy a specification: Why no one has specified priority. Proc. 12th ACM Symp. on Prine. of Prog. Lang., New Orleans, 79-83.
- Lamport, L. and F.B. Schneider [1984]. The "Hoare logic" of esp, and all that. ACM Trans. on Prog. Lang. and Sys., 6(2):281-296.
- Landweber, L.H. [1969]. Decision problems for w-automata. Math. Sys. Theory, 4:376-384.
- Lauer, P.E., M.W. Shields, and E. Best [1979]. Formal theory of the basic COSY notation. Computing Lab., Univ. of Newcastle upon Tyne, Tech. Report TR143.
- Lehmann, D., A. Pnueli, and J. Stavi [1981]. Impartiality, justice and fairness: The ethics of concurrent termination. In Proc. 8th Int. Colloq. Aut. Lang. and Prog. Lec. Notes in Compo Sci. 115, Springer-Verlag, Berlin, 264-277.
- Lehmann, D. and S. Shelah [1982]. Reasoning about time and chance. Info. and Cont., 53(3):165-198.
- Levin, G.M. and D. Gries [1981]. A proof technique for communicating sequential processes. Acta Informatica, 15:281-302.
- Lichtenstein, O. [1990]. Decidability, Completeness, and Extensions of Linear Time Temporal Logic. Ph.D. Thesis, Weizmann Institute.
- Lichtenstein, 0., A. Pnueli, and L. Zuck [1985]. The glory of the past. Proc. Conf. on Logics of Programs. Lec. Notes in Compo Sci. 193, Springer-Verlag, Berlin, 196-218.
- Lynch, N.A. and M.R. Tuttle [1987]. Hierarchical correctness proofs for distributed algorithms. Proc. 6th Symp. on Prine. of Dist. Comp., 137-151.
- Manna, Z. [1969a]. Properties of programs and the first-order predicate calculus. J. ACM, 16(2):244-255.
- Manna, Z. [1969b]. The correctness of programs. J. Compo Sys. Sci., 3(2):119-127.
- Manna, Z. [1982]. Verification of sequential programs: Temporal axiomatization. In Theoretical Foundations of Programming Methodology, M. Broy and G. Schmidt (editors), NATO Advanced Study Institutes Series, D. Reidel, Dordrecht, Holland, 53-102.
- Manna, Z. and A. Pnueli [1979]. The modal logic of programs. Proc. 6th Int. Colloq. Aut. Lang. Prog. Lec. Notes in Compo Sci. 71, Springer-Verlag, Berlin, 385-409.
- Manna, Z. and A. Pnueli [1981]. Verification of concurrent programs: The temporal framework. In The Correctness Problem in Computer Science, R.S. Boyer and J.S. Moore (editors), Academic Press, London, 215-273.
- Manna, Z. and A. Pnueli [1983a]. How to cook a temporal proof system for your pet language. Proc. 10th ACM Symp. on Princ. of Prog. Lang., 141-154.
- Manna, Z. and A. Pnueli [1983b]. Proving precedence properties: The temporal way. Proc. 10th Int. Colloq. Aut. Lang. Prog. Lec. Notes in Compo Sci. 154, Springer-Verlag, Berlin, 491-512.
- Manna, Z. and A. Pnueli [1983c]. Verification of concurrent programs: A temporal proof system. In Foundations of Computer Science IV, Distributed Systems: Part 2, J.W. de Bakker and J. van Leeuwen (editors), Mathematical Centre Tracts 159, Center for Mathematics and Computer Science, Amsterdam, 163-255.
- Manna, Z. and A. Pnueli [1989a]. The anchored version of the temporal framework. In Linear Time, Branching Time and Partial Order in Logics and Models for Concurrency, J.W. de Bakker, W.-P. de Roever, and G. Rozenberg (editors). Lec. Notes in Compo Sci. 354, Springer-Verlag, Berlin, 201-284.
- Manna, Z. and A. Pnueli [1989b]. Completing the temporal picture. Proc. 16th Int. Colloq. Aut. Lang. Prog., G. Ausiello, M. Dezani-Ciancaglini, and S. Ronchi Della Rocca (editors). Lec. Notes in Compo Sci. 372, Springer-Verlag, Berlin, 534-558. Also in Theor. Compo Sci., 1991,83(1):97-130.
- Manna, Z. and A. Pnueli [1990]. A hierarchy of temporal properties. Proc. 9th ACM Symp. on Princ. of Dist. Comp., 377-408.
- McDermott, D.V. [1982]. A temporal logic for reasoning about processes and plans. Cognitive Science, 6:101-155.
- McNaughton, R. and S. Papert [1971]. Counter Free Automata. MIT Press, Cambridge, MA.
- McTaggart, J.M.E. [1927]. The Nature of Existence, Vol. I, Cambridge.
- Milner, R. [1980]. A Calculus of Communicating Systems. Lec. Notes in Compo Sci. 92, Springer-Verlag, Berlin.
- Milner, R. [1989]. Communication and Concurrency. Prentice-Hall, London.
- Misra, J. and K.M. Chandy [1981]. Proofs of networks of processes. IEEE Trans. on Software Eng., SE-7(4):417-426.
- Misra, J. and K.M. Chandy [1982]. A distributed graph algorithm: Knoth detection. ACM Trans. on Prog. Lang. and Sys., 4(4):678-686.
- Misra, J., K.M. Chandy and T. Smith [1982]. Proving safety and liveness of communicating processes with examples. Proc. ACM Symp. on Prine. of Dist. Comp., Ottawa, Canada, 157-164.
- Moszkowski, B.C. [1983]. Reasoning about Digital Circuits. Ph.D. Thesis, Stanford Univ. Tech. Report STAN-CS-83-970.
- Moszkowski, B.C. [1986]. Executing Temporal Logic Programs. Cambridge Univ. Press.
- Nguyen, V., A. Demers, S. Owicki, and D. Gries [1986]. A modal and temporal proof system for networks of processes. Distributed Computing, 1(1):7-25.
- Nguyen, B., D. Gries, and S. Owicki [1985]. A model and temporal proof system for network of processes. Proc. 12th ACM Symp. on Princ. of Prog. Lang., 121-13l.
- Ostroff, J.S. [1989]. Temporal Logic for Real-Time Systems. Advanced Software Development Series. Research Studies Press, John Wiley & Sons, Taunton, England.
- Owicki, S. and D. Gries [1976a]. An axiomatic proof technique for parallel programs, Acta Informatica, 6(4):319-340.
- Owicki, S. and D. Gries [1976b]. Verifying properties of parallel programs: An axiomatic approach. Comm. ACM, 19(5):279-284.
- Owicki, S. and L. Lamport [1982]. Proving liveness properties of concurrent programs. ACM Trans. on Prog. Lang. and Sys., 4(3):455-495.
- Park, D. [1980]. On the semantics of fair parallelism. In Abstract Software Specification. Lec. Notes in Compo Sci. 86, Springer-Verlag, Berlin, 504-524.
- Park, D. [1981]. A predicate transformer for weak fair interation. Proc. 6th IBM Symp. on Mathematical Foundations of Computer Science, Hakone, Japan.
- Park, D. [1983]. The fairness problem and nondeterministic computing networks. In Foundations of Computer Science IV, Distributed Systems, J.W. de Bakker and J. van Leeuwen (editors), Mathematical Centre Tracts 159, Center for Mathematics and Computer Science, Amsterdam, 133-16l.
- Perrin, D. [1984]. Recent results on automata and infinite words. Mathematical Foundations of Compo Sci. Lec. Notes in Compo Sci. 176, Springer-Verlag, Berlin, 134-148.
- Perrin, D. [1985]. VariE~tes de semigroupes et mots infinis. C.R. Acad. Sci. Paris, 295:595-598.
- Perrin, D. and J.E. Pin [1986]. First order logic and star-free sets. J. Compo Syst. Sci. 32:393-406.
- Peterson, G.L. [1983]. A new solution to Lamport's concurrent programming problem. ACM Trans. on Prog. Lang. and Sys., 5(1):56-65.
- Peterson, J.L. [1981]. Petri Net Theory and Modeling of Systems. Prentice-Hall, Englewood Cliffs, NJ.
- Petri, C.A. [1962]. Kommunikation mit Automaten. Bonn: Institut fur Instrumentelle Mathematik, Schriften des Um No.2. Also in English translation: Communication with Automata. Tech. Report RADC-TR-65-377, Vol. 1, Suppll, Applied Data Research, Princeton, NJ, 1966.
- Pinter, S. and P.L. Wolper [1984]. A temporal logic for reasoning about partially ordered computations. Proc. 3rd ACM Symp. on Princ. of Dist. Comp., 28-37.
- Pnueli, A. [1977]. The temporal logic of programs. Proc. 18th IEEE Symp. on Found. of Compo Sci., 46-57.
- Pnueli, A. [1981]. The temporal semantics of concurrent programs. Theor. Compo Sci., 13:1-20.
- Pnueli, A. [1983]. On the extremely fair treatment of probabilistic algorithms. Proc. 15th ACM Symp. on Theory of Comp., 278-290.
- Pnueli, A. [1986]. Applications of temporal logic to the specification and verification of reactive systems: A survey of current trends. In Current Trends in Concurrency, J.W. de Bakker, W.-P. de Roever, and G. Rozenberg (editors). Lec. Notes in Compo Sci. 224, Springer-Verlag, Berlin, 510-584.
- Pnueli, A. and R. Rosner [1988]. A framework for the synthesis of reactive modules. Proc. Int. Conf. on Concurrency: Concurrency 88, F.H. Vogt (editor). Lec. Notes in Compo Sci. 335, Springer-Verlag, Berlin, 4-17.
- Pnueli, A. and L. Zuck [1986]. Verification of multiprocess probabilistic protocols. Distributed Computing, 1:53-72.
- Pratt, V.R. [1981]. A decidable JL-calculus. Proc. 20th IEEE Symp. on Found. of Compo Sci., 421-427.
- Priese, L., R. Rehrmann, and U. Willecke-Klemme [1987]. An introduction to the regular theory of fairness. Theor. Compo Sci., 53:217-237.
- Prior, A. [1967]. Past, Present, and Future. Clarendon Press, Oxford. 
- Queille, J.P. and J. Sifakis [1983]. Fairness and related properties in transition systems - A temporal logic to deal with fairness. Acta Informatica, 19:195-220.
- Reisig, W. [1985]. Petri Nets: An Introduction. EATCS Monographs on Theoretical Computer Science, Vol. 4, Springer-Verlag, Berlin.
- Reisig, W. [1989]. Towards a temporal logic for causality and choice in distributed systems. In Linear Time, Branching Time and Partial Order in Logics and Models for Concurrency, J.W. de Bakker, W.-P. de Roever and G. Rozenberg (editors). Lec. Notes in Compo Sci. 354, Springer-Verlag, Berlin, 1989.
- Rescher, N. and A. Urquhart [1971]. Temporal Logic. Springer-Verlag, New York.
- Reynolds, J.C. [1978]. Syntactic control of interference. Proc. 5th ACM Symp. on Princ. of Prog. Lang., 39-46.
- Reynolds, J.C. [1989]. Syntactic control of interference: Part 2. Proc. 16th Int. Colloq. Aut. Lang. and Prog. Lec. Notes in Compo Sci. 372, Springer-Verlag, Berlin, 704-722.
- de Roever, W.-P. [1985]. The quest for compositionality - A survey of assertionbased proof systems for concurrent program, Part I: Concurrency based on shared variables. In The Role of Abstract Models in Computer Science, E.J. Neuhold (editor), North-Holland, 181-206.
- Rosner, R. and A. Pnueli [1986]. A choppy logic. Proc. 1st IEEE Symp. on Logic in Compo Sci., 306-313.
- Schwartz, R.L. and P.M. Melliar-Smith [1982]. From state machines to temporal logic: Specification methods for protocol standards. IEEE 'I'rans. on Comm., 30(12) :2486-2496.
- Schwartz, R.L., P.M. Melliar-Smith, and F.H. Vogt [1983]. An interval-based temporal logic. Proc. Workshop on Logics of Programs, E.M. Clarke and D.C. Kozen (editors). Lec. Notes Compo Sci. 164, Springer-Verlag, Berlin, 501-512.
- Shapiro, E. [1989]. The family of concurrent logic programming languages. ACM Compo Surveys, 21(3):412-510.
- Shoham, Y. [1988]. Reasoning About Change. MIT Press, Cambridge, MA.
- Sistla, A.P. [1983]. Theoretical Issues in the Design of Distributed and Concurrent Systems. Ph.D. Thesis, Harvard Univ., Cambridge, MA.
- Sistla, A.P. [1985]. On characterization of safety and liveness properties in temporallogic. Proc. 4th ACM Symp. on Princ. of Dist. Comp., 39-48.
- Sistla, A.P. and E.M. Clarke [1985]. The complexity of propositional linear temporallogic. J. ACM, 32:733-749.
- Sistla, A.P., E.M. Clarke, N. Francez and Y. Gurevish [1982]. Can message buffers be characterized in linear temporal logic? Proc. ACM Symp. on Princ. of Dist. Comp., 148-156.
- Sistla, A.P., E.M. Clarke, N. Francez, and A.R. Meyer [1984]. Can message buffers be axiomatized in temporal logic? Info. and Cont., 63(1,2):88-112.
- Sistla, A.P., M.Y. Vardi, and P. Wolper [1987]. The complementation problem for Biichi automata with application to temporal logic. Theor. Compo Sci., 49:217-237.
- Sounderarajan, N. [1984]. Axiomatic semantics of communicating sequential processes. ACM 'I'rans. on Prog. Lang. and Sys., 6:647-662.
- Staiger, L. [1987]. Research in the theory of w-languages. J. Inform. Process. Cybernet. 23:415-439.
- Tarski, A. [1955]. A lattice-theoretical fixpoint theorem and its applications. Pacific J. Math., 55:285-309.
- Thomas, W. [1979]. Star-free regular sets of w-sequences. Info. and Cont., 42:148-156.
- Thomas, W. [1981]. A combinatorial approach to the theory of w-automata. Info. and Cont., 48:261-283.
- Thomas, W. [1990]. Automata on infinite objects. In Handbook of Theoretical Computer Science, J. van Leeuwen (editor), North-Holland, Amsderdam, 134-19l.
- van Benthem, J.F.A.K. [1983]. The Logic of Time. Reidel, Dardrecht.
- Vardi, M.Y. [1985]. Automatic verification of probabilistic concurrent finite-state programs. Proc. 26th IEEE Symp. on Found. of Compo Sci., 327-338.
- Vardi, M.Y. [1988]. A temporal fixpoint calculus. Proc. 15th ACM Symp. on Princ. of Prog. Lang., 250-259.
- Vardi, M.Y. and P. Wolper [1983]. Yet another process logic. Proc. Workshop on Logics of Programs, E.M. Clarke and D.C. Kozen (editors). Lec. Notes Compo Sci. 164, Springer-Verlag, Berlin, 501-512.
- Vardi, M.Y. and P. Wolper [1986]. An automata-theoretic approach to automatic program verification. Proc. 1st IEEE Symp. on Logic in Camp. Sci., 332-344.
- Wagner, K. [1979]. On w-regular sets. Info. and Cont., 43:123-177.
- Wolper, P. [1983]. Temporal logic can be more expressive. Info. and Cant., 56:72-99.
- Wolper, P. [1986]. Expressing interesting properties of programs in propositional temporal logic. Proc. 13th ACM Symp. on Prine. of Prog. Lang., 184-193.
- Wolper, P., M.Y. Vardi, and A.P. Sistla [1983]. Reasoning about infinite computation paths. Proc. 24th IEEE Symp. on Found. of Compo Sci., 185-194.
- Zwiers, J., A. de Bruin, and W.-P. de Roever [1984]. A proof system for partial correctness of dynamic networks. In Proc. Workshop on Logics of Programs, E. Clarke and D. Kozen (editors). Lec. Notes in Compo Sci. 164, SpringerVerlag, Berlin.
- Zwiers, J., W.-P. de Roever, and P. van Emde Boas [1985]. Compositionality and concurrent networks: Soundness and completeness of a proofsystem. Proc. 12th Int. Colloq. Lang. Prog. Lec. Notes in Compo Sci. 194, Springer-Verlag, Berlin, 509-519.


