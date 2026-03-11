# Compilers: Principles, Techniques, and Tools

Dragon Book.

action: [dragon/README.md](./dragon/README.md)

# 1 Introduction
## 1.1 Language Processors
## 1.2 The Structure of a Compiler
## 1.3 The Evolution of Programming Languages
## 1.4 The Science of Building a Compiler
## 1.5 Applications of Compiler Technology
## 1.6 Programming Language Basics
## 1.7 Summary of Chapter 1
## 1.8 References for Chapter 1

- 1 Bergin, T. J. and R. G. Gibson, **History of Programming Languages**, ACM Press, New York, 1996.
- 2 http://gcc.gnu.org/ .
- 3 http://research.microsoft.com/phoenix/default.aspx .
- 4 Hennessy, J. L. and D. A. Patterson, **Computer Organization and Design: The Hardware/Software Interface**, Morgan-Kaufmann, San Francisco, CA, 2004.
- 5 Scott, M. L., **Programming Language Pragmatics**, second edition, MorganKaufmann, San Francisco, CA, 2006.
- 6 Sethi, R., **Programming Languages: Concepts and Constructs**, AddisonWesley, 1996.
- 7 Wexelblat, R. L., **History of Programming Languages**, Academic Press, New York, 1981.

# 2 A Simple Syntax-Directed Translator

> This chapter is an introduction to the compiling techniques in Chapters 3 through 6 of this book.

> In this chapter, the emphasis is on the front end of a compiler, in particular on lexical analysis, parsing, and intermediate code generation.

> The working Java translator appears in Appendix A.

example:

```
{
  int i; int j; float[100] a; float v; float x;
  while ( true ) {
    do i = i + 1; while ( a[i] < v );
    do j = j - 1; while ( a[j] > v );
    if ( x >= j ) break;
    x = a[i]; a[i] = a[j]; a[j] = x;
  }
}

1:  i = i + 1
2:  t1 = a [ i ]
3:  if t1 < v goto 1
4:  j = j - 1
5:  t2 = a [ j ]
6:  if t2 > v goto 4
7:  ifFalse i >= j goto 9
8:  goto 14
9:  x = a [ i ]
10: t3 = a [ j ]
11: a [ i ] = t3
12: a [ j ] = x
13: goto 1
14:
```

## 2.1 Introduction

three-address instructions: `x = y op z`, where `op` is a binary operator, `y` and `z` are addresses for the operands, and `x` is the address for the result of the operation.

## 2.2 Syntax Definition

### 2.2.1 Definition of Grammars

A **context-free grammar** has four components:

1. A set of **terminal** symbols, sometimes referred to as "tokens". The terminals are the elementary symbols of the language defined by the grammar.

2. A set of **nonterminals**, sometimes called "syntactic variables". Each nonterminal represents a set of strings of terminals, in a manner we shall describe.

3. A set of **productions**, where each production consists of a nonterminal, called the **head** or **left side** of the production, an arrow, and a sequence of terminals and/or nonterminals, called the **body** or **right side** of the production. The intuitive intent of a production is to specify one of the written forms of a construct; if the head nonterminal represents a construct, then the body represents a written form of the construct.

4. A designation of one of the nonterminals as the **start** symbol.

example:

```
list  -> list + digit
list  -> list - digit
list  -> digit
digit -> 0|1|2|3|4|5|6|7|8|9

9-5+2
3-1
7
```

### 2.2.2 Derivations

A grammar **derives** strings by beginning with the start symbol and repeatedly replacing a nonterminal by the body of a production for that nonterminal.

The terminal strings that can be derived from the start symbol form the **language** defined by the grammar.

**Parsing** is the problem of taking a string of terminals and figuring out how to derive it from the start symbol of the grammar, and if it cannot be derived from the start symbol of the grammar, then reporting syntax errors within the string.

> In this chapter, for simplicity, we begin with source program like `9-5+2` in which each character is a terminal.

### 2.2.3 Parse Trees
### 2.2.4 Ambiguity

A grammar can have more than one parse tree generating a given string of terminals. Such a grammar is said to be **ambiguous**.

example:

```
string -> string + string | string - string |0|1|2|3|4|5|6|7|8|9

9-5+2

(9-5)+2
9-(5+2)
```

### 2.2.5 Associativity of Operators


example:

```
right   -> letter = right | letter
letter  -> a|b|...|z

a=b=c

a=(b=c)
```

### 2.2.6 Precedence of Operators

example:

```
expr    -> expr + term
        | expr - term
        | term
term    -> term * factor
        | term / factor
        | factor
factor  -> `digit`
        | ( expr )

9+5*2

9+(5*2)
```

### 2.2.7 Exercises for Section 2.2

## 2.3 Syntax-Directed Translation

**Syntax-directed translation** is done by attaching rules or program fragments to productions in a grammar.

example:

```
expr -> expr1 + term

translate expr1;
translate term;
handle +;
```

==Attributes==

An **attribute** is any quantity associated with a programming construct.

> we use grammar symbols (nonterminals and terminals) to represent programming construct.

examples:

- data types of expressions,
- the number of instructions in the generated code,
- the location of the first instruction in the generated code for a construct.

==(Syntax-directed) translation schemes==

A **translation scheme** is a notation for attaching *program fragments* to the productions of a grammar.

The program fragments are executed when the production is used during syntax analysis.

The combined result of all these fragment executions, in the order induced by the syntax analysis, produces the translation of the program to which this analysis/synthesis process is applied.

### 2.3.1 Postfix Notation
### 2.3.2 Synthesized Attributes

A **syntax-directed definition** associates

1. with each grammar symbol, a set of attributes, and
2. with each production, a set of **semantic rules** for computing the values of the attributes associated with the symbols appearing in the production.

example:

- each nonterminal has a string-valued attribute `t` that represents the postfix notation for the expression generated by that nonterminal in a parse tree.
- the symbol `||` in the sematic rule is the operator for string concatenation.

```
production              semantic rules

expr -> expr1 + term    expr.t = expr1.t || term.t || '+'
expr -> expr1 - term    expr.t = expr1.t || term.t || '-'
expr -> term            expr.t = term.t
term -> 0               term.t = '0'
term -> 1               term.t = '1'
...
term -> 9               term.t = '9'
```


### 2.3.3 Simple Syntax-Directed Definitions
### 2.3.4 Tree Traversals

A **traversal** of a tree starts at the root and visits each node of the tree in some order.

depth-first traversal:

```
procedure visit(node N) {
  for ( each child C of N, from left to right ) {
    visit(C)
  }
  evaluate semantic rules at node N;
}
```

### 2.3.5 Translation Schemes

Program fragments embedded within production bodies are called **semantic actions**.

example:

```
rest -> + term {print('+')} rest1
```

actions for translating into postfix notaion:

```
expr -> expr1 + term  {print('+')}
expr -> expr1 - term  {print('-')}
expr -> term
term -> 0             {print('0')}
term -> 1             {print('1')}
...
term -> 9             {print('9')}
```

### 2.3.6 Exercises for Section 2.3

## 2.4 Parsing

> Programming-language parsers almost always make a single left-to-right scan over the input, looking ahead one terminal at a time, and constructing pieces of the prase tree as they go.

In **top-down** parsers, construction starts at the root and proceeds towards the leaves, while in **bottom-up** parsers, construction starts at the leaves and proceeds towards the root.

### 2.4.1 Top-Down Parsing

The top-down construction of a prase tree, is done by starting with the root, and repeatedly performing thr following two steps:

1. at node N, labeled with nonterminal A, select one of the productions for A and construct children at N for the symbols in the production body.
2. find the next node at which a subtree is to be constructed, typically the leftmost unexpanded nonterminal of the tree.

For some grammars, the above steps can be implemented during a single left-to-right scan of the input string. The current terminal being scanned in the input is frequently referred to as the **lookahead** symbol.

In general, the selction of a production for a nonterminal way invole **trial-and-error**; that is, we may have to try a production and backtrack to try another production if the first is found to be unsuitable.

### 2.4.2 Predictive Parsing

> **Recursive-descent parsing** is a top-down method of syntax analysis in which a set of recursive procedures is used to process the input. One procedure is associated with each nonterminal of a grammar.

**predictive parsing**: a simple form of recursive-descent parsing, in which the lookahead symbol unambiguously determine the flow of control through the procedure body for each nonterminal.

> $FIRST(\alpha)$ in section 4.4.2

### 2.4.3 When to Use ε-Productions
### 2.4.4 Designing a Predictive Parser
### 2.4.5 Left Recursion

left-recursive production example:

```
expr -> expr + term
```

> A left-recursive production can be elimated by rewriting the offending production.

$$
\begin{equation}
\begin{aligned}
& A \rightarrow A \, \alpha \, | \, \beta \\
\implies & A \rightarrow \beta \, R \\
& R \rightarrow \alpha \, R \, | \, \epsilon
\end{aligned}
\end{equation}
$$

- $\alpha$ and $\beta$ are sequences of terminals and nonterminals that do not start with $A$
- nonterminal $R$ and its production $R \rightarrow \alpha \, R$ are **right recursive**.

### 2.4.6 Exercises for Section 2.4

## 2.5 A Translator for Simple Expressions

A syntax-directed translation scheme often serves as the Specification for a translator:

example: action for translating into postfix notation

```
expr  -> expr + term  {print('+')}
      | expr - term   {print('-')}
      | term
term  -> 0            {print('0')}
      | 1             {print('1')}
      | ...
      | 9             {print('9')}
```

### 2.5.1 Abstract and Concrete Syntax

In abstract syntax tree, many nonterminals of a grammar represent programming constructs, but others are "helpers" of on sort of another, such as those representing terms, factors, or other variations of expressions. These heloers typically are not needed and are hence dropped, to emphase the contrast, a parse tree is sometimes called a **concrete syntax tree**.

### 2.5.2 Adapting the Translation Scheme

1. extend left-recursion-elimination technique to multiple productions for $A$.

$$
\begin{equation}
\begin{aligned}
& A \rightarrow A \, \alpha \, | \, A \, \beta \, | \, \gamma \\
\implies & A \rightarrow \gamma \, R \\
& R \rightarrow \alpha \, R \, | \, \beta \, R \, | \, \epsilon
\end{aligned}
\end{equation}
$$

2. semantic actions embedded in the productions are simply carried along in the transformation, as if they were terminals.

example:

apply

$$
\begin{equation}
\begin{aligned}
A &= expr \\
\alpha &= + \, term \, \{print('+')\} \\
\beta &= - \, term \, \{print('-')\} \\
\gamma &= term
\end{aligned}
\end{equation}
$$

```
expr  -> expr + term  {print('+')}          expr  -> term rest
      | expr - term   {print('-')}          rest  -> + term {print('+')} rest
      | term                          ==>         | - term {print('-')} rest
term  -> 0            {print('0')}                | ε
      | 1             {print('1')}          term  -> 0 {print('0')}
      | ...                                       | 1 {print('1')}
      | 9             {print('9')}                | ...
                                                  | 9 {print('9')}
```

### 2.5.3 Procedures for the Nonterminals
### 2.5.4 Simplifying the Translator
### 2.5.5 The Complete Program

``` java
class Parser { /**/ }

public class Postfix { /**/ }
```

## 2.6 Lexical Analysis  

> In this section, a token is a terminal along with additional information.

A sequence of input characters that comprises a single token is called a **lexeme**.

> The lexical analyzer in this section allows numbers, identifiers, and "white space"(blanks, tabs, and newlines) to appear within expression.

example: actions for translating into postfix notation

```
expr    -> expr + term    {print('+')}
        | expr - term     {print('-')}
        | term
term    -> term * factor  {print('*')}
        | term / factor   {print('/')}
        | factor
factor  -> ( expr )
        | `num`           {print(num.value)}
        | `id`            {print(id.lexeme)}
```

### 2.6.1 Removal of White Space and Comments
### 2.6.2 Reading Ahead
### 2.6.3 Constants
### 2.6.4 Recognizing Keywords and Identifiers
### 2.6.5 A Lexical Analyzer
### 2.6.6 Exercises for Section 2.6

## 2.7 Symbol Tables

> **Symbol tables** are data structures that are used by compilers to hold information about source-program structs.

### 2.7.1 Symbol Table Per Scope

> The term "scope of identifier x" really refers to the scope of a particular declaration of x.

``` java
class Env { /**/ }
```

### 2.7.2 The Use of Symbol Tables

> In effect, the role of a symbol table is to pass information from declarations to uses.

example:

```
program ->                  {top=null;}
            block
block   -> '{'              {saved=top; top=new Env(top); print("{ ");}
            decls stmts '}' {top=saved; print("} ")}
decls   -> decls decl
        | ε
decls   -> `type` `id` ';'  {s=new Symbol; s.type=type.lexeme; top.put(id.lexeme, s);}
stmts   -> stmts stmt
        | ε
stmt    -> block
        | factor ';'        {print("; ");}
factor  -> `id`             {s=top.get(id.lexeme); print(id.lexeme); print(":");} print(s.type);
```

## 2.8 Intermediate Code Generation

> The front end of a compiler constructs an **intermediate representation** of the source program from which the back end generates the target program.

### 2.8.1 Two Kinds of Intermediate Representations

- trees: parse trees, abstract syntax trees
- linear representation: three-address code

### 2.8.2 Construction of Syntax Trees

example: construction of syntax trees for expression and statements

```
program -> block                      {return block.n;}
block   -> '{' stmts '}'              {block.n=stmts.n;}
stmts   -> stmts1 stmt                {stmts.n=new Seq(stmts1.n, stmt.n);}
        | ε                           {stmts.n=null;}
stmt    -> expr ';'                   {stmt.n=new Eval(expr.n);}
        | 'if' ( expr ) stmt1         {stmt.n=new If(expr.n, stmt1.n);}
        | 'while' ( expr ) stmt1      {stmt.n=new While(expr.n, stmt1.n);}
        | 'do' stmt1 'while' ( expr ) {stmt.n=new Do(stmt1.n, expr.n);}
        | block                       {stmt.n=block.n;}
expr    -> rel = expr1                {expr.n=new Assign('=', rel.n, expr1.n);}
        | rel                         {expr.n=rel.n;}
rel     -> rel1 < add                 {rel.n=new Rel('<', rel1.n, add.n);}
        | rel1 <= add                 {rel.n=new Rel('<=', rel1.n, add.n);}
        | add                         {rel.n=add.n;}
add     -> add1 + term                {add.n=new Op('+', add1.n, term.n);}
        | term                        {add.n=term.n;}
term    -> term1 * factor             {term.n=new Op('*', term1.n, factor.n);}
        | factor                      {term.n=factor.n;}
factor  -> ( expr )                   {factor.n=expr.n;}
        | `num`                       {factor.n=new Num(num.value);}
```

### 2.8.3 Static Checking

Static checking includes:

- syntactic checking,
- type checking.

### 2.8.4 Three-Address Code

**Three-address code** is a sequence of instructions of the form:

```
x = y op z

; control flow instructions
ifFalse x goto L  ; if x is false, next execute the instruction labeled L
ifTrue x goto L   ; if x is true, next execute the instruction labeled L
goto L            ; next execute the instruction labeled L

; copy value instructions
x = y             ; copy the value of y into x
```

- `x`,`y`,`z` are names, constants, or compiler-generated tempories,
- `op` stands for an operator.


### 2.8.5 Exercises for Section 2.8

## 2.9 Summary of Chapter 2

# 3 Lexical Analysis
## 3.1 The Role of the Lexical Analyzer
## 3.2 Input Buffering  
## 3.3 Specification of Tokens
## 3.4 Recognition of Tokens
## 3.5 The Lexical-Analyzer Generator Lex
## 3.6 Finite Automata
## 3.7 From Regular Expressions to Automata
## 3.8 Design of a Lexical-Analyzer Generator
## 3.9 Optimization of DFA-Based Pattern Matchers  
## 3.10 Summary of Chapter 3
## 3.11 References for Chapter 3

- 1 Aho, A. V., **Algorithms for finding patterns in strings**, in Handbook of Theoretical Computer Science (J. van Leeuwen, ed.), Vol. A, Ch. 5, MIT Press, Cambridge, 1990.
- 2 Aho, A. V. and M. J. Corasick, **Efficient string matching: an aid to bibliographic search**, Comm. ACM 18:6 (1975), pp. 333-340.
- 3 Aho, A. V., B. W. Kernighan, and P. J. Weinberger, **The AWK Programming Language**, Addison-Wesley, Boston, MA, 1988.
- 4 **Flex** home page http://www.gnu.org/software/flex/, Free Software Foundation.
- 5 Hopcroft, J. E., R. Motwani, and J. D. Ullman, **Introduction to Automata Theory, Languages, and Computation**, Addison-Wesley, Boston MA, 2006.
- 6 Human, D. A., **The synthesis of sequential machines**, J. Franklin Inst. 257 (1954), pp. 3{4, 161, 190, 275-303.
- 7 **JFlex** home page http://jflex.de/ .
- 8 http://www.cs.princeton.edu/~appel/modern/java/JLex .
- 9 Kleene, S. C., **Representation of events in nerve nets**, in [16], pp. 3-40.
- 10 Lesk, M. E., **Lex - a lexical analyzer generator**, Computing Science Tech. Report 39, Bell Laboratories, Murray Hill, NJ, 1975. A similar document with the same title but with E. Schmidt as a coauthor, appears in Vol. 2 of the Unix Programmer's Manual, Bell laboratories, Murray Hill NJ, 1975; see http://dinosaur.compilertools.net/lex/index.html .
- 11 Knuth, D. E., J. H. Morris, and V. R. Pratt, **Fast pattern matching in strings**, SIAM J. Computing 6:2 (1977), pp. 323-350.
- 12 McCullough, W. S. and W. Pitts, **A logical calculus of the ideas immanent in nervous activity**, Bul l. Math. Biophysics 5 (1943), pp. 115-133.
- 13 McNaughton, R. and H. Yamada, **Regular expressions and state graphs for automata**, IRE Trans. on Electronic Computers EC-9:1 (1960), pp.38-47.
- 14 Moore, E. F., **Gedanken experiments on sequential machines**, in [16], pp. 129-153.
- 15 Rabin, M. O. and D. Scott, **Finite automata and their decision problems**, IBM J. Res. and Devel. 3:2 (1959), pp. 114-125.
- 16 Shannon, C. and J. McCarthy (eds.), **Automata Studies**, Princeton Univ. Press, 1956.
- 17 Thompson, K., **Regular expression search algorithm**, Comm. ACM 11:6(1968), pp. 419-422.
# 4 Syntax Analysis

## 4.1 Introduction
### 4.1.1 The Role of the Parser
### 4.1.2 Representative Grammars
### 4.1.3 Syntax Error Handling
### 4.1.4 Error-Recovery Strategies

## 4.2 Context-Free Grammars
### 4.2.1 The Formal Definition of a Context-Free Grammar

A context-free grammar consists of terminals, nonterminals, a start symbol, and productions:

1. **Terminals** are the basic symbols from which strings are formed.
2. **Nonterminals** are syntactic variables that denote sets of strings.
3. In a grammar, one nonterminal is distinguished as the **start symbol**, and the set of strings it denotes is the language generated by the grammar.
4. The **productions** of a grammar specify the manner in which the terminals and nonterminals can be combined to form strings. Each production consists of:

(4.1) a nonterminal called the *head* or *left side* of the production;

(4.2) the symbol `->`;

(4.3) a *body* or *right side* consisting of zero or more terminals and nonterminals.

### 4.2.2 Notational Conventions

(1) These symbols are terminals:

- (a) lowercase letters early in the alphabet: `a, b, c`;
- (b) operator symbols: `+, -` and so on;
- (c) punctuation symbols: `()`, `,` and so on;
- (d) the digits: `0, 1, ..., 9`;
- (e) boldface strings: **`id`**, **`if`** and so on.

(2) These symbols are nonterminals:

- (a) uppercase letters early in the alphabet: `A, B, C`;
- (b) the letter `S`: it is usually the start symbol;
- (c) lowercase, italic names: *`expr`*, *`stmt`*;
- (d) when discussing programming constructs, uppercase letter may be used to represent nonterminals for the constructs: expression `E`, terms `T`, factors `F`;

(3) uppercase letters late in the alphabet, `X, Y, Z`, represents *grammar symbols*, that is either nonterminals or terminals;

(4) lowercase letters late in the alphabet, `u, v, ..., z`, represent strings of terminals;

(5) lowercase Greek letters $\alpha$, $\beta$, $\gamma$, represent strings of grammar symbols;

(6) A set of productions $A \rightarrow \alpha_{1}, A \rightarrow \alpha_{2}, \cdots, A \rightarrow \alpha_{k}$ with a commom head `A` (A-productions), may be written $A \rightarrow \alpha_{1} | \alpha_{2} | \cdots | \alpha_{k}$;

(7) unless stated otherwise, the head of the first production is the start symbol.

### 4.2.3 Derivations

consider a nonterminal `A` in the middle of a sequence of grammar symbols, $\alpha A \beta$, where $\alpha$ and $\beta$ are arbitrary strings of grammar symbols, suppose $A \rightarrow \gamma$ is a production, then we write $\alpha A \beta \Rightarrow \alpha \gamma \beta$.

- $\Rightarrow$: derives in one step.

When a sequence of derivation steps $\alpha_{1} \Rightarrow \alpha_{2} \Rightarrow \cdots \alpha_{n}$ rewrites $\alpha_{1}$ to $\alpha_{n}$, we say $\alpha_{1}$ **derives** $\alpha_{n}$.

- $\overset{\ast}{\Rightarrow}$: derives in zero or more steps.
- $\alpha \overset{\ast}{\Rightarrow} \alpha$ for any string $\alpha$;
- if $\alpha \overset{\ast}{\Rightarrow} \beta$ and $\beta \Rightarrow \gamma$, then $\alpha \overset{\ast}{\Rightarrow} \gamma$.


If $S \overset{\ast}{\Rightarrow} \alpha$, `S` is the start symbol of a grammar G, we say that $\alpha$ is a **sentential form** of G.

A **sentence** of G is a sentential form with no nonterminals.

The **language** generated by a grammar is its set of sentences. A language that can be generate by a grammar is said to be a **context-free language**.


consider derivations in which the nonterminals to be replaced at each step:

- in **leftmost** derivations, the leftmost nonterminal in each sentential is always chosen. if $\alpha \Rightarrow \beta$ is a step in which the leftmost nonterminal in $\alpha$ is replaced, we weite $\alpha \underset{lm}{\Rightarrow} \beta$.
- in **rightmost** derivations, the rightmost nonterminal is always chosend, we write $\alpha \underset{rm}{\Rightarrow} \beta$.

$\alpha \overset{\ast}{\underset{lm}{\Rightarrow}} \beta$:  $\alpha$ derives $\beta$ by a leftmorst derivation.

If $S \overset{\ast}{\underset{lm}{\Rightarrow}} \alpha$, the we say that $\alpha$ is a **left-sentential form** of the grammar.

rightmost derivations are sometimes callled **canonical derivations**.

### 4.2.4 Parse Trees and Derivations
### 4.2.5 Ambiguity
### 4.2.6 Verifying the Language Generated by a Grammar

A proof that a grammar G generates a language L has two parts:

- show that every string generate by G is in L;
- every string in L can indeed be generated by G.

### 4.2.7 Context-Free Grammars Versus Regular Expressions

Every regular language is a context-free language, but not vice-versa.

### 4.2.8 Exercises for Section 4.2

## 4.3 Writing a Grammar
### 4.3.1 Lexical Versus Syntactic Analysis
### 4.3.2 Eliminating Ambiguity
### 4.3.3 Elimination of Left Recursion

==Algorithm 4.19: Eliminating left recursion.==

### 4.3.4 Left Factoring

==Algorithm 4.21: Left factoring a grammar.==

### 4.3.5 Non-Context-Free Language Constructs

A few syntactic constructs found in typical programming languages cannot be specified using grammars alone:

- the problem of checking that identifiers are declared before they are used in a program;
- the problem of checking that the number of formal parameters in the declaration of a function agrees with the number of actual parameters in a use of the function.

### 4.3.6 Exercises for Section 4.3

## 4.4 Top-Down Parsing
### 4.4.1 Recursive-Descent Parsing
### 4.4.2 FIRST and FOLLOW

Purpose:

- during top-down parsing, `FIRST` and `FOLLOW` allow us to choose which production to apply, based on the next input symbol;
- during panic-mode error recovery, sets of tokens produced by `FOLLOW` can be used as synchronizing tokens.

$FIRST(\alpha)$:

- $\alpha$ is any string of grammar symbols; the set of terminals that begin string derived from `\alpha`.
- If $\alpha \overset{\ast}{\Rightarrow} \epsilon$, then $\epsilon$ is also in $FIRST(\alpha)$.

$FOLLOW(A)$:

- for nonterminal `A`, the set of terminals `a` that can appear immediately to the right of `A` in some sentential form: $S \overset{\ast}{\Rightarrow} \alpha A a \beta$.
- there may have been symbols between `A` and `a` at some time during the derivation, but if so, they derive $\epsilon$ and disappeared.
- If `A` can be the rightmost symbol in some sentential form, then `$` is in $FOLLOW(A)$.

> TBD: method for calculating $FIRST(\alpha)$ and $FOLLOW(A)$

### 4.4.3 LL(1) Grammars

Predictive parsers (that is recursive-descent parsers needing no backtracking) can be constructed for a class of grammar called **LL(1)**:

- first `L`: scanning the input from left to right,
- second `L`: producing a leftmost derivation,
- `1`: using one input symbol of lookahead at each step to make parsing action decisions.

A grammar G is LL(1) *if and only if* whenever $A \rightarrow \alpha | \beta$ are two distinct productions of G, the following conditions hold:

- 1 for no terminal `a` do both $\alpha$ and $\beta$ derive strings beginning with `a`;
- 2 at most one of $\alpha$ and $\beta$ can derive the empty string;
- 3 if $\beta \overset{\ast}{\Rightarrow} \epsilon$, then $\alpha$ does not derive any string beginning with a terminal in $FOLLOW(A)$. If $\alpha \overset{\ast}{\Rightarrow} \epsilon$, then $\beta$ does not derive any string beginning with a terminal in $FOLLOW(A)$.

==Algorithm 4.31: Construction of a predictive parsing table.==

### 4.4.4 Nonrecursive Predictive Parsing

==Algorithm 4.34: Table-driven predictive parsing.==

### 4.4.5 Error Recovery in Predictive Parsing
### 4.4.6 Exercises for Section 4.4

## 4.5 Bottom-Up Parsing

A **bottom-up parse** corresponds to the construction of a parse tree for an input beginning at the leaves, and working up towards the root.

### 4.5.1 Reductions

> We can think of bottom-up parsing as the process of **reducing** a string `w` to the start symbol of the grammar.

At each reduction step, a specific substring matching the body of a production, is replaced by the nonterminal at the head of that production.

### 4.5.2 Handle Pruning
### 4.5.3 Shift-Reduce Parsing

**shift-reduce parsing** is a form of the bottom-up parsing in which a *stack* holds grammar symbols, and an *input buffer* holds the rest of the string to be parsed.

4 actions:

- (1) **shift**: shift the next input symbol onto the top of the stack;
- (2) **reduce**: the right end of the string to be reduced must be at the top of the stack; locate the left end of the string with the stack and decide with what nonterminal to replace the string;
- (3) **accept**: announce successful completion of parsing;
- (4) **error**: discover a syntax error (and call an error recovery routine).

### 4.5.4 Conflicts During Shift-Reduce Parsing

- shift/reduce conflict
- reduce/reduce conflict

### 4.5.5 Exercises for Section 4.5

## 4.6 Introduction to LR Parsing: Simple LR

**LR(k)** parsing: type of bottom-up parser

- `L`: left-to-right scanning of the input,
- `R`: constructing a rightmost derivations in reverse,
- `k`: the number of input symbols of lookahead that are used in making parsing decisions.

### 4.6.1 Why LR Parsers?
### 4.6.2 Items and the LR(0) Automaton
### 4.6.3 The LR-Parsing Algorithm
### 4.6.4 Constructing SLR-Parsing Tables
### 4.6.5 Viable Prefixes
### 4.6.6 Exercises for Section 4.6

## 4.7 More Powerful LR Parsers
### 4.7.1 Canonical LR(1) Items
### 4.7.2 Constructing LR(1) Sets of Items
### 4.7.3 Canonical LR(1) Parsing Tables
### 4.7.4 Constructing LALR Parsing Tables
### 4.7.5 Ecient Construction of LALR Parsing Tables
### 4.7.6 Compaction of LR Parsing Tables
### 4.7.7 Exercises for Section 4.7

## 4.8 Using Ambiguous Grammars
### 4.8.1 Precedence and Associativity to Resolve Conflicts
### 4.8.2 The "Dangling-Else" Ambiguity
### 4.8.3 Error Recovery in LR Parsing
### 4.8.4 Exercises for Section 4.8

## 4.9 Parser Generators
### 4.9.1 The Parser Generator Yacc
### 4.9.2 Using Yacc with Ambiguous Grammars
### 4.9.3 Creating Yacc Lexical Analyzers with Lex
### 4.9.4 Error Recovery in Yacc
### 4.9.5 Exercises for Section 4.9

## 4.10 Summary of Chapter 4
## 4.11 References for Chapter 4

- 1 Aho, A. V., S. C. Johnson, and J. D. Ullman, **Deterministic parsing of ambiguous grammars** Comm. ACM 18:8 (Aug., 1975), pp. 441-452.
- 2 Backus, J.W, **The syntax and semantics of the proposed international algebraic language of the Zurich-ACM-GAMM Conference**, Proc. Intl. Conf. Information Processing, UNESCO, Paris, (1959) pp. 125-132.
- 3 Birman, A. and J. D. Ullman, **Parsing algorithms with backtrack**, Information and Control 23:1 (1973), pp. 1-34.
- 4 Cantor, D. C., **On the ambiguity problem of Backus systems**, J. ACM 9:4 (1962), pp. 477-479.
- 5 Chomsky, N., **Three models for the description of language**, IRE Trans. on Information Theory IT-2:3 (1956), pp. 113-124.
- 6 Chomsky, N., **On certain formal properties of grammars**, Information and Control 2:2 (1959), pp. 137-167.
- 7 Dain, J., **Bibliography on Syntax Error Handling in Language Translation Systems**, 1991. Available from the comp.compilers newsgroup; see http://compilers.iecc.com/comparch/article/91-04-050 .
- 8 DeRemer, F., **Practical Translators for LR(k) Languages**, Ph.D. thesis, MIT, Cambridge, MA, 1969.
- 9 DeRemer, F., **Simple LR(k) grammars**, Comm. ACM 14:7 (July, 1971), pp. 453-460.
- 10 Donnelly, C. and R. Stallman, **Bison: The YACC-compatible Parser Generator**, http://www.gnu.org/software/bison/manual/ .
- 11 Earley, J., **An ecient context-free parsing algorithm**, Comm. ACM 13:2 (Feb., 1970), pp. 94-102.
- 12 Earley, J., **Ambiguity and precedence in syntax description**, Acta Informatica 4:2 (1975), pp. 183-192.
- 13 Floyd, R. W., **On ambiguity in phrase-structure languages**, Comm. ACM 5:10 (Oct., 1962), pp. 526-534.
- 14 Floyd, R. W., **Syntactic analysis and operator precedence**, J. ACM 10:3 (1963), pp. 316-333.
# 5 Syntax-Directed Translation
## 5.1 Syntax-Directed Definitions

A **syntax-directed definition(SDD)** is a context-free grammar together with attributes and rules. Attributes are associated with grammar symbols and rules are associated with productions.

### 5.1.1 Inherited and Synthesized Attributes

2 kinds of attributes for nonterminals:

- 1 A **synthesis attribute** for a nonterminal A at a parse-tree node N is defined by a semantic rule associated with *the production at N*. A synthesized attribute at node N is defined only in terms of attribute values at *the children of N* and at *N itself*.

- 2 An **inherited attribute** for a nonterminal B at a parse-tree node N is defined by a semantic rule associated with *the production at the parent of N*. An inherited attribute at node N is defined only in terms of attribute values at *N's parent*, *N itself*, and *N's siblings*.

Figure 5.1 Syntax-directed definition of a simple desk calculator

```
   PRODUCTION   SEMANTIC RULES

1) L -> E n     L.val = E.val
2) E -> E1 + T  E.val = E1.val + T.val
3) E -> T       E.val = T.val
4) T -> T1 * F  T.val = T1.val X F.val
5) T -> F       T.val = F.val
6) F -> ( E )   F.val = E.val
7) F -> digit   F.val = digit.lexval
```

A SSD that involves only synthesized attributes is called **S-attributed**.

A SSD without side effects is sometimes called an **attributed grammar**.

### 5.1.2 Evaluating an SDD at the Nodes of a Parse Tree

A parse tree, showing the values of its attributes is called an **annotated parse tree**.

With *synthesized attribute*, we can evaluate attributes in any bottom-up order, such as that of a postorder traversal of the parse tree.

For SDDs with both *inherited* and *synthesized* attributes, there is no guarantee that there is even one order in which to evaluate attributes at nodes.

Figure 5.3 Annotated parse tree for 3 * 5 + 4 n (using SDD in Figure 5.1)

```
                      L.val = 19
                            |-----------|
                      E.val = 19        n
              |-------------|--------------|
        E.val = 15          +           T.val = 4
              |                            |
        T.val = 15                      F.val = 4
    |---------|---------|                  |
T.val = 3     *    F.val = 5         digit.lexval = 4
    |                   |
F.val = 3         digit.lexval = 5
    |
digit.lexval = 3
```

Figure 5.4 An SDD based on a grammar suitable for top-down parsing

```
   PRODUCTION     SEMANTIC RULES

1) T -> F T'      T'.inh = F.val
                  T.val = T'.syn
2) T' -> * F T1'  T1'.inh = T.inh X F.val
                  T'.syn = T1'.syn
3) T' -> ε        T'.syn = T'.inh
4) F -> digit     F.val = digit.lexval
```
- `T` and `F` have a synthesized attribute `val`,
- `digit` has a synthesized attribute `lexval`,
- `T'` has an inherited attribute `inh` and a synthesized attribute `syn`.

Figure 5.5 Annotated parse tree for 3 * 5 (using SDD in Figure 5.4)

```
              T.val = 15
    |-------------|-------------|
F.val = 3                   T'.inh =3
    |                       T'.syn = 15
    |                 |---------|---------------|
digit.lexval = 3      *     F.val = 5       T1'.inh = 15
                                |           T1'.syn = 15
                                |               |
                          digit.lexval = 4      ε
```

### 5.1.3 Exercises for Section 5.1

## 5.2 Evaluation Orders for SDD's
### 5.2.1 Dependency Graphs

A **dependency graph** depicts the flow of information among the attribute instances in a particular tree; a tree from one attribute instance to another means the value of the first is needed to compute the second.

- 1 For each parse-tree node, a node labeled by grammar symbol X, the dependency graph has a node for each attribute associated with X.

- 2 Suppose a semantic rule associated with a production p defines the value of *synthesized attribute* A.b in terms of the value of X.c (the rule may define A.b in terms of other attributes in addition to X.c), then the dependency graph has an edge from X.c to A.b.

- 3 Suppose a semantic rule associated with a production p defines the value of *inherited attribute* B.c in terms of the value of X.a, then the dependency graph has an edge from X.a to B.c.

### 5.2.2 Ordering the Evaluation of Attributes

If the dependency graph as an edge from node M to node N, then the attribute corresponding to M must be evaluated before the attribute of N. Such an ordering of the only allowable orders of evaluation embeds a directed graph into a linear order, is called a **topological sort** of the graph.

If there is any cycle in the graph, then there are not topological sorts, that is, there is no way to evaluate the SDD on this parse tree.

If there are not cycles, then there is always at least one topological sort.

### 5.2.3 S-Attributed Definitions

An SDD is **S-attributed** if every attribute is *synthesized*.

When an SDD is S-attributed, we can evaluate its attributes in any bottom-up order of the nodes of the parse tree.

### 5.2.4 L-Attributed Definitions

ideas behind L-attributed SDDs is that, between the attributes associated with a production body, dependency graph edges go from left to right, but not from right to left.

An SDD is **L-attributed**, each attributed must be either:

(1) synthesized, or

(2) inherited, but with rules limited. suppose A -> X1 X2 ... Xn, and there is a inherited attribute Xi.a computed by a rule associated with this production, then the rule may use only:

(2.1) inherited attributes associated with the head A;
(2.2) either inherited or synthesized attributes with the occurrence of symbols X1,X2,...,Xi-1 located to the left of Xi;
(2.3) inherited or synthesized attributes associated with this occurrence of Xi itself, but only in such a way that there are no cycles in a dependency graph formed by the attributes of this Xi.

The SDD in Figure 5.4 is L-attributed.

### 5.2.5 Semantic Rules with Controlled Side Effects

We shall control side effect in SDDs in one of the following ways:

- 1 Permit side effects when attribute evaluation based on any topological sort of the dependency graph produces a "correct" translation, where "correct" depends on the application.
- 2 Constrain the allowable evaluation orders, so that the same translation is produced for any allowable order.

### 5.2.6 Exercises for Section 5.2

## 5.3 Applications of Syntax-Directed Translation

We consider 2 SDDs for constructing syntax trees for expression.

The final example is an L-attributed definition that deals with base and array types.

### 5.3.1 Construction of Syntax Trees

Figure 5.10 Constructing syntax trees for simple expression

```
   PRODUCTION   SEMANTIC RULES

1) E -> E1 + T  E.node = new Node('+', E1.node, T.node)
2) E -> E1 - T  E.node = new Node('+', E1.node, T.node)
3) E -> T       E.node = T.node
4) T -> ( E )   T.node = E.node
5) T -> id      T.node = new Leaf(id, id.entry)
6) T -> num     T.node = new Leaf(num, num.val)
```

implement the nodes of a syntax tree by objects with a suitable number of fields:

- `op`: the label of the node,
- `Leaf(op, val)`: create a leaf object,
- `Node(op,c1,c2,...,ck)`: create an object with first field `op` and k additional fields for the k children `c1,c2,...,ck`.

Figure 5.11 Syntax tree for a-4+c

```
              | [+  |  | ] |
              | --- ||-------|
     | [-  |  | ]            [id | ] |
     | --- ||---|             |-- to entry for c
[id | ]   [num|4]
     |-- to entry for a
```

Figure 5.12 Steps in the construction of the syntax tree for a-4+c

```
1) p1 = new Leaf(id, entry-a);
2) p2 = new Leaf(num, 4);
3) p3 = new Node('-', p1, p2);
4) p4 = new Leaf(id, entry-c);
5) p5 = new Node('+', p3, p4);
```

Figure 5.13 Constructing syntax trees during top-down parsing

```
   PRODUCTION     SEMANTIC RULES

1) E -> T E'      E.node = E'.syn
                  E'.inh = T.node
2) E' -> + T E1'  E1'.inh = new Node('+', E'.inh, T.node)
                  E'.syn = E1'.syn
3) E' -> - T E1'  E1'.inh = new Node('-', E'.inh, T.node)
                  E'.syn = E1'.syn
4) E' -> ε        E'.syn = E'.inh
5) T -> ( E )     T.node = E.node
6) T -> id        T.node = new Leaf(id, id.entry)
7) T -> num       T.node = new Leaf(num, num.val)
```

- `E'` has an inherited attribute `inh` and a synthesized attribute `syn`.
- `E'.inh`: represents the partial syntax tree constructed so far.

### 5.3.2 The Structure of a Type

Figure 5.16 T generates either a basic type of an array type

```
PRODUCTION        SEMANTIC RULES

T -> B C          T.t = C.t
                  C.b = B.t
B -> int          B.t = integer
B -> float        B.t = float
C -> [ num ] C1   C.t = array(num.val, C1.t)
                  C1.b = C.b
C -> ε            C.t = C.b
```

- `B` and `T` has a synthesized attribute `t`: represent a type,
- `C` has two attributes: an inherited attribute `b` and a synthesized attribute `t`,
- `b` pass a basic type down the tree,
- `t` accumulate the result.

### 5.3.3 Exercises for Section 5.3

## 5.4 Syntax-Directed Translation Schemes
### 5.4.1 Postfix Translation Schemes
### 5.4.2 Parser-Stack Implementation of Postfix SDT's
### 5.4.3 SDT's With Actions Inside Productions
### 5.4.4 Eliminating Left Recursion From SDT's
### 5.4.5 SDT's for L-Attributed Definitions
### 5.4.6 Exercises for Section 5.4

### 5.4.7 Implementing L-Attributed SDD's
### 5.4.8 Translation During Recursive-Descent Parsing
### 5.4.9 On-The-Fly Code Generation
### 5.4.10 L-Attributed SDD's and LL Parsing
### 5.4.11 Bottom-Up Parsing of L-Attributed SDD's
### 5.4.12 Exercises for Section 5.5

## 5.5 Summary of Chapter 5
## 5.6 References for Chapter 5

- 1 Brooker, R. A. and D. Morris, **A general translation program for phrase structure languages**, J. ACM 9:1 (1962), pp. 1-10.
- 2 Irons, E. T., **A syntax directed compiler for Algol 60**, Comm. ACM 4:1 (1961), pp. 51{55.
- 3 Jazayeri, M., W. F. Ogden, and W. C. Rounds, **The intrinsic exponential complexity of the circularity problem for attribute grammars**, Comm. ACM 18:12 (1975), pp. 697-706.
- 4 Johnson, S. C., **Yacc - Yet Another Compiler Compiler**, Computing Science Technical Report 32, Bell Laboratories, Murray Hill, NJ, 1975. Available at http://dinosaur.compilertools.net/yacc/ .
- 5 Knuth, D.E., **Semantics of context-free languages**, Mathematical Systems Theory 2:2 (1968), pp. 127{145. See also Mathematical Systems Theory 5:1 (1971), pp. 95-96.
- 6 Lewis, P. M. II, D. J. Rosenkrantz, and R. E. Stearns, **Attributed translations**, J. Computer and System Sciences 9:3 (1974), pp. 279-307.
- 7 Paakki, J., **Attribute grammar paradigms - a high-level methodology in language implementation**, Computing Surveys 27:2 (1995), pp. 196-255.
- 8 Samelson, K. and F. L. Bauer, **Sequential formula translation**, Comm. ACM 3:2 (1960), pp. 76-83.  
# 6 Intermediate-Code Generation


## 6.1 Variants of Syntax Trees
### 6.1.1 Directed Acyclic Graphs for Expressions
### 6.1.2 The Value-Number Method for Constructing DAG's
### 6.1.3 Exercises for Section 6.1

## 6.2 Three-Address Code
### 6.2.1 Addresses and Instructions


Three-code address is built from two concepts: **addresses** and **instructions**.

An address can be one of the following:

- A **name**. For convenience, we allow source-program names to appear as addresses in three-address code. In an implementation, a source name is replaced by a pointer to its symbol-table entry, where all information about the name is kept.
- A **constants**.
- A **compiler-generated temporary**.

A **symbolic label** represents the index of a three-address instruction in the sequence of instructions.

A list of the common three-address instruction forms:

- (1) Assignment instruction `x = y op z`, `op` is a binary arithmetic or logical operations, `x,y,z` are addresses.
- (2) Assignment instruction `x = op y`, `op` is a unary operation.
- (3) Copy instruction `x = y`, `x` is assigned the value of `y`.
- (4) An unconditional jump `goto L`. The three-address instruction with label `L` is the next to be executed.
- (5) Conditional jumps `if x goto L` and `ifFalse x goto L`. These instructions execute the instruction with label `L` next if `x` is true or false respectively. Otherwise, the next instruction in sequence is excuted next as usual.
- (6) Conditional jumps, such as `if x relop y goto L`, execute the instruction with label `L` if `x` stands in relation `relop` to `y`; if not, the instruction following `if x relop y goto L` is executed next.
- (7) Procedure calls and returns: `param x` for parameters, `call p,n` and `y = call p,n` for procedure and function calls respectively, `return y` for returns, where `y` representing an optional returned value.

part of a call of the procedure `p(x1,x2,...,xn)`:

```
param x1
param x2
...
param xn
call p,n
```

- (8) Indexed copy instruction `x=y[i]` and `x[i]=y`. `x=y[i]` sets `x` the the value in the location `i` memory units beyond location `y`; `x[i]=y` sets the contents of the location `i` units beyond `x` to the value of `y`.
- (9) Address and pointer assignment instruction `x=&y`, `x=*y` and `*x=y`. `x=&y` sets the location (r-value) of `x` to be the location (l-value) of `y`; `x=*y` presumably `y` is a pointer or a temporary whose r-value is a location; `*x=y` sets the r-value of the object pointed to by `x` to the r-value of `y`.

Example:

```
// statement
do i = i + 1; while (a[i] < v)

// 2 translations to three-address code
L: t1 = i + 1
   i = t1
   t2 = i * 8
   t3 = a [ t2 ]
   if t3 < v goto L

100: t1 = i + 1
102: i = t1
103: t2 = i * 8
104: t3 = a [ t2 ]
105: if t3 < v goto L
```
### 6.2.2 Quadruples

In a compiler, three-address instructions can be implemented as objects or as records with fields for the operator and the operands.

3 representations of three-address instructions in a data structure:

(1) **quadruple**/**quad** has 4 fields `op, arg1, arg2, result`

- `op` field contains an internal code for the operator

example:

```
x = y + z

op  arg1 arg2 result
+   y     z   x
```

exceptions:

- Instructions with unary operators do not use `arg2`: `x = minus y`, `x = y`;
- Operators like `param` use neither `arg2` nor `result`;
- Conditional and unconditional jumps put the target label in `result`.

### 6.2.3 Triples

(2) **triple** has 3 fields `op, arg1, arg2`, refer to the result of an operation `x op y` to its position.

example:

```
a = b * -c + b * -c

  op    arg1 arg2
0 minus c
1 *     b    (0)
2 minus c
3 *     b    (2)
4 +     (1)  (3)
5 =     a    (4)
```

(3) **indirect triples** consist of a listing of pointers to triples.

example:

```
a = b * -c + b * -c

    instruction   op    arg1 arg2
35  (0)         0 minus c
36 (1)          1 *     b    (0)
37 (2)          2 minus c
38 (3)          3 *     b    (2)
39 (4)          4 +     (1)  (3)
40 (5)          5 =     a    (4)
```

### 6.2.4 Static Single-Assignment Form

All assignment in SSA(Static Single-Assignment) form are to variables with distinct names, example:


```
three-address code    SSA form

p = a + b             p1 = a + b
q = p - c             q1 = p1 - c
p = q * d             p2 = q1 * d
p = e - p             p3 = e - p2
q = p + q             q2 = p3 + q1
```

SSA uses a notational convention called the φ-function to combine the two defitions of a variables, example:


```
if (flag) x = -1; else x 1;
y = x * a;


if (flag) x1 = -1; else x2 = 1;
x3 = φ(x1, x2);
y = x3 * a;
```

### 6.2.5 Exercises for Section 6.2

## 6.3 Types and Declarations
### 6.3.1 Type Expressions
### 6.3.2 Type Equivalence
### 6.3.3 Declarations
### 6.3.4 Storage Layout for Local Names
### 6.3.5 Sequences of Declarations
### 6.3.6 Fields in Records and Classes
### 6.3.7 Exercises for Section 6.3

## 6.4 Translation of Expressions
### 6.4.1 Operations Within Expressions
### 6.4.2 Incremental Translation
### 6.4.3 Addressing Array Elements
### 6.4.4 Translation of Array References
### 6.4.5 Exercises for Section 6.4

## 6.5 Type Checking
### 6.5.1 Rules for Type Checking
### 6.5.2 Type Conversions
### 6.5.3 Overloading of Functions and Operators
### 6.5.4 Type Inference and Polymorphic Functions
### 6.5.5 An Algorithm for Uni### cation
### 6.5.6 Exercises for Section 6.5

## 6.6 Control Flow
### 6.6.1 Boolean Expressions
### 6.6.2 Short-Circuit Code
### 6.6.3 Flow-of-Control Statements
### 6.6.4 Control-Flow Translation of Boolean Expressions
### 6.6.5 Avoiding Redundant Gotos
### 6.6.6 Boolean Values and Jumping Code
### 6.6.7 Exercises for Section 6.6

## 6.7 Backpatching
### 6.7.1 One-Pass Code Generation Using Backpatching
### 6.7.2 Backpatching for Boolean Expressions
### 6.7.3 Flow-of-Control Statements
### 6.7.4 Break-, Continue-, and Goto-Statements
### 6.7.5 Exercises for Section 6.7

## 6.8 Switch-Statements
### 6.8.1 Translation of Switch-Statements
### 6.8.2 Syntax-Directed Translation of Switch-Statements
### 6.8.3 Exercises for Section 6.8

## 6.9 Intermediate Code for Procedures

## 6.10 Summary of Chapter 6

## 6.11 References for Chapter 6

- 1 Ershov, A. P., **On programming of arithmetic operations**, Comm. ACM 1:8 (1958), pp. 3{6. See also Comm. ACM 1:9 (1958), p. 16.
- 2 Feldman, S. I., **Implementation of a portable Fortran 77 compiler using modern tools**, ACM SIGPLAN Notices 14:8 (1979), pp. 98-106.
- 3 **GCC** home page http://gcc.gnu.org/, Free Software Foundation.
- 4 Gosling, J., **Java intermediate bytecodes**, Proc. ACM SIGPLAN Workshop on Intermediate Representations (1995), pp. 111-118.
- 5 Huskey, H. D., M. H. Halstead, and R. McArthur, **Neliac - a dialect of Algol**, Comm. ACM 3:8 (1960), pp. 463-468.
- 6 Johnson, S. C., **A tour through the portable C compiler**, Bell Telephone Laboratories, Inc., Murray Hill, N. J., 1979.
- 7 Milner, R., **A theory of type polymorphism in programming**, J. Computer and System Sciences 17:3 (1978), pp. 348-375.
- 8 Pierce, B. C., **Types and Programming Languages**, MIT Press, Cambridge, Mass., 2002.
- 9 Ritchie, D. M., **A tour through the UNIX C compiler**, Bell Telephone Laboratories, Inc., Murray Hill, N. J., 1979.
- 10 Strong, J., J. Wegstein, A. Tritter, J. Olsztyn, O. Mock, and T. Steel, **The problem of programming communication with changing machines: a proposed solution**, Comm. ACM 1:8 (1958), pp. 12-18. Part 2: 1:9 (1958), pp. 9-15. Report of the SHARE Ad-Hoc Committee on Universal Languages.
- 11 Wirth, N. **The design of a Pascal compiler**, Software|Practice and Experience 1:4 (1971), pp. 309-333.
# 7 Run-Time Environments
## 7.1 Storage Organization  
## 7.2 Stack Allocation of Space
## 7.3 Access to Nonlocal Data on the Stack  
## 7.4 Heap Management  
## 7.5 Introduction to Garbage Collection  
## 7.6 Introduction to Trace-Based Collection
## 7.7 Short-Pause Garbage Collection
## 7.8 Advanced Topics in Garbage Collection
## 7.9 Summary of Chapter 7
## 7.10 References for Chapter 7

- 1 Baker, H. G. Jr., **The treadmill: real-time garbage collection without motion sickness**, ACM SIGPLAN Notices 27:3 (Mar., 1992), pp. 66-70.
- 2 Cheney, C. J., **A nonrecursive list compacting algorithm**, Comm. ACM 13:11 (Nov., 1970), pp. 677-678.
- 3 Church, A., **The Calculi of Lambda Conversion**, Annals of Math. Studies, No. 6, Princeton University Press, Princeton, N. J., 1941.
- 4 Collins, G. E., **A method for overlapping and erasure of lists**, Comm. ACM 2:12 (Dec., 1960), pp. 655-657.
- 5 Dijkstra, E. W., **Recursive programming**, Numerische Math. 2 (1960), pp. 312{318.
- 6 Dijkstra, E. W., L. Lamport, A. J. Martin, C. S. Scholten, and E. F. M. Steens, **On-the-fly garbage collection: an exercise in cooperation**, Comm. ACM 21:11 (1978), pp. 966-975.
- 7 Fenichel, R. R. and J. C. Yochelson, **A Lisp garbage-collector for virtualmemory computer systems**, Comm. ACM 12:11 (1969), pp. 611{612.
- 8 Frege, G., **Begriffsschrift, a formula language, modeled upon that of arithmetic, for pure thought**, (1879). In J. van Heijenoort, From Frege to Godel, Harvard Univ. Press, Cambridge MA, 1967.
- 9 Hudson, R. L. and J. E. B. Moss, **Incremental Collection of Mature Objects**, Proc. Intl. Workshop on Memory Management, Lecture Notes In Computer Science 637 (1992), pp. 388-403.
- 10 Johnson, S. C. and D. M. Ritchie, **The C language calling sequence**, Computing Science Technical Report 102, Bell Laboratories, Murray Hill NJ, 1981.
- 11 Knuth, D. E., **Art of Computer Programming, Volume 1: Fundamental Algorithms**, Addison-Wesley, Boston MA, 1968.
- 12 Lieberman, H. and C. Hewitt, **A real-time garbage collector based on the lifetimes of objects**, Comm. ACM 26:6 (June, 1983), pp. 419-429.
- 13 McCarthy, J., **Recursive functions of symbolic expressions and their computation by machine**, Comm. ACM 3:4 (Apr., 1960), pp. 184-195.
- 14 McCarthy, J., **History of Lisp.** See pp. 173-185 in R. L. Wexelblat (ed.), History of Programming Languages, Academic Press, New York, 1981.
- 15 Minsky, M., **A LISP garbage collector algorithm using secondary storage**, A. I. Memo 58, MIT Pro ject MAC, Cambridge MA, 1963.
- 16 Randell, B. and L. J. Russell, **Algol 60 Implementation**, Academic Press, New York, 1964.
- 17 Wilson, P. R., **Uniprocessor garbage collection techniques**, ftp://ftp.cs.utexas.edu/pub/garbage/bigsurv.ps
# 8 Code Generation
## 8.1 Issues in the Design of a Code Generator
## 8.2 The Target Language
## 8.3 Addresses in the Target Code  
## 8.4 Basic Blocks and Flow Graphs
## 8.5 Optimization of Basic Blocks
## 8.6 A Simple Code Generator
## 8.7 Peephole Optimization  
## 8.8 Register Allocation and Assignment  
## 8.9 Instruction Selection by Tree Rewriting  
## 8.10 Optimal Code Generation for Expressions
## 8.11 Dynamic Programming Code-Generation
## 8.12 Summary of Chapter 8  
## 8.13 References for Chapter 8  

- 1 Aho, A. V. and S. C. Johnson, **Optimal code generation for expression trees**, J. ACM 23:3, pp. 488-501.
- 2 Aho, A. V., M. Ganapathi, and S. W. K. Tjiang, **Code generation using tree matching and dynamic programming**, ACM Trans. Programming Languages and Systems 11:4 (1989), pp. 491-516.
- 3 Chaitin, G. J., M. A. Auslander, A. K. Chandra, J. Cocke, M. E. Hopkins, and P. W. Markstein, **Register allocation via coloring**, Computer Languages 6:1 (1981), pp. 47-57.
- 4 Chaitin, G. J., **Register allocation and spilling via graph coloring**, ACM SIGPLAN Notices 17:6 (1982), pp. 201-207.
- 5 Chow, F. and J. L. Hennessy, **The priority-based coloring approach to register allocation**, ACM Trans. Programming Languages and Systems 12:4 (1990), pp. 501-536.
- 6 Cooper, K. D. and L. Torczon, **Engineering a Compiler**, Morgan Kaufmann, San Francisco CA, 2004.
- 7 Ershov, A. P., **On programming of arithmetic operations**, Comm. ACM 1:8 (1958), pp. 3-6. Also, Comm. ACM 1:9 (1958), p. 16.
- 8 Ershov, A. P., **The Alpha Automatic Programming System**, Academic Press, New York, 1971.
- 9 Fischer, C. N. and R. J. LeBlanc, **Crafting a Compiler with C**, BenjaminCummings, Redwood City, CA, 1991.
- 10 Fraser, C. W., D. R. Hanson, and T. A. Proebsting, **Engineering a simple, effcient code generator generator**, ACM Letters on Programming Languages and Systems 1:3 (1992), pp. 213-226.
- 11 Glanville, R. S. and S. L. Graham, **A new method for compiler code generation**, Conf. Rec. Fifth ACM Symposium on Principles of Programming Languages (1978), pp. 231-240.
- 12 Hennessy, J. L. and D. A. Patterson, **Computer Architecture: A Quantitative Approach**, Third Edition, Morgan Kaufman, San Francisco, 2003.
- 13 Lowry, E. S. and C. W. Medlock, **Object code optimization**, Comm. ACM 12:1 (1969), pp. 13-22.
- 14 Pelegri-Llopart, E. and S. L. Graham, **Optimal code generation for expressions trees: an application of BURS theory**, Conf. Rec. Fifteenth Annual ACM Symposium on Principles of Programming Languages (1988), pp. 294-308.
- 15 Schwartz, J. T., **On Programming: An Interim Report on the SETL Project**, Technical Report, Courant Institute of Mathematical Sciences, New York, 1973.
- 16 Sethi, R. and J. D. Ullman, **The generation of optimal code for arithmetic expressions**, J. ACM 17:4 (1970), pp. 715-728.
# 9 Machine-Independent Optimizations
## 9.1 The Principal Sources of Optimization
## 9.2 Introduction to Data-Flow Analysis
## 9.3 Foundations of Data-Flow Analysis  
## 9.4 Constant Propagation  
## 9.5 Partial-Redundancy Elimination
## 9.6 Loops in Flow Graphs
## 9.7 Region-Based Analysis
## 9.8 Symbolic Analysis
## 9.9 Summary of Chapter 9
## 9.10 References for Chapter 9

- 1 Allen, F. E., **Program optimization**, Annual Review in Automatic Programming 5 (1969), pp. 239-307.
- 2 Allen, F. E., **Control flow analysis**, ACM Sigplan Notices 5:7 (1970), pp. 1-19.
- 3 Cocke, J., **Global common subexpression elimination**, ACM SIGPLAN Notices 5:7 (1970), pp. 20-24.
- 4 Cocke, J. and J. T. Schwartz, **Programming Languages and Their Compilers: Preliminary Notes**, Courant Institute of Mathematical Sciences, New York Univ., New York, 1970.
- 5 Cousot, P. and R. Cousot, **Abstract interpretation: a unied lattice model for static analysis of programs by construction or approximation of fixpoints**, Fourth ACM Symposium on Principles of Programming Languages (1977), pp. 238-252.
- 6 Cytron, R., J. Ferrante, B. K. Rosen, M. N. Wegman, and F. K. Zadeck, **Efficiently computing static single assignment form and the control dependence graph**, ACM Transactions on Programming Languages and Systems 13:4 (1991), pp. 451-490.
- 7 Ershov, A. P., **Alpha | an automatic programming system of high efficiency**, J. ACM 13:1 (1966), pp. 17-24.
- 8 Gear, C. W., **High speed compilation of ecient ob ject code**, Comm. ACM 8:8 (1965), pp. 483-488.
- 9 Hecht, M. S. and J. D. Ullman, **Flow graph reducibility**, SIAM J. Computing 1 (1972), pp. 188-202.
- 10 Hecht, M. S. and J. D. Ullman, **Characterizations of reducible flow graphs**, J. ACM 21 (1974), pp. 367-375.
- 11 Kam, J. B. and J. D. Ullman, **Monotone data flow analysis frameworks**, Acta Informatica 7:3 (1977), pp. 305-318.
- 12 Kasami, T., W. W. Peterson, and N. Tokura, **On the capabilities of while, repeat, and exit statements**, Comm. ACM 16:8 (1973), pp. 503-512.
- 13 Kildall, G., **A unied approach to global program optimization**, ACM Symposium on Principles of Programming Languages (1973), pp. 194-206.
- 14 Knoop, J., **Lazy code motion**, Proc. ACM SIGPLAN 1992 conference on Programming Language Design and Implementation, pp. 224-234.
- 15 Kosara ju, S. R., **Analysis of structured programs**, J. Computer and System Sciences 9:3 (1974), pp. 232-255.
- 16 Lowry, E. S. and C. W. Medlock, **Object code optimization**, Comm. ACM 12:1 (1969), pp. 13-22.
- 17 Morel, E. and C. Renvoise, **Global optimization by suppression of partial redundancies**, Comm. ACM 22 (1979), pp. 96-103.
- 18 Prosser, R. T., **Application of boolean matrices to the analysis of flow diagrams**, AFIPS Eastern Joint Computer Conference (1959), Spartan Books, Baltimore MD, pp. 133-138.
- 19 Ullman, J. D., **Fast algorithms for the elimination of common subexpressions**, Acta Informatica 2 (1973), pp. 191-213.
- 20 Vyssotsky, V. and P. Wegner, **A graph theoretical Fortran source language analyzer**, unpublished technical report, Bell Laboratories, Murray Hill NJ, 1963.
- 21 Wulf, W. A., R. K. Johnson, C. B. Weinstock, S. O. Hobbs, and C. M. Geschke, **The Design of an Optimizing Compiler**, Elsevier, New York, 1975.
# 10 Instruction-Level Parallelism
## 10.1 Processor Architectures
## 10.2 Code-Scheduling Constraints
## 10.3 Basic-Block Scheduling
## 10.4 Global Code Scheduling
## 10.5 Software Pipelining
## 10.6 Summary of Chapter 10  
## 10.7 References for Chapter 10

- 1 Bernstein, D. and M. Rodeh, **Global instruction scheduling for superscalar machines**, Proc. ACM SIGPLAN 1991 Conference on Programming Language Design and Implementation, pp. 241-255.
- 2 Dasgupta, S., **The organization of microprogram stores**, Computing Surveys 11:1 (1979), pp. 39-65.
- 3 Fisher, J. A., **Trace scheduling: a technique for global microcode compaction**, IEEE Trans. on Computers C-30:7 (1981), pp. 478-490.
- 4 Gross, T. R. and Hennessy, J. L., **Optimizing delayed branches**, Proc. 15th Annual Workshop on Microprogramming (1982), pp. 114-120.
- 5 Hennessy, J. L. and D. A. Patterson, **Computer Architecture: A Quantitative Approach**, Third Edition, Morgan Kaufman, San Francisco, 2003.
- 6 Kuck, D., Y. Muraoka, and S. Chen, **On the number of operations simultaneously executable in Fortran-like programs and their resulting speedup**, IEEE Transactions on Computers C-21:12 (1972), pp. 1293-1310
- 7 Lam, M. S., **Software pipelining: an eective scheduling technique for VLIW machines**, Proc. ACM SIGPLAN 1988 Conference on Programming Language Design and Implementation, pp. 318-328.
- 8 Lamport, L., **The parallel execution of DO loops**, Comm. ACM 17:2 (1974), pp. 83-93.
- 9 Patel, J. H. and E. S. Davidson, **Improving the throughput of a pipeline by insertion of delays**, Proc. Third Annual Symposium on Computer Architecture (1976), pp. 159-164.
- 10 Rau, B. R. and C. D. Glaeser, **Some scheduling techniques and an easily schedulable horizontal architecture for high performance scientic computing**, Proc. 14th Annual Workshop on Microprogramming (1981), pp. 183-198.
- 11 Tokoro, M., E. Tamura, and T. Takizuka, **Optimization of microprograms**, IEEE Trans. on Computers C-30:7 (1981), pp. 491-504.
- 12 Wood, G., **Global optimization of microprograms through modular control constructs**, Proc. 12th Annual Workshop in Microprogramming (1979), pp. 1-6.
# 11 Optimizing for Parallelism and Locality
## 11.1 Basic Concepts
## 11.2 Matrix Multiply: An In-Depth Example
## 11.3 Iteration Spaces
## 11.4 Affine Array Indexes  
## 11.5 Data Reuse
## 11.6 Array Data-Dependence Analysis
## 11.7 Finding Synchronization-Free Parallelism
## 11.8 Synchronization Between Parallel Loops
## 11.9 Pipelining
## 11.10 Locality Optimizations
## 11.11 Other Uses of Affine Transforms  
## 11.12 Summary of Chapter 11
## 11.13 References for Chapter 11

- 1 Abu-Sufah, W., D. J. Kuck, and D. H. Lawrie, **On the performance enhancement of paging systems through program analysis and transformations**, IEEE Trans. on Computing C-30:5 (1981), pp. 341-356.
- 2 Allen, F. E., M. Burke, P. Charles, R. Cytron, and J. Ferrante, **An overview of the PTRAN analysis system for multiprocessing**, J. Paral lel and Distributed Computing 5:5 (1988), pp. 617-640.
- 3 Allen, F. E. and J. Cocke, **A Catalogue of optimizing transformations**, in Design and Optimization of Compilers (R. Rustin, ed.), pp. 1-30, Prentice-Hall, 1972.
- 4 Allen, R. and K. Kennedy, **Automatic translation of Fortran programs to vector form**, ACM Transactions on Programming Languages and Systems 9:4 (1987), pp. 491-542.
- 5 Banerjee, U., **Data Dependence in Ordinary Programs**, Master's thesis, Department of Computer Science, University of Illinois Urbana-Champaign, 1976.
- 6 Banerjee, U., **Speedup of Ordinary Programs**, Ph.D. thesis, Department of Computer Science, University of Illinois Urbana-Champaign, 1979.
- 7 Dantzig, G. and B. C. Eaves, **Fourier-Motzkin elimination and its dual**, J. Combinatorial Theory, A(14) (1973), pp. 288-297.
- 8 Feautrier, P., **Some efficient solutions to the affine scheduling problem: I. One-dimensional time**, International J. Paral lel Programming 21:5 (1992), pp. 313-348,
- 9 Hennessy, J. L. and D. A. Patterson, **Computer Architecture: A Quantitative Approach**, Third Edition, Morgan Kaufman, San Francisco, 2003.
- 10 Kuck, D., Y. Muraoka, and S. Chen, **On the number of operations simultaneously executable in Fortran-like programs and their resulting speedup**, IEEE Transactions on Computers C-21:12 (1972), pp. 1293-1310
- 11 Kung, H. T. and C. E. Leiserson, **Systolic arrays (for VLSI)**, in Du, I. S. and G. W. Stewart (eds.), Sparse Matrix Proceedings pp. 256-282. Society for Industrial and Applied Mathematics, 1978.
- 12 Lam, M. S., E. E. Rothberg, and M. E. Wolf, **The cache performance and optimization of blocked algorithms**, Proc. Sixth International Conference on Architectural Support for Programming Languages and Operating Systems (1991), pp. 63-74.
- 13 Lamport, L., **The parallel execution of DO loops**, Comm. ACM 17:2 (1974), pp. 83-93.
- 14 Lim, A. W., G. I. Cheong, and M. S. Lam, **An ane partitioning algorithm to maximize parallelism and minimize communication**, Proc. 13th International Conference on Supercomputing (1999), pp. 228-237.
- 15 Lim, A. W. and M. S. Lam, **Maximizing parallelism and minimizing synchronization with ane transforms**, Proc. 24th ACM SIGPLAN-SIGACT Symposium on Principles of Programming Languages (1997), pp. 201-214.
- 16 Lim, A. W., S.-W. Liao, and M. S. Lam, **Blocking and array contraction across arbitrarily nested loops using ane partitioning**, Proc. ACM SIGPLAN Symposium on Principles and Practice of Paral lel Programming (2001), pp. 103-112.
- 17 Loveman. D. B., **Program improvement by source-to-source transformation**, J. ACM 24:1 (1977), pp. 121-145.
- 18 Maydan, D. E., J. L. Hennessy, and M. S. Lam, **An ecient method for exact dependence analysis**, Proc. ACM SIGPLAN 1991 Conference on Programming Language Design and Implementation, pp. 1-14.
- 19 McKeller, A. C. and E. G. Coman, **The organization of matrices and matrix operations in a paged multiprogramming environment**, Comm. ACM, 12:3 (1969), pp. 153-165.
- 20 Mowry, T. C., M. S. Lam, and A. Gupta, **Design and evaluation of a compiler algorithm for prefetching**, Proc. Fifth International Conference on Architectural Support for Programming Languages and Operating Systems (1992), pp. 62-73.
- 21 Padua, D. A. and M. J. Wolfe, **Advanced compiler optimizations for supercomputers**, Comm. ACM, 29:12 (1986), pp. 1184-1201.
- 22 Portereld, A., **Software Methods for Improving Cache Performance on Supercomputer Applications**, Ph.D. Thesis, Department of Computer Science, Rice University, 1989.
- 23 Pugh, W. and D. Wonnacott, **Eliminating false positives using the omega test**, Proc. ACM SIGPLAN 1992 Conference on Programming Language Design and Implementation, pp. 140-151.
- 24 Sarkar, V. and G. Gao, **Optimization of array accesses by collective loop transformations**, Proc. 5th International Conference on Supercomputing (1991), pp. 194-205.
- 25 R. Shostak, **Deciding linear inequalities by computing loop residues**, J. ACM, 28:4 (1981), pp. 769-779.
- 26 Towle, R. A., **Control and Data Dependence for Program Transformation**, Ph.D. thesis, Department of Computer Science, University of Illinois Urbana-Champaign, 1976.
- 27 Wolf, M. E. and M. S. Lam, **A data locality optimizing algorithm**, Proc. SIGPLAN 1991 Conference on Programming Language Design and Implementation, pp. 30-44.
- 28 Wolfe, M. J., Techniques for Improving the Inherent Paral lelism in Programs, Master's thesis, Department of Computer Science, University of Illinois Urbana-Champaign, 1978.  
# 12 Interprocedural Analysis
## 12.1 Basic Concepts  
## 12.2 Why Interprocedural Analysis?
## 12.3 A Logical Representation of Data Flow  
## 12.4 A Simple Pointer-Analysis Algorithm
## 12.5 Context-Insensitive Interprocedural Analysis
## 12.6 Context-Sensitive Pointer Analysis
## 12.7 Datalog Implementation by BDD's
## 12.8 Summary of Chapter 12
## 12.9 References for Chapter 12

- 1 Allen, F. E., **Interprocedural data flow analysis**, Proc. IFIP Congress 1974 pp. 398-402, North Holland, Amsterdam, 1974.
- 2 Andersen, L., Program Analysis and Specialization for the C Programming Language, Ph.D. thesis, DIKU, Univ. of Copenhagen, Denmark, 1994.
- 3 Avots, D., M. Dalton, V. B. Livshits, and M. S. Lam, **Improving software security with a C pointer analysis**, ICSE 2005: Proc. 27th International Conference on Software Engineering, pp. 332-341.
- 4 Ball, T. and S. K. Ra jamani, **A symbolic model checker for boolean programs**, Proc. SPIN 2000 Workshop on Model Checking of Software, pp. 113-130.
- 5 Ball, T., E. Bounimova, B. Cook, V. Levin, J. Lichtenberg, C. McGarvey, B. Ondrusek, S. Ra jamani, and A. Ustuner, **Thorough static analysis of device drivers**, EuroSys (2006), pp. 73-85.
- 6 Banning, J. P., **An ecient way tond the side eects of procedural calls and the aliases of variables**, Proc. Sixth Annual Symposium on Principles of Programming Languages (1979), pp. 29-41.
- 7 Barth, J. M., **A practical interprocedural data flow analysis algorithm**, Comm. ACM 21:9 (1978), pp. 724-736.
- 8 Berndl, M., O. Lohtak, F. Qian, L. Hendren, and N. Umanee, **Pointsto analysis using BDD's**, Proc. ACM SIGPLAN 2003 Conference on Programming Language Design and Implementation, pp. 103-114.
- 9 Bryant, R. E., **Graph-based algorithms for Boolean function manipulation**, IEEE Trans. on Computers C-35:8 (1986), pp. 677-691.
- 10 Bush, W. R., J. D. Pincus, and D. J. Siela, **A static analyzer fornding dynamic programming errors**, Software-Practice and Experience, 30:7 (2000), pp. 775-802.
- 11 Callahan, D., K. D. Cooper, K. Kennedy, and L. Torczon, **Interprocedural constant propagation**, Proc. SIGPLAN 1986 Symposium on Compiler Construction, SIGPLAN Notices, 21:7 (1986), pp. 152-161.
- 12 Engler, D., B. Chelf, A. Chou, and S. Hallem, **Checking system rules using system-specic, programmer-written compiler extensions**, Proc. Sixth USENIX Conference on Operating Systems Design and Implementation (2000). pp. 1-16.
- 13 Emami, M., R. Ghiya, and L. J. Hendren, **Context-sensitive interprocedural points-to analysis in the presence of function pointers**, Proc. SIGPLAN Conference on Programming Language Design and Implementation (1994), pp. 224-256.
- 14 F ahndrich, M., J. Rehof, and M. Das, **Scalable context-sensitive flow analysis using instantiation constraints**, Proc. SIGPLAN Conference on Programming Language Design and Implementation (2000), pp. 253-263.
- 15 Heintze, N. and O. Tardieu, **"Ultra-fast aliasing analysis using CLA: a million lines of C code in a second**, Proc. of the SIGPLAN Conference on Programming Language Design and Implementation (2001), pp. 254-263.
- 16 Lam, M. S., J. Whaley, V. B. Livshits, M. C. Martin, D. Avots, M. Carbin, and C. Unkel, **Context-sensitive program analysis as database queries**, Proc. 2005 ACM Symposium on Principles of Database Systems, pp. 1-12.
- 17 Livshits, V. B. and M. S. Lam, **Finding security vulnerabilities in Java applications using static analysis**, Proc. 14th USENIX Security Symposium (2005), pp. 271-286.
- 18 Milanova, A., A. Rountev, and B. G. Ryder, **Parameterized ob ject sensitivity for points-to and side-eect analyses for Java**, Proc. 2002 ACM SIGSOFT International Symposium on Software Testing and Analysis, pp. 1-11.
- 19 Rinard, M., C. Cadar, D. Dumitran, D. Roy, and T. Leu, **A dynamic technique for eliminating buffer overflow vulnerabilities (and other memory errors)**, Proc. 2004 Annual Computer Security Applications Conference, pp. 82-90.
- 20 Ruwase, O. and M. S. Lam, **A practical dynamic buffer overflow detector**, Proc. 11th Annual Network and Distributed System Security Symposium (2004), pp. 159-169.
- 21 Sharir, M. and A. Pnueli, **Two approaches to interprocedural data flow analysis**, in S. Muchnick and N. Jones (eds.) Program Flow Analysis: Theory and Applications, Chapter 7, pp. 189-234. Prentice-Hall, Upper Saddle River NJ, 1981.
- 22 Steensgaard, B., **Points-to analysis in linear time**, Twenty-Third ACM Symposium on Principles of Programming Languages (1996).
- 23 Ullman, J. D. and J. Widom, **A First Course in Database Systems**, Prentice-Hall, Upper Saddle River NJ, 2002.
- 24 Whaley, J. and M. S. Lam, **Cloning-based context-sensitive pointer alias analysis using binary decision diagrams**, Proc. ACM SIGPLAN 2004 Conference on Programming Language Design and Implementation, pp.131-144.
- 25 Zhu, J., **Symbolic Pointer Analysis**, Proc. International Conference in Computer-Aided Design (2002), pp. 150-157.

# 13 A  A Complete Front End
## 13.1 A.1 The Source Language

```
program   -> block
block     -> { decls stmts }
decls     -> decls decl | ε
decl      -> type `id` ;
type      -> type [ `num` ] | `basic`         # basic represents basic types
stmts     -> stmts stmt | ε

stmt      -> loc = bool ;
          | 'if' ( bool ) stmt
          | 'if' ( bool ) stmt 'else' stmt
          | 'while' ( bool ) stmt
          | 'do' stmt 'while' ( bool ) ;
          | 'break' ;
          | block
loc       -> loc [ bool ] | `id`

bool      -> bool || join | join
join      -> join && equality | equality
equality  -> equality == rel | equality != rel | rel
rel       -> expr < expr | expr <= expr | expre >= expr | expr > expr | expr
expr      -> expr + term | expr - term | term
term      -> term * unary | term / unary | unary
unary     -> ! unary | - unary | factor
factor    -> ( bool ) | loc | `num` | `real` | 'true' | 'false'
```

- `''`: literal,
- ``` `` ```: lexer identifier.


## 13.2 A.2 Main
## 13.3 A.3 Lexical Analyzer
## 13.4 A.4 Symbol Tables and Types
## 13.5 A.5 Intermediate Code for Expressions  
## 13.6 A.6 Jumping Code for Boolean Expressions
## 13.7 A.7 Intermediate Code for Statements
## 13.8 A.8 Parser  
## 13.9 A.9 Creating the Front End

# 14 B Finding Linearly Independent Solutions
