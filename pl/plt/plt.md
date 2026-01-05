# Programming Language Theory

# Reading List

## Google AI Mode

A strong reading list for learning Programming Language Theory (PLT) often progresses from foundational concepts to more advanced topics like type theory and semantics. Key books consistently recommended by academics and practitioners include: 

Foundational Texts
- **Structure and Interpretation of Computer Programs (SICP)** by Harold Abelson, Gerald Jay Sussman, and Julie Sussman is a classic introduction using Scheme.
- **Essentials of Programming Languages (EOPL)** by Daniel P. Friedman and Mitchell Wand teaches concepts through interpreters.
- **Programming Languages: Application and Interpretation** by Shriram Krishnamurthi is a free online book also using an interpreter-based approach. 

Core PLT and Semantics
- **Types and Programming Languages (TAPL)** by Benjamin C. Pierce is a standard text on type systems.
- **The Formal Semantics of Programming Languages: An Introduction** by Glynn Winskel covers mathematical techniques for reasoning about languages.
- **Semantics with Applications: An Appetizer** by Hanne Riis Nielson and Flemming Nielson is another well-regarded book on formal semantics.
- **Practical Foundations for Programming Languages (PFPL)** by Robert Harper offers a rigorous, modern foundation. 

Advanced and Specialized Topics
- **Advanced Topics in Types and Programming Languages (ATTAPL)** edited by Benjamin C. Pierce is a follow-up to TAPL.
- **Programming Language Foundations in Agda (PLFA)** by Philip Wadler and Wen Kokke uses the Agda proof assistant.
- **Software Foundations (SF)** by Benjamin C. Pierce et al. is an online series using Coq for logic, semantics, and formal verification.
- **Compilers: Principles, Techniques, and Tools** (The **Dragon Book**) is a key reference for applying PLT concepts in compilers. 

For self-study, building intuition through implementation (like EOPL/PLAI) before moving to more theoretical texts (like TAPL) is often suggested.

## Quora
* [What are good books for learning program language theory?](https://www.quora.com/What-are-good-books-for-learning-program-language-theory)
  * Benjamin Pierce's **Types and Programming Languages** and the follow-up **Advanced Topics in Types and Programming Languages**
  * **Practical Foundations for Programming Languages**
  * **Programming Language Pragmatics**, Third Edition: Michael L. Scott: 9780123745149

A compact, structured reading list for learning programming language theory (PLT), organized by level and topic, with short notes on why each book is useful and what prerequisites help.
 
Foundational / introductory
- **Types and Programming Languages** — Benjamin C. Pierce (2002)  
  - Comprehensive introduction to type systems, operational semantics, lambda calculus. Rigorous but accessible; many universities use it as a first PLT text.
- **Semantics with Applications: An Appetizer** — Hanne Riis Nielson &amp; Flemming Nielson (2015)  
  - Lightweight, practical coverage of operational and denotational semantics and static analysis; good bridge from programming to formal methods.
- **Programming Language Pragmatics** — Michael L. Scott (4th ed., 2015)  
  - Broader view: language design, implementation, parsing, runtime systems. Less formal but excellent for contextual understanding.

Core theory and type systems
- **Practical Foundations for Programming Languages** — Robert Harper (2016)  
  - Modern, modular treatment of type theory, operational semantics, modules, polymorphism. Formal and up-to-date; good after Pierce.
- **Advanced Topics in Types and Programming Languages** — Benjamin C. Pierce (ed.) (2005)  
  - Edited collection of advanced essays: subtyping, concurrency, dependent types, advanced type systems.
- **Types and Programming Languages: The Art of Type Systems** (lecture notes/variants cited) — for targeted study of polymorphism, type inference.

Lambda calculus, semantics, and logic
- **The Lambda Calculus: Its Syntax and Semantics** — Henk Barendregt (1984, corrected ed.)  
  - Definitive technical reference on lambda calculus; dense but essential for deep work.
- **Semantics of Programming Languages: Structures and Techniques** — Carl A. Gunter (1992)  
  - Rigorous presentation of denotational and operational semantics, domain theory.
- **Domain Theory** — Samson Abramsky &amp; Achim Jung (in Handbook of Logic in Computer Science, 1994)  
  - Concise yet authoritative introduction to domain theory foundations used in semantics.

Type theory and dependently typed programming
- **Homotopy Type Theory: Univalent Foundations of Mathematics** — The Univalent Foundations Program (2013)  
  - If interested in modern dependent type theory and foundations; high-level and research-oriented.
- **Type Theory and Formal Proof** — Rob Nederpelt &amp; Herman Geuvers (2014)  
  - Accessible introduction to type theory, proofs as programs, and proof assistants.
- **Certified Programming with Dependent Types** — Adam Chlipala (CPDT) (2013)  
  - Practical, Coq-focused path from basic theory to verified programs.

Programming language implementation
- **Modern Compiler Implementation in ML/Java/C** — Andrew W. Appel (3rd ed.)  
  - Practical compilation techniques with clear connections to semantics and type checking.
- **Compilers: Principles, Techniques, and Tools** — Aho, Lam, Sethi, Ullman (2nd ed., aka Dragon Book)  
  - Classic compiler construction reference; useful when combined with PL semantics.

Concurrency, effects, and advanced topics
- **Communicating Sequential Processes** — C.A.R. Hoare (1985) and related texts for CSP  
  - Foundational for concurrency models.
- **Programming Languages and Systems** — Papers/edited volumes such as POPL/POPL proceedings and the **Advanced Topics** collection for contemporary research topics (grad-level reading).

Practical/bridge texts and resources
- **Software Foundations** — Benjamin Pierce et al. (online, freely available)  
  - Series of Coq-based volumes covering PL foundations, semantics, and verification. Great for hands-on formalization.
- Lecture notes and MOOC courses (e.g., MIT, Cornell, UPenn) — often current, concise, and aligned with research trends.

Recommended progression (typical)
1. Start with Pierce (**Types and Programming Languages**) + **Programming Language Pragmatics** for context.  
2. Work through operational semantics and simple proofs using **Semantics with Applications** or course notes.  
3. Study Harper for deeper type-theory structure and polymorphism.  
4. Read Barendregt and domain-theory material for advanced semantics.  
5. Use Appel + Dragon Book when moving into implementation.  
6. Explore dependently typed texts (Chlipala, Software Foundations) if pursuing verification or modern type theory.

Prerequisites and study tips
- Comfortable with discrete math, logic, and proof techniques (induction, structural recursion).  
- Familiarity with lambda calculus and functional programming (OCaml/Haskell) accelerates learning.  
- Work through exercises and formalizations (Coq/Agda) to internalize semantics and type proofs.  
- Complement books with recent POPL/ICFP papers to see active research directions.

Notes on currency
- Core theory in these texts remains valid; for the newest developments (e.g., gradual typing, refinement types, session types, capabilities, effect systems) consult recent conference papers (POPL, ICFP, PLDI) and surveys from 2020–2024.

## Goodreads
* [Programming Languages Theory Books](https://www.goodreads.com/shelf/show/programming-languages-theory)

# See Also
* [Programming language theory - wikipedia](https://en.wikipedia.org/wiki/Programming_language_theory)
* [The next 700 programming languages](https://doi.org/10.1145/365230.365257) - 1966
* [Programming Language Theory - GitHub](https://github.com/steshaw/plt): Programming Language Theory λΠ
* [Programming Language Research - GitHub](https://github.com/imteekay/programming-language-research): Programming Language Research, Applied PLT & Compilers