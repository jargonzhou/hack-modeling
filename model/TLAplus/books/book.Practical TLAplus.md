# Practical TLA+
* Hillel Wayne. **Practical TLA+: Planning Driven Development**. Apress: 2018.
* https://github.com/Apress/practical-tla-plus

- Part I: The Semantics of TLA+ and PlusCal: 1-6
- Part II: Applying TLA+: 7-11

# Introduction
This is a book about **specification**.

Instead of writing your design in code or plain English, you write it in TLA+'s special notation.
Once you specify your core *assumptions* and *requirements*, it can *explore how that system would evolve over time*, and *whether it actually has the properties you want*.

By leveraging simple math, TLA+ can express concepts much more elegantly and accurately that a programming language can.

Instead of being compiled or interpreted, TLA+ is **checked**.
We use a **model checker**, called **TLC**, to execute every possible behavior of our specification.

With TLA+ we can check that *global properties are preserved*, that *distributed systems are fault-tolerant*, or even that *every behavior of an algorithm eventually terminates with a correct answer*.
**We can cut out bugs before we've written a single line of code.** 
## What This Book Will Teach You
2 benefits to learning TLA+:
1. **model checking**: once you have written a specification in TLA+, you can use the model checker to find any *inconsistencies* in your spec. TLA+ can find bugs that span multiple systems and several nested race conditions.
2. **specify a system** fores you to be *precise* in what you actually want. By unambiguously writing your specification, you understand it better.

challenges: the change of perspective
- how to specify an algorithm?
- how to specify a distributed system?
- how to make the jump from knowing TLA+ in theory to using it in practice, finding actual bugs in actual production systems?
## What This Book Won’t Teach You
- This book will not teach you programming.
- This book is not a comprehensive resource on how to use TLA+. We focus on using **PlusCal**, the main algorithm language that compiles to TLA+.
## Prerequisites
- You should already be an experienced programmer.
- Knowing some logic and math is going to help.
## How This Book Is Structured
2 parts:
- chapter 1-6: semantics of TLA+ and PlusCal.
- chapter 7-11: applications of TLA+.
## Initial Setup
### The Toolbox
To use TLA+, we need the *PlusCal compiler*, the *syntactic checker*, and the *TLC model checker*.

The offical IDE called the *TLA+ Toolbox*.
Create a new module: 'File' - 'Open Spec' - 'Add New Spec'.
### PT
The PT library is a collection of useful operators and definitions that will make learning and using the language easier.

Set up: 'File' - 'Preferences' - 'TLA+ Preferences' - 'TLA+ library path locations'.

# 1 An Example
## 1.1 The Problem
Alice and Bob have accounts at Bankgroup. Each account has 0 or more dollars in it.
*wire* feature: any user can transfer money to any other user.

wire feature's *requirements*:
1. each wire must be between two different people in the bank, and wire at least one dollar.
2. if a wire is successful, the value of the wire is deducted from the sender account and added to the receiver account.
3. if the wire fails, the two accounts are unchanged.
4. a wire may not cause an account to have a negative balance.
5. for scaling reasons, multiple wires may happen simultaneously.
### 1.1.1 Boilerplate
'File' - 'Open Spec' - 'Add New Spec'
> [!example] Create `wire` module/specification
```TLA+ title="wire.tla"
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
begin
    skip;
end algorithm;*)
===============================
```
- `\*` is single line comment, `(* *)` is comment block.
### 1.1.2 Specifying
system states: 
- the set of people with accounts,
- how much money each of them has.

> [!example] Specifying states and invariants in `wire` module
```TLA+ title="wire.tla" {5-14}
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5],
        sender = "alice",
        receiver = "bob",
        amount = 3;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    skip;
end algorithm;*)
===============================
```
- `variables` defines system states.
- `people` is a **set**,  which is an unordered collection of things.
- `acc` is a **function**, which is closer to dictionaries or mappings.
- `NoOverdrafts` is an **invariant**, which is something we want to be true at every state of the system, no matter how it starts or where it ends. If it's false, the specification has an error.
	- `==` is the definition of an **operator**, which is closer to what we normally think of programming functions.
	- `NoOverdrafts` means *for all `p` in the set of `people`, their account must be greater than or equal to 0*.
### 1.1.3 Implementing
> [!example] Implementing `wire` module
```TLA+ title="wire.tla" {17-20}
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5],
        sender = "alice",
        receiver = "bob",
        amount = 3;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] + amount;
end algorithm;*)
===============================
```
- `Withdraw` and `Deposit` are **labels**, they signify that everything inside them happnes in the same moment of time.

We write part of our specification in **PlusCal**, a special language that compiles to pure TLA+.

then perform 'File' - 'Translate PlusCal Algorithm':
```TLA+ title="wire.tla" {22, 59}
---------- MODULE wire --------
EXTENDS Integers
    
(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5],
        sender = "alice",
        receiver = "bob",
        amount = 3;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] + amount;
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "ed73f16c" /\ chksum(tla) = "f067a8a0")
VARIABLES people, acc, sender, receiver, amount, pc

(* define statement *)
NoOverdrafts == \A p \in people: acc[p] >= 0


vars == << people, acc, sender, receiver, amount, pc >>

Init == (* Global variables *)
        /\ people = {"alice", "bob"}
        /\ acc = [p \in people |-> 5]
        /\ sender = "alice"
        /\ receiver = "bob"
        /\ amount = 3
        /\ pc = "Withdraw"

Withdraw == /\ pc = "Withdraw"
            /\ acc' = [acc EXCEPT ![sender] = acc[sender] - amount]
            /\ pc' = "Deposit"
            /\ UNCHANGED << people, sender, receiver, amount >>

Deposit == /\ pc = "Deposit"
           /\ acc' = [acc EXCEPT ![receiver] = acc[receiver] + amount]
           /\ pc' = "Done"
           /\ UNCHANGED << people, sender, receiver, amount >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Withdraw \/ Deposit
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
===============================
```

### 1.1.4 Verifying
To check that this spec works, we need to create a **model** to check it.
The model is like the *simulation* we want to run.
Different models may set up different initial conditions and check for different things.

Create the model: 'TLC Model Checker' - 'New Model'.
select 'Model Overview' - 'What is the behavior spec?' - 'Temporal formula' to `Spec`.
add 'Model Overview' - 'What to check?' - 'Invariants' `NoOverdrafts`, then run the model.

result:
```TLA+ nums
(* Model Checking Results *)
StatesFound == 4
DistinctStates == 3

(* TLC Errors *)
Error == "no"
```

TLC did an exhaustive search across the entier state space.
### 1.1.5 Initial Conditions
> [!example] Initial Conditions in wire.tla
```TLA+ title="wire.tla" {10}
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5],
        sender = "alice",
        receiver = "bob",
        amount \in 1..6;

define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

begin
    Withdraw:
        acc[sender] := acc[sender] - amount;
    Deposit:
        acc[receiver] := acc[receiver] + amount;
end algorithm;*)
===============================
```
- `amount \in 1..6` expands the set of possible initial states for specification.

result:
```TLA+ {25, 28}
(* Model Checking Results *)
StatesFound == 22
DistinctStates == 17

(* TLC Errors *)
Error == "Invariant NoOverdrafts is violated."
ErrorTrace == 
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
acc |-> [alice |-> 5, bob |-> 5],
amount |-> 6,
pc |-> "Withdraw",
people |-> {"alice", "bob"},
receiver |-> "bob",
sender |-> "alice"
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Withdraw",
   location |-> "line 42, col 13 to line 45, col 63 of module wire"
 ],
acc |-> [alice |-> -1, bob |-> 5],
amount |-> 6,
pc |-> "Deposit",
people |-> {"alice", "bob"},
receiver |-> "bob",
sender |-> "alice"
]
>>
```

## 1.2 Multiple Processes
In PlusCal, each algorithm happening simultaneously belongs to its own **process**.
Each process can have its own *code* and its own *local variables*.

> [!example] Simultaneous wires
```TLA+ {13, 25}
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5];
        
define
    NoOverdrafts == \A p \in people: acc[p] >= 0
end define;

process Wire \in 1..2
    variables
        sender = "alice",
        receiver = "bob",
        amount \in 1..acc[sender];
begin
    CheckAndWithdraw:
        if amount <= acc[sender] then
                acc[sender] := acc[sender] - amount;
            Deposit:
                acc[receiver] := acc[receiver] + amount;
        end if; 
end process;

end algorithm;*)
===============================
```

```TLA+ nums
(* Model Checking Results *)
StatesFound == 332
DistinctStates == 222

(* TLC Errors *)
Error == "no"
```

## 1.3 Temporal Properties
While simple invariants check that every state of the specification is valid, **Temporal Properties** check that every possible *lifetime* of the algorithm, from start to finish, obeys something that *relates different states* in the sequence to each other.

> [!example] Temporal property: the total final value of the account is equal to the total starting value
```TLA+ {11}
---------- MODULE wire --------
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [p \in people |-> 5];
        
define
    NoOverdrafts == \A p \in people: acc[p] >= 0
    EventuallyConsistent == <>[](acc["alice"] + acc["bob"] = 10)
end define;

process Wire \in 1..2
    variables
        sender = "alice",
        receiver = "bob",
        amount \in 1..acc[sender];
begin
    CheckAndWithdraw:
        if amount <= acc[sender] then
                acc[sender] := acc[sender] - amount;
            Deposit:
                acc[receiver] := acc[receiver] + amount;
        end if; 
end process;

end algorithm;*)
===============================
```

- `<>[]` is the *eventually-always* operator. `EventuallyConsistent` means the sum of the two account eventually always equal to 10 dollars.

Add `EventuallyConsistent` to 'Model Overview' - 'What to check?' - 'Properties'.

result:
```TLA+ {28, 30, 41, 43, 54, 56, 61}
(* Model Checking Results *)
StatesFound == 332
DistinctStates == 222

(* TLC Errors *)
Error == "Temporal properties were violated."
ErrorTrace ==     
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
acc |-> [alice |-> 5, bob |-> 5],
amount |-> <<1, 1>>,
pc |-> <<"CheckAndWithdraw", "CheckAndWithdraw">>,
people |-> {"alice", "bob"},
receiver |-> <<"bob", "bob">>,
sender |-> <<"alice", "alice">>
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "CheckAndWithdraw",
   location |-> "line 54, col 27 to line 60, col 77 of module wire"
 ],
acc |-> [alice |-> 4, bob |-> 5],
amount |-> <<1, 1>>,
pc |-> <<"CheckAndWithdraw", "Deposit">>,
people |-> {"alice", "bob"},
receiver |-> <<"bob", "bob">>,
sender |-> <<"alice", "alice">>
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "CheckAndWithdraw",
   location |-> "line 54, col 27 to line 60, col 77 of module wire"
 ],
acc |-> [alice |-> 3, bob |-> 5],
amount |-> <<1, 1>>,
pc |-> <<"Deposit", "Deposit">>,
people |-> {"alice", "bob"},
receiver |-> <<"bob", "bob">>,
sender |-> <<"alice", "alice">>
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Deposit",
   location |-> "line 62, col 18 to line 65, col 68 of module wire"
 ],
acc |-> [alice |-> 3, bob |-> 6],
amount |-> <<1, 1>>,
pc |-> <<"Deposit", "Done">>,
people |-> {"alice", "bob"},
receiver |-> <<"bob", "bob">>,
sender |-> <<"alice", "alice">>
],
<Stuttering>
>>
```
   

# 2 PlusCal
## 2.1 Introduction
PlusCal is a language that compiles down to TLA+.
Lamport developed it in 2009 to make TLA+ more accessible to programmers.
## 2.2 Specifications
### 2.2.1 Layout of a Spec
```TLA+ 
---- MODULE wire ----
EXTENDS Integers

(*--algorithm wire
    variables
        people = {"alice", "bob"},
        acc = [alice |-> 5, bob |-> 5];

begin            \* put the algorithm itself
    skip;
end algorithm;*)
====
```
- All TLA+ specs must start with at least 4 `-` on each side of the `MODULE` and 4 `=` at the end.
- module name must be the same as the filename.
- `EXTENDS` is the import keyword, here we import the `Integers` module.
- `\*` starts a line comment, `(* ... *)` is a block comment.
- PlusCal specs are placed in the comment, are started with `--algorithm <name>`, and closed with `end algorithm`. The name of the algorithm does not have to match the filename.
- `variables` defines variables in the algorithm. Variables are separated by `,` or `;`.
### 2.2.2 Expressions
Everything in an expression is either a value (like `{TRUE}`), or an **operator** (like `+`).
Checking an expression will also evaluate the spec:
- not run : 'Model Overview' - 'What is the behavior Spec?' - 'No Behavior Spec'.
- 'Model Checking Results' - 'Evaluate Constant Expression'.
### 2.2.3 Values
4 kinds of basic values in TLA+:
- **strings**: must be written in double quotes, example: `"PlusCal"`.
- **integers**: floats are not supported.
- **booleans**: `TRUE`, `FALSE`.
- **model values**: see chapter 4.
```TLA+
x = y                        \* Equals
x /= y                       \* Not Equals
x ## 2.y
x /\ y                       \* And
x \/ y                       \* or
x := y                       \* Assignment (PlusCal only)
~x                           \* Not
```
```TLA+
EXTENDS Integers

x + y                        \* arithmetic
x - y
x * y
x \div y                     \* integer division
x % y

a..b                         \* range operator: the set {a, a+1, a+2, ..., b}
```

4 kinds of constructed types in TLA+:
- **sets**: unordered collections of elements. all elements in the set must have the *same* type. example: `{"a", "b", "c"}`.
```TLA+
x \in set                    \* is element of set
x \notin set                 \* is not element of set
~(x \in set)
set1 \subseteq set2          \* is subset of set
set1 \union set2             \* set union
set1 \intersect set2         \* set intersection
set1 \ set2                  \* set difference
Cardinality(set)             \* number of elements in set
                             \* require EXTENDS FiniteSets

(* set transformation *)
{x \in set: conditional}     \* filter sets
{expression: x \in set}      \* map sets
```
- **tuples** / **sequences**: ordered collections of elements, with the index starting at **1**. They are specified with `<<` and `>>`, and its elements do *not* need to be the same type. example: `tup = <<"a", {1, 2}>>`, then `tup[1] = "a"` and `tup[2] = {1, 2}`. 
```TLA+
EXTENDS Sequences

Head(sequence)               \* head
Tail(seq)                    \* tail
Append(seq, x)               \* append
seq1 \o seq2                 \* combine
Len(seq)                     \* length of sequence
```
> [!quote] tuple v.s. sequence
> By convention, we use *tuple* when we don't expect to use sequence operators on it or change its lenght, and we use *sequence* if we do.
- **structures**: map strings to values, write as `[ key1 |-> val1, key2 |-> val2 ]`, the values do not have to be the same type. get the value with `struct.key`. example: `[a |-> 1, b |-> <<1, {}>>].b` returns `<<1, {}>>`.
- **functions**: see chapter 3.
### 2.2.4 PlusCal Algorithm Body
- **Assignment**: assign an existing variable to a different value. done with `:=`.
- `assert`: an assertion. 
adding assertions is one common way we test *invariants*: the assertion checks that in that step a given expression holds, if it fails the spec broke the invariant.
```TLA+
EXTENDS TLC

assert TRUE  \* do nothing 
assert FALSE \* raise an error
```
- `skip`: a no-op.
- `if`: the only conditional in PlusCal.
```TLA+
if condition1 then
    body
elsif condition2 then
    body
else
    body
end if;
```
- `while`: the only form of loops in PlusCal.
```TLA+
while condition do
    body
end while;
```
- Macros
clean up sepcs, add **macros** before the `begin`:
```TLA+
macro name(arg1, arg2) begin
    \* assignments
    \* assertions
    \* if statements
end macro;

begin
    name(x, y);
end algorithm;
```
*can*: place assignments, assertions, `if` statements in macros; refer to outside values in macros, assign to outside variables in macros.
*cannot*: place `while` loops in macros; assign to any variable more than once.
### 2.2.5 Example
> [!example]- Design a sorting machine `recycler`
>    Requirement:
>    A machine that sorts material into *recycle* and *trash*.
>    It has finite space for both recycle and trash.
>    Items with a specified size and type come in, one at a time.
> 
> The machine sorts items according to the rules:
>  - if the item is labeled as *recycle* and it is under the reamining capacity for the recycling bin, the item goes into recycle.
>   - if the item labeled as *trash* **OR** the item is labeled as *recycle* and there is not enough recycling capacity **AND** there is sufficient capacity in the trash bin, the item goes into trash.
>   - otherwise, it's dropped on the floor.
> ```TLA+
> ---------- MODULE recycler ----------
> EXTENDS Sequences, Integers, TLC, FiniteSets
> 
> (*--algorithm recycler
> variables
>     capacity = [trash |-> 10, recycle |-> 10],
>     bins = [trash |-> {}, recycle |-> {}],
>     count = [trash |-> 0, recycle |-> 0],
>     items = <<
>         [type |-> "recycle", size |-> 5],
>         [type |-> "trash", size |-> 5],
>         [type |-> "recycle", size |-> 4],
>         [type |-> "recycle", size |-> 3]
>     >>,
>     curr = ""; \* helper: current item
> 
> macro add_item(type) begin
>     bins[type] := bins[type] \union {curr};
>     capacity[type] := capacity[type] - curr.size;
>     count[type] := count[type] + 1;
> end macro;
> 
> begin
>     while items /= <<>> do
>         curr := Head(items);
>         items := Tail(items);
>         if curr.type = "recycle" /\ curr.size < capacity.recycle then
>             add_item("recycle");
>         elsif curr.size < capacity.trash then
>             add_item("trash");
>         end if;
>     end while;
>     
>     assert capacity.trash >= 0 /\ capacity.recycle >= 0;
>     assert Cardinality(bins.trash) = count.trash;
>     assert Cardinality(bins.recycle) = count.recycle;
> end algorithm; *)
> ===============================
> ```
>
> result:
> ```TLA+ linenums="1"
> (* Model Checking Results *)
> StatesFound == 7
> DistinctStates == 6
> 
> (* TLC Errors *)
> Error == "no"
> ```

## 2.3 Complex Behaviors
Ways to check an entire space of setups and runtime occurrences.
### 2.3.1 Multiple Starting States
We initialize variables with `=`, but we can also initialize them with `\in`.
`x \in set` means *variable `x` is any possible element in the set*.
> [!example] multiple starting states  
```TLA+ {2}
    (*--algorithm in
    variables x \in 1..3;
    begin
        assert x <= 2;
    end algorithm; *)
```
   
TLC will first try running the whole algorithm with `x = 1`, then `x = 2`, then finally `x = 3`, which fails.
arbitrary number, boolean, set, tuple/sequence, structure:
```TLA+
1..3                          \* {1, 2, 3}
BOOLEAN                       \* for {TRUE, FALSE}
SUBSET set                    \* power set
UNION {set1, set2, ..., setn} \* set1 \union set2 \union ... \union \setn
set1 \X set2                  \* the set of all tuples where the first element is in set1,
                              \* the second is in set2
                              \* \X is not associative
[key: set]                    \* a set of structure where the value of key is some element of set
[key1: set, key2: {value}]    \* one key is always a specific value
```

All of these can be freely mixed and matched. example `variable x \in [key: (set1 \x set2)]` means *`x` is a structure where the value of key is some pair of elements, the first being in `set1`, the second being in `set2`*.

> [!example] Sorting machine with multiple starting states
```TLA+ {6-10}
    ---------- MODULE recycler ----------
    EXTENDS Sequences, Integers, TLC
    
    (*--algorithm recycler
    variables
        capacity \in [trash: 1..10, recycle: 1..10],
        bins = [trash |-> <<>>, recycle |-> <<>>],
        count = [trash |-> 0, recycle |-> 0],
        item = [type: {"trash", "recycle"}, size: 1..6],
        items \in item \X item \X item \X item, \* 4 items
        curr = ""; \* helper: current item
    
    macro add_item(type) begin
        bins[type] := Append(bins[type], {curr});
        capacity[type] := capacity[type] - curr.size;
        count[type] := count[type] + 1;
    end macro;
    
    begin
        while items /= <<>> do
            curr := Head(items);
            items := Tail(items);
            if curr.type = "recycle" /\ curr.size < capacity.recycle then
                add_item("recycle");
            elsif curr.size < capacity.trash then
                add_item("trash");
            end if;
        end while;
        
        assert capacity.trash >= 0 /\ capacity.recycle >= 0;
        assert Len(bins.trash) = count.trash;
        assert Len(bins.recycle) = count.recycle;
    end algorithm; *)
    ===============================
```

result:
```TLA+ nums
    (* Model Checking Results *)
    StatesFound == 9323626
    DistinctStates == 7250026
    
    (* TLC Errors *)
    Error == "no"
```
### 2.3.2 Nondeterministic Behavior
Not all behavior is *deterministic*: a request may succeed or fail, a query might return a random result, there might be one of several choices to make.

2 PlusCal construts to simulate nondeterminisim:
- `either`
```TLA+
either
    \* branch 1
or
    \* branch 2
    \* ...
or
    \* branch n
end either;
```
TLC will check all branches simultaneously.
We can place any assignment or PlusCal expression inside of an `either` branch.
If all of the branches are *macro-valid*, we may place an `either` inside of a macro.
- `with`
```TLA+
(* case 1 *)
with var = value do
    \* body
end with;

(* case 2 *)
with var \in set do
    \* body
end with;
```

case 1 just creates a *temporary varaible*.
case 2 is *nondeterministic*.
TLC will check what happens for all possible assignments of `var` to elements of `set`.
If the set is empty, the spec halts until the set is not empty. (For single process apps, this is considered a spec failure.)

No *double-assignments* and no `while` loops can be placed in `with` statements.
We can place `with` statements inside macros.

> [!example] An idealized model of sending messages
> two-trun cycle:
> 1. on the sender's turn, they put a message in transit.
> 2. on the receiver's turn, they either receive a message in transit or do nothing.
>    
> There is a definite order on how the messages are sent and an order in which they are received, they aren't ordered in transit.
```TLA+
    ---------- MODULE telephone ----------
    EXTENDS Sequences, TLC
    
    (*--algorithm telephone
    variables
        to_send = <<1, 2, 3>>,
        received = <<>>,
        in_transit = {},
        can_send = TRUE;
    
    \* WARN: Deadlock reached.
    \* sender depend on reciver to set can_send.
    
    begin
        while Len(received) /= 3 do
            \* send
            if can_send /\ to_send /= <<>> then
                in_transit := in_transit \union {Head(to_send)};
                can_send := FALSE;
                to_send := Tail(to_send);
            end if;
            
            \* receive
            either
                with msg \in in_transit do
                    received := Append(received, msg);
                    in_transit := in_transit \ {msg};
                    \* case: the message is successfully received,
                    \*       but the mechanism that reports it was received fails.
                    either
                        can_send := TRUE;
                    or
                        skip;
                    end either;
                end with;
            or
                skip;
            end either;
        end while;
    end algorithm; *)
    ===============================
```
    
result:
```TLA+ {27, 28, 29, 31, 40, 41, 42, 53}
    (* Model Checking Results *)
    StatesFound == 27
    DistinctStates == 17
    
    (* TLC Errors *)
    Error == "Deadlock reached."
    ErrorTrace == 
    <<
    [
     _TEAction |-> [
       position |-> 1,
       name |-> "Initial predicate",
       location |-> "Unknown location"
     ],
    can_send |-> TRUE,
    in_transit |-> {},
    pc |-> "Lbl_1",
    received |-> <<>>,
    to_send |-> <<1, 2, 3>>
    ],
    [
     _TEAction |-> [
       position |-> 2,
       name |-> "Lbl_1",
       location |-> "line 53, col 10 to line 66, col 30 of module telephone"
     ],
    can_send |-> FALSE,
    in_transit |-> {1},
    pc |-> "Lbl_2",
    received |-> <<>>,
    to_send |-> <<2, 3>>
    ],
    [
     _TEAction |-> [
       position |-> 3,
       name |-> "Lbl_2",
       location |-> "line 68, col 10 to line 76, col 29 of module telephone"
     ],
    can_send |-> FALSE,
    in_transit |-> {},
    pc |-> "Lbl_1",
    received |-> <<1>>,
    to_send |-> <<2, 3>>
    ],
    [
     _TEAction |-> [
       position |-> 4,
       name |-> "Lbl_1",
       location |-> "line 53, col 10 to line 66, col 30 of module telephone"
     ],
    can_send |-> FALSE,
    in_transit |-> {},
    pc |-> "Lbl_2",
    received |-> <<1>>,
    to_send |-> <<2, 3>>
    ]
    >>
```

# 3 Operators and Functions
## 3.1 Operators
An **operator** is the TLA+ equivalent of a *procedure* in programming.
```TLA+
Op(arg1, arg2) == Expr
Op == Expr                \* represent constants
```

> [!example] use operators to simplify the setup of `recycler`
```TLA+
BinTypes == {"trash", "recycle"}
SetsOfFour(set) == set \X set \X set \X set
Items == [type: BinTypes, size: 1..6]

(* --algorithm recycler
variables
    capacity \* ...
    items \in SetsOfFour(Items);
```

> [!tip] semicolons (`;`), whitespace
> The TLA+ does not use semicolons; only the PlusCal computations need semicolons.
> TLA+'s syntax is (with the exception of nested conditional) not whitespace sensitive.

If we want to define an operator using the variables of a PlusCal algorithm, we can place it in a `define` block.

**definitions** must go above *macro definitions* and below *variable definitions*.
> [!example] `define` block
```TLA+
define
    NoBinOverflow ==
        capacity.trash >= 0 /\ capacity.recycle >= 0
    
    CountsMatchUp ==
        Len(bins.trash) = count.trash /\ Len(bins.recycle) = count.recycle
end define;

\* ...
assert NoBinOverflow /\ CountsMatchUp
```

The idiomatic way to write multiple clauses in a single operator: place `/\` before the first clause.
We can also *nested clauses*, this is the only place in TLA+ where *whitespace* matters.

> [!example] multitple clauses in a single operator
```TLA+
define
    Invariant ==
        /\ capacity.trash >= 0
        /\ capacity.recycle >= 0
        /\ Len(bins.trash) = count.trash
        /\ Len(bin.recycle) = count.recycle
end define;
```

```TLA+
\* A /\ (B \/ C) /\ D

/\ A
/\ B
    \/ C
/\ D
```

**special forms of operators** with their own syntax:
### 3.1.1 high-order operators
- `Apply`
high-order operators: the operators that take other operators as paramenters, using `_` to specify how many parameters the operator takes.
```TLA+
Add(a, b) == a + b
Apply(op(_, _), x , y) == op(x, y)

\* Apply(Add, 1, 2)
\* 3
```
### 3.1.2 anonymous operators
- `LAMBDA`
define anonymous operators: `LAMBDA param1, param2, paramN: body`.
anonymous operators can only be used as arguments to other operators, not as stand-alone operators.
```TLA+
Apply(LAMBDA x, y: x + y, 1, 2)
\* 3
```

`>=`, `\o` etc are operators.

> [!tip] User Definable Operator Symbols
> Toolbox - 'Help' - 'The TLA+ Cheat Sheet'

> [!example] user defined operators
```TLA+
set ++ elem == set \union {elem}
set -- elem == set \ {elem}

\* {1, 2} ++ 3
\* {1, 2, 3}

\* {1, 2} -- 2
\* {1}
```

## 3.2 Invariants

We can use operators as **invariants**: an invariants is a boolean expression that's checked at the end of every step of the model. It it's false, the model fails.

tell model to check invariants: 'Model Overview' - "Invariants' - 'Add' the invariants or 'Add' any expression we want.

### 3.2.1 Logical Operators
express complex properties.
#### 3.2.1.1 `\A`, `\E`
**quantifiers**
- `\A` means *all elements in a set*: `\A x \in set: P(X)`, which means *for all elements in the set, P(x) is true*.
- \E` means *there exists some element in the set*: `\E x \in set: P(X)`, which means *there is at least one element in the set where P(x) is true*.

If the set is empty, `\E` will be false, and `\A` will be true, regardless of the expression.

- `~\E` for *there is no element in the set*.
- `~\A` for *not all elements in the set*.

> [!example] `\A`, `\E`
```TLA+
AllLessThan(set, max) == \A mum \in set: num < max

\* AllLessThan({}, 1)         \* TRUE
\* AllLessThan({1, 3}, 4)     \* TRUE
\* AllLessThan({1, 3}, 2)     \* FALSE
\* AllLessThan({1, 3}, "FOO") \* error

SeqOverlapsSet(seq, set) == \E x \in 1..Len(seq): seq[x] \in set

\* SeqOverlapsSet(<<1, 3>>, {2, 3, 4}) \* TRUE

\* \E x \in {}: 1 > x         \* FALSE
```

> [!example] define quantifiers over multiple values
A *commutative* operator is one where the order of the arguments doesn't matter.
```TLA+
\* pull mutlple elements from the set
IsCommutativeOver(Op(_, _), S) ==
    \A x, y \in S: Op(x, y) = Op(y, x)

\* sequential clauses to the quantifier
IsCommutativeOver(Op(_, _), S) ==
    \A x \in S, y \in S: Op(x, y) = Op(y, x)

\* unpack a tuple
IsCommutativeOver(Op(_, _), S) ==
    \A <<x, y>> \in S \X S: Op(x, y) == Op(y, x)

\* IsCommutativeOver(LAMBDA x, y: x + y, 1..10) \* TRUE
\* IsCommutativeOver(LAMBDA x, y: x - y, 1..10) \* FALSE
```

- `=>`, `<=>`
	- `P => Q` means *if P is true, then Q is true*, it's equivalent to `~P \/ Q`.
	- `P <=> Q` means *either P and Q are both true, or P and Q are both false*

> [!example] `=>`, `<=>`
```TLA+
Xor(A, B) == (~A /\ B) \/ (A /\ ~B)
OtherXor(A, B) == ~A <=> B

\* \A A \in BOOLEAN, B \in BOOLEAN: Xor(A, B) = OtherXor(A, B)
\* TRUE
```
```TLA+
\* (P /\ Q) => R
/\ P
/\ Q
=> R

\* P /\ (Q => R)
/\ P
/\ Q
    => R
```

### 3.2.2 Expressions
all of these keywords can be used as part of any expression.
#### 3.2.2.1 `LET-IN`
any expression can use `LET-IN` to add *local operators and definitions* to just that expression alone.
> [!example] `LET-IN`
```TLA+
RotateRight(seq) ==
    LET
        last == seq[Len(seq)]
        first == SubSeq(seq, 1, Len(seq) - 1)
    IN <<last>> \o first

\* RotateRight(<<1, 2, 3>>)
\* <<3, 1, 2>>
```
#### 3.2.2.2 `IF-THEN-ELSE`
- `IF Condition THEN Exp1 ELSE Exp2`
All if-statements must include an `ELSE`.
> [!example] `IF-THEN-ELSE`
```TLA+
Max(x, y) == IF x > y THEN x ELSE y

\* <<Max(2, 3), Max(3, 2)>>
\* <<3, 3>>
```

#### 3.2.2.3 `CASE`
Subsequent cases in a case statement are marked by a `[]`.
`OTHER` is the default. 
If none of the cases match and there is no default, TLC consider that an error.
If more than one case statement matches, the behavior is *undefined*.
> [!example] `CASE`
```TLA+
CASE x = 1 -> TRUE
  [] x = 2 -> TRUE
  [] x = 3 -> 7
  [] OTHER -> FALSE
```

#### 3.2.2.4 `CHOOSE`
- `CHOOSE x \in S: P(x)` means *select an x such that P(x) is true*.
If more than one `x` matches, TLC will select an arbitrary one.
If no `x` matches, TLC will raise an error.
> [!example] `CHOOSE`
```TLA+
IndexOf(seq, elem) ==
    CHOOSE i \in 1..Len(seq): seq[i] = elem

\* IndexOf(<<8, 3, 1>>, 3)
\* 2

\* IndexOf(<<8, 3, 1>>, 4) 
\* error
```

combine `CHOOSE` with logical operators:
```TLA+
(* CHOOSE an element of the set that's bigger than the rest of them. *)
Max(set) == CHOOSE x \in set: \A y \in set: x >= y

\* Max(1..10)
\* 10
```

solve equations: `2x + y = -2` and `3x - 2y = 11`:
```TLA+
CHOOSE <<x, y>> \in (-10..10) \X (-10..10)
    /\ 2*x + y = -2
    /\ 3*x - 2*y = 11

\* <<1, -4>>
```

## 3.3 Functions
A **function** maps a set of inputs (its **domain**) to a set of outputs.
The mapping can either be set manually or via an expression.

```TLA+
[x \in set 
	|-> P(x)]

(* use multiple elements *)
[x, y \in set 
	|-> P(x, y)]
[x \in set1, y \in set2 
	|-> Q(x, y)]
```

Use `f[bar]` to *call* a function. 
If `f` has two values, we can call it with `f[a, b]` or `f[<<a, b>>]`.
*Tuples and structures are actually just special cases of functions.*

Just as we can assign sequences and structures to PlusCal variables, we can also assign functions:
```TLA+ hl_lines="5"
Flags == {"f1", "f2"}

(*--algorithm flags
variables
flags = [f \in Flags |-> FALSE];
begin
with f \in Flags do
    flags[f] := TRUE;
end with;
end algorithm*)
```

### 3.3.1 Functions and Operators
We can make a *function* as an *operator*.
```TLA+
(* the operator does not take any arguments *)
Op == [x \in S |-> P(x)]
Op[x \in S] == P(x)

(* the operator defines a function based on its arguments *)
MapToSomeNumber(set, num) == [x \in set |-> num]
```

> [!tip] operators v.s. functions
> Operators can work with arbitrary inputs, while functions must have a specified domain.
> 
> Functions can be created by operators and passed around, and they have no restrictions on recursion or higher-order operators.

```TLA+
SumUpTo(n) ==
    LET F[m \in 0..n] ==
        IF m = 0 THEN 0
        ELSE m + F[m-1]    \* recursion
    IN F[n]

(* with PT library *)
PT == INSTANCE PT
SumUpTo(n) ==
    PT!ReduceSet(LAMBDA x, y: x + y, 0..n, 0)

\* SumUpTo(10)
\* 55
```

special operators to manipulate functions:
#### 3.3.1.1 `DOMAIN`
`DOMAIN` is a special prefix operator that gives the possible inputs to a function.
If `func = [x \in set |-> ...]`, then `DOMAIN func = set`.
`DOMAIN seq = 1..Len(seq)` and `DOMAIN struct` is the set of keys in the structure.

> [!example] `DOMAIN`
```TLA+
F[x \in BOOLEAN] == x
G == <<6, 0, 9>>
H == [F |-> DOMAIN F, G |-> DOMAIN G]

\* H
\* [F |-> {FALSE, TRUE}, G |-> 1..3]

\* DOMAIN H
\* {"F", "G"}
```

#### 3.3.1.2 `@@`
- `f @@ g` merges two functions. 
If some element `x` is in both domains, then we use `f[x]`.
```TLA+
(* identical definition. *)
Merge(f, g) == [
x \in (DOMAIN f) \union (DOMAIN g) |->
    IF x \in DOMAIN f
    THEN f[x]
    ELSE g[x]
]
```

> [!example] `@@`
```TLA+
EXTENDS TLC

f[x \in 1..2] == "a"
g[x \in 2..3] == "b"

\* f @@ g
\* <<"a", "a", "b">>

\* g @@ f
\* <<"a", "b", "b">>
```

#### 3.3.1.3 `:>`
- `a :> b` is the function `[x \in {a} |-> b]`.
> [!example] `:>`
```TLA+
EXTENDS TLC

\* (2 :> 3)[2]
\* 3

\* ("a" :> "b").a
\* "b"
```

### 3.3.2 Sets of Functions
`[set1 -> set2]` is *the set of all functions* that map elements of `set1` to elements of `set2`.

> [!tip] `|->` v.s. `->`
`|->` is for functions, not sets of functions.
```TLA+
\* [s \in {"a", "b"} |-> {1, 2}]
\* [a |-> {1, 2}, b |-> {1, 2}]

\* [{"a", "b"} -> {1, 2}]
\* { [a |-> 1, b |-> 1],
\*   [a |-> 1, b |-> 2],
\*   [a |-> 2, b |-> 1],
\*   [a |-> 2, b |-> 2] }
```

TLC displays functions with a domain `1..N` as a sequence: `[x \in 1..3 |-> P(x)]` is just the sequence `<<P(1), P(2), P(3)>>`. (the fact that sequences are just functions with a special domain.)

The set of functions `[1..3 -> S]` is `S \X S \X S`.

> [!example] sets of functions
```TLA+
SeqOf(set, count) == [1..count -> set]

\* SeqOf({"a", "b"})
\*{ <<"a", "a">>,
\*     <<"a", "b">>,
\*     <<"a", "c">>,
\*     <<"b", "a">>,
\*     <<"b", "b">>,
\*     <<"b", "c">>,
\*     <<"c", "a">>,
\*     <<"c", "b">>,
\*     <<"c", "c">> }
```
## 3.4 Example
> [!example] Knapsack Problem
>
> We have a knapsack of volume N and a set of items.
> Each item has a value and a size.
> We can fit any number of each item in the knapsack as long as the sum of them all is less than the capacity of the sack.
> 
> What's the most valuable knapsack you can make?
> 
> Show how we can formally define the most valuable knapsack with TLA+ operators.

```TLA+
---------- MODULE  knapsack ----------
EXTENDS TLC, Integers, Sequences
PT == INSTANCE PT

Capacity == 7

Items == {"a", "b", "c"}
ItemParams == [size: 2..4, value: 0..5]
\* ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
ItemSets == [Items -> ItemParams]

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

\* sack: item |-> count
KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

\* may be multiple best cases
BestKnapsacks(itemset) ==
    LET 
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
                    \A worse \in all \ {best}:
                        value(best) >= value(worse)
    IN {k \in all: value(best) = value(k)}

\* BestKnapsacks(HardcodedItemSet)
\* {[a |-> 1, b |-> 3, c |-> 0]}

\* KnapsackValue([a |-> 1, b |-> 3, c |-> 0], HardcodedItemSet)
\* 10

(*--algorithm knapsack
variables
    itemset \in ItemSets;

begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm; *)
===============================
```

result:
```TLA+
(* Model Checking Results *)
StatesFound == 17496
DistinctStates == 11664

(* TLC Errors *)
Error == "no"
```


# 4 Constants, Models, and Imports
Use *the TLC configuration* to simplify and generalize model, and add modularity and better debugging.
## 4.1 Constants
**Constants** are values that are *defined in the model* instead of the specification.
Constants can be used anywhere you'd use any other value, and they cannot be modified.
```TLA+ hl_lines="2"
EXTENDS Integers, TLC
CONSTANTS Capacity, Items, SizeRange, ValueRange
\* we could also do CONSTANTS Op(_, _...)
```

For any given model, we assign values to the constants in 'Model Overview' - 'What is the model?': (must have specified constant in the spec with `CONSTANTS ConstantName` ahead)

- **constant operators**: define the operator.
- **constant values**: 'Ordinary assignment', 'Model value', 'Set of model values'.

> [!tip] Notation: specify assignment
specify assignment to constants with `C <- val`.
### 4.1.1 Ordinary Assignment
set the constant to any other TLA+ value: numbers, sets, sequences, functions, etc.
```
Capacity <- 7
ValueRange <- 0..3
SizeRange <- 1..4
Items <- {"a", "b", "c"}
```
### 4.1.2 Model Values
If we assign a **model value** to a constant, that constant becomes *a new type* that's only equal to itself.
If `M` and `N` are both model values, then `M /= N`.

Comparing values of different types is considered a spec failure.
we cannot have `{TRUE, FALSE, "null"}`, but can have `{TRUE, FALSE, NULL}` if `NULL` is a model value.
### 4.1.3 Sets of Model Values
We can also define a whole set of model values. When using constants, sets of model values are often preferable to sets of strings:

**symmetric**: in a given run, we will get the same results if we replace all instances of `i1` with `i2`, `i2` with `i3`, and `i3` with `i1`. that means the set is *symmetric*.
```
Items <- [ model value ] {i1, i2, i3}

Items <- [ model value ] <symmetrical> {i1, i2, i3}
```

> [!example] `knapsack` with model values
> 
```TLA+ {3, 6, 8, 9, 10}
---------- MODULE knapsack ----------
EXTENDS TLC, Integers, Sequences
CONSTANTS Capacity, Items, SizeRange, ValueRange
PT == INSTANCE PT

\*Capacity == 7

\*Items == {"a", "b", "c"}
\*ItemParams == [size: 2..4, value: 0..5]
ItemParams == [size: SizeRange, value: ValueRange]
\* ItemSets == [a: ItemParams, b: ItemParams, c: ItemParams]
ItemSets == [Items -> ItemParams]

HardcodedItemSet == [
    a |-> [size |-> 1, value |-> 1],
    b |-> [size |-> 2, value |-> 3],
    c |-> [size |-> 3, value |-> 1]
]

\* sack: item |-> count
KnapsackSize(sack, itemset) ==
    LET size_for(item) == itemset[item].size * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: size_for(item) + acc, Items, 0)

ValidKnapsacks(itemset) ==
    {sack \in [Items -> 0..4]: KnapsackSize(sack, itemset) <= Capacity}

KnapsackValue(sack, itemset) ==
    LET value_for(item) == itemset[item].value * sack[item]
    IN PT!ReduceSet(LAMBDA item, acc: value_for(item) + acc, Items, 0)

\* may be multiple best cases
BestKnapsacks(itemset) ==
    LET 
        value(sack) == KnapsackValue(sack, itemset)
        all == ValidKnapsacks(itemset)
        best == CHOOSE best \in all:
                    \A worse \in all \ {best}:
                        value(best) >= value(worse)
    IN {k \in all: value(best) = value(k)}

\* BestKnapsacks(HardcodedItemSet)
\* {[a |-> 1, b |-> 3, c |-> 0]}

\* KnapsackValue([a |-> 1, b |-> 3, c |-> 0], HardcodedItemSet)
\* 10

(*--algorithm knapsack
variables
    itemset \in ItemSets;

begin
    assert BestKnapsacks(itemset) \subseteq ValidKnapsacks(itemset);
end algorithm; *)
===============================
```

'Model Overview' - 'What is the model?'
```
Items <- [ model value ] {i1, i2, i3}                   \* case 1
Items <- [ model value ] <symmetrical> {i1, i2, i3}     \* case 2

ValueRange <- 0..3
SizeRange <- 1..4
Capacity <- 7   
```

see `MC.tla` and `MC.cfg`.

result:
```TLA+ nums
(* Model Checking Results *)
StatesFound == 12288        \* case 1
DistinctStates == 8192

StatesFound == 5728         \* case 2
DistinctStates == 1632

(* TLC Errors *)
Error == "no"
```

### 4.1.4 `ASSUME`
`ASSUME` is an expression about the constants that, if false, prevents the spec from running.

`ASSUME` may use constants and constant operators as part of the expression, but may not use operators not defined as constants.
```TLA+ hl_lines="2 3 4"
CONSTANTS Capacity, Items, SizeRange, ValueRange
ASSUME SizeRange \subseteq 1..Capacity
ASSUME Capacity > 0
ASSUME \A v \in ValueRange: v >= 0

ItemParams == [size: SizeRange, value: ValueRange]
ItemSets == [Items -> ItemParams]
```

TLA+ supports specifying certain kinds of **infinite sets**, we cannot select elements from the set nor assign them as part of variables, but we can test membership:
- `EXTENDS Integers`: `Int`.
- `EXTENDS Naturals`: `Nat` (`Nat == {0, 1, 2, ...}`)
```TLA+ hl_lines="2 3"
ASSUME SizeRange \subseteq 1..Capacity
ASSUME Capacity \in Nat \ {0}
ASSUME ValueRange \subseteq Nat
```
## 4.2 TLC Runtime
### 4.2.1 Configuration
- [[index.TLA+#6.2.1 TLC Configuration]]
### 4.2.2 Error Traces
*Error-Trace Exploration*: between the error output and the 'Error-Trace'.
we can inject arbitrary expressions into the trace and evaluate it for debugging, the expressions are evaluated for every step of the error trace.

Every expression uses the values it has at the *beginning* of the step. 
By adding a single quote `'`, we can ask it to evaluate what it is at the *end* of the step. This is called a **primed value**:
- `Op(x', y)`: evaluate what `Op` is after `x` changes in that step.
- `Op(x, y)'`: evaluate what `Op`'s output changed to.
- cannot nest two primed operators: `SumItemsOver(knapsack', "value")'` is an error.
### 4.2.3 The TLC Module
#### 4.2.3.1 `Print` and `PrintT`
`Print(val, out)` prints `val` and `out` to 'User Output' and then evaluates to `out`.
`PrintT(val)` is `Print(val, TRUE)`.

TLC provides `JavaTime`, which evaluates to the current epoch time.
#### 4.2.3.2 `Assert`
`Assert(val, out)` is `TRUE` if `val` is `TRUE`; if `val` is false, the spec fails with output `out`.
```TLA+
Assert(3 < 5, "3 is more than 5")
Assert(3 > 5, "3 is more that 5")

LET x == 3 y == 5 IN Assert(x > y, <<x, " is more than ", y>>)
LET x == 3 y == 5 IN Assert(x > y, ToString(x) \o " is more that " \o ToString(y))
```
#### 4.2.3.3 `Permutations` and `SortSeq`
`Permutations(set)` is the set of all possible ways to order the set `set`.
`SortSeq(seq, Op(_, _))` sorts a sequence based on `Op`.
```TLA+
Permutations({1, 2, 3})
\*{ <<1, 2, 3>>,
\*     <<1, 3, 2>>,
\*     <<2, 1, 3>>,
\*     <<2, 3, 1>>,
\*     <<3, 1, 2>>,
\*     <<3, 2, 1>> }

SortSeq(<<1, 2, 3>>, LAMBDA x, y: x > y)
\* <<3, 2, 1>>
```
## 4.3 Imports
A specification can have multiple *modules*.
The first moudle you create is the *main* module and the only one that is run.
Other modules can provide new operators, values and data structures to the specification.

create a *new module* in spec: 'File' - 'Open Module' - 'Add TLA+ Module'.
The new module should not contain any PlusCal, *it is for operators only*. *it may have constants*.

we can include any modules in spec that are in the library path by default.

two ways to import modules: 
- `EXTENDS`: can list multiple modules at once.
- `INSTANCE`: only import one at a time.

`EXTENDS` and `INSTANCE` will not import operators or instance prepended with `LOCAL`.

The Toolbox discovers modules in one of the three ways:

1. all modules in the same folder as the rest of your spec.
2. add a universal library path: 'Preference' - `TLA+ Preferences'.
3. add an additional library path local to your project: right click on the project in 'Spec Explorer', then select 'Prferences'.
### 4.3.1 `EXTENDS`
`EXTENDS` dumps the module into the same namespace. 
The module may *not* have any constants.

We cannot have more than one `EXTENDS` statement in spec.
```TLA+
EXTENDS TLC, Integers
```
### 4.3.2 `INSTANCE`
`INSTANCE` works like `EXTENDS`, except:
1. we cannot import multiple modules in the same statement.
2. like operators, we can prefix an instance with `LOCAL` to make it private to the module.
3. we can namespace modules: assign to an operator, for example `PT == INSTANCE PT`, use `PT!Op` to call an operator in `PT`.
4. we can import *parameterized modules*, or modules with constants defined at import time.

```TLA+
---------- MODULE Point ----------
LOCAL INSTANCE Integers
CONSTANTS X, Y
ASSUME X \in Int
ASSUME Y \in Int

Point == <<X, Y>>
Add(x, y) == <<X + x, Y + y>>
===============================
```

since `Point` module has constants, we have to define them on import:
```TLA+
INSTANCE Point WITH X <- 1, Y <- 2

Point        \* <<1, 2>>
Add(3, 4)    \* <<4, 6>>
```

we can assign the instance to an operator, which acts as a *namespace*:
```TLA+
P1 == INSTANCE Point WITH X <- 1, Y <- 2
P2 == INSTANCE Point WITH X <- 2, Y <- 1

P1!Point    \* <<1, 2>>
P2!Point    \* <<2, 1>>
```

partial assignment to a namespace:
```TLA+
P1(Y) == INSTANCE Point WITH X <- 1
P2(X) == INSTANCE Point WITH Y <- 1
P3(X, Y) == INSTANCE Point

P1(3)!Point        \* <<1, 3>>
P2(3)!Add(1, 1)    \* <<4, 2>>
P3(1, 2)!Add(2, 3) \* <<3, 5>>
```

misc style:
```TLA+
X == 1
Y == 2
P == INSTANCE Point

\* equivalent to

P == INSTANCE Point WITH X <- 1, Y <- 2
```


# 5 Concurrency
In a **concurrent system**, there is no single timeline. We have multiple actions that can happen in any order, producing a fractured spread of new timelines.

## 5.1 Labels

> [!quote] Labels
**Labels** determine the *grain of atomicity* of specs.
>
> TLC executes everything in a label in a single step, or **action**.
> Then it checks all invariants and looks for the next label to execute.
> Just as TLC checks all possible behaviors on every `either` and `with`, it also checks all possible behaviors on the set of next possible labels.

When translating PlusCal into TLA+, we get a `pc` (program counter) variable that tracks which label we are currently on.
`pc = "A"` means the next state will consist of everything under the `A` label.
`goto NameOfLabel` means jumping to a label in the same process.
PlusCal automatically defines a `Done` label at the end of every process.

place labels with the rules:

1. must have a label at the beginning of each process and before every `while`.
2. may not place a label inside a macro or a `with` statement.
3. must place a label after every `goto`.
4. if use an `either` or an `if`, and any possible branch has a label inside it, must place a label after the end of the control structure.
5. may not assign th the same variable twice in a label.

> [!example] Labels
```TLA+
Valid:
    either x := 1;
    or     x := 2;
    end either;
Invalid:
    x := 1;
    x := 2;
```

even though `x` appear twice in `Valid` label, only one of those assignments can happen in any execution of the label.

`Invalid` assign to `x` twice, so it's an invalid use of a label.

we cannot write this, because that assigns to `struct` twice:

```TLA+
Invalid:
    struct.key1 = 1;
    struct.key2 = 2
```

we can use `||` to combine two assignments and they will be evaluated simultaneously:

```TLA+
Valid:
    struct.key1 = 1 ||
    struct.key2 = 2;
```

## 5.2 Processes

The *reader-write pattern*: two or more asynchronous processes communicating over a shared channel, one of which is primarily writing messages and one of which is primarily consuming them.


Use `process` keyword to mark the system *concurrent*: there is no enforced order to when either process runs.

Each process must be assigned a value. 
All processes must explicitly use (and begin with) labels.

TLC is able to choose any process to run.
`pc` is no longer a single value, it's a function that represents the current label each process can execute.


> [!example] bounded message queue `message_queue`
invariant: the message buffer length does not exceed the maximum size.
```TLA+
---------- MODULE  ----------
EXTENDS TLC, Integers, Sequences
CONSTANTS MaxQueueSize

(*--algorithm message_queue
variables queue = <<>>;

define
    BoundedQueue == Len(queue) <= MaxQueueSize
end define;

macro add_to_queue(val) begin
    await Len(queue) < MaxQueueSize;
    queue := Append(queue, val);
end macro;

process writer = "writer"
begin Write:
    while TRUE do
        \* queue := Append(queue, "msg");
        \* await Len(queue) <= MaxQueueSize;
        add_to_queue("msg");
    end while;
end process;

process reader = "reader"
variables current_message = "none"; \* local variable
begin Read:
    while TRUE do
         await queue /= <<>>;
         current_message := Head(queue);
         queue := Tail(queue);
         
         either
            skip;
         or
            NotifyFailure:
                current_message := "none";
                add_to_queue("fail");
         end either;
    end while;
end process;

end algorithm; *)
===============================
```

`reader` process has a **local variable** `current_message`, which cannot be accessed in `writer` process or anything in a `define` block, but a macro can use it if called in the process.
local variable can also be defined with `\in`.

result: the spec fails

### 5.2.1 `await`

`await Expression` prevents a step from running until `Expression` is true.
we can also use the keyword `when`.

> [!example] `await`
```TLA+ hl_lines="5 15"
process reader = "reader"
variables current_message = "none";
begin Read:
    while TRUE do
         await queue /= <<>>;
         current_message := Head(queue);
         queue := Tail(queue);
    end while;
end process;

process writer = "writer"
begin Write:
    while TRUE do
        queue := Append(queue, "msg");
        await Len(queue) <= MaxQueueSize;
    end while;
end process;
```

### 5.2.2 Deadlocks

A **deallock** is when none of the process in specs can take any actions: usually because of an `await` statement, but can also happen with `with x \in S` if `S` is the empty set.

'Model Overview' - 'What to check?' - 'Deadlock'.

> [!example] process sets
change the reader from a single process to a set of them:
```TLA+
process reader \in {"r1", "r2"}
\* ...
    add_to_queue(self);
\* ...
end process;
```

process with multiple copies: `self` is whatever value that given copy is assigned to.

## 5.3 Procedures

A **procedure** has the same syntax as a macro, except that it has labels in it.
we can define local variables for a procedure, can only define the local variables as equaling an expression (`=`), but not being some element of a set (`\in`).

exit the procedure with `return`: it does not return any value to the calling process, it simply ends the procedure.

in order to call a procedure in a process, prefix it with `call`.
a called procedure must be immediately followed by a lebel, the end of the enclosing block, a `goto`, or a `return`.

procedures must be defined after macros and before processes.

> [!example] Procedure
```TLA+
procedure add_to_queue(val="") begin
    Add:
        await Len(queue) < MaxQueueSize;
        queue := Append(queue, val);
        return;
end procedure;

process writer = "writer"
\* ...
    call add_to_queue("msg");
\* ...
end process;
```

## 5.4 Example

> [!example] several clients consume some shared resource that periodically renews: `cache`
```TLA+
---------- MODULE  ----------
EXTENDS Integers
CONSTANT ResourceCap, MaxConsumerReq, Actors

ASSUME ResourceCap > 0
ASSUME MaxConsumerReq \in 1..ResourceCap
ASSUME Actors /= {}

(*--algorithm cache
variables
    resource_cap \in 1..ResourceCap,
    resources_left = resource_cap,
    reserved = 0; \* our semaphore

define
    ResourceInvariant == resources_left >= 0
end define;

process actor \in Actors
variables
    resources_needed \in 1..MaxConsumerReq
begin
    WaitForResources:
        while TRUE do
            await reserved + resources_needed <= resources_left;
            reserved := reserved + resources_needed;
            UseResources:
                while resources_needed > 0 do
                    resources_left := resources_left - 1;
                    resources_needed := resources_needed -1;
                    reserved := reserved - 1;
                end while;
                with x \in 1..MaxConsumerReq do
                    resources_needed := x;
                end with;                
        end while;
end process;

process time = "time"
begin
    Tick:
        resources_left := resource_cap;
        goto Tick;
end process;

end algorithm; *)
===============================
```

result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 1588
DistinctStates == 500

(* TLC Errors *)
Error == "no"
```

# 6 Temporal Logic
*invariants*: statements that must be true for all states in a behavior.
**temporal properties**: statements about the hehavior itself.
> [!example] temporal properties
>
>    1. does the algorithm always terminate?
>    2. will all messages in the queue get processed?
>    3. if disrupted, will the system return to a stable state over time?
>    4. is the database eventually consistent?
 
Temporal properties are very powerful but also much harder to guarantee.
Systems have a whole new set of failure modes that apply to temporal properties.
## 6.1 Termination
**Termination** is the requirement that the algorithm eventually ends: if the algorithm *crashes* or *enters an infinite loop*, then it violates termination.

> [!example] a car at a traffic light
>    
>    The *traffic light* alternates between red and green.
>    The *car* waits until the light is green before moving.
>    
>    'Model Overview' - 'What do check?' - 'Properties' - 'Termination'.    
```TLA+
---------- MODULE  ----------
NextColor(c) == CASE c = "red" -> "green"
                  [] c = "green" -> "red"

(*--algorithm traffic
variables
    at_light = TRUE,
    light = "red";
    
process light = "light"
begin
    Cycle:
        while at_light do
            light := NextColor(light);
        end while;
end process;

process car = "car"
begin
    Drive:
        when light = "green";
        at_light := FALSE;
end process;

end algorithm; *)
===============================
```

result:
```TLA+ linenums="1" hl_lines="26 35 37"
(* Model Checking Results *)
StatesFound == 6
DistinctStates == 4

(* TLC Errors *)
Error == "Temporal properties were violated."
ErrorTrace == 
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
at_light |-> TRUE,
light |-> "red",
pc |-> [light |-> "Cycle", car |-> "Drive"]
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Cycle",
   location |-> "line 41, col 10 to line 47, col 30 of module traffic"
 ],
at_light |-> TRUE,
light |-> "green",
pc |-> [light |-> "Cycle", car |-> "Drive"]
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Drive",
   location |-> "line 51, col 10 to line 55, col 26 of module traffic"
 ],
at_light |-> FALSE,
light |-> "green",
pc |-> [light |-> "Cycle", car |-> "Done"]
],
<Stuttering>
>>
```

### 6.1.1 Stuttering
TLC works by looking at all of then enabled labels at each step and picking one.
It also has another option: it can take no action at all, we call this **stuttering**.

In most cases, stuttering does not change the spec; the one special case is if the spec keeps stuttering, over and over again, and never takes any other action.

A **liveness** check is one that verifies the system eventually does what you expected it to do.
Here, TLC never finishes evaluating `Cycle` so the spec never terminates.
(`at_light` is `FALSE`, when evaluting `Cycle` there is no action can be taken, so stutterred.)

stuttering can be useful to represent *a server crashing*, or *a process timing out*, or *an awaited signal never coming*.

If we want to explicitly rule out stuttering, we need to add **fairness**.
### 6.1.2 Fairness, Weak and Strong

2 kinds of fairness:
- **weak fairness**: a weakly fair action will, if it *stays enabled*, eventually happen.
we can declare every label in a process weakly fair by calling it a `fair process`.
> [!example] declare every label in a process weakly fair
```TLA+ hl_lines="1 9"
fair process light = "light"
begin
    Cycle:
        while at_light do
            light := NextColor(light);
        end while;
end process;

fair process car = "car"
begin
    Drive:
        when light = "green";
        at_light := FALSE;
end process;
```

result:
```TLA+ linenums="1" hl_lines="26"
(* Model Checking Results *)
StatesFound == 6
DistinctStates == 4

(* TLC Errors *)
Error == "Invariant NoOverdrafts is violated."
ErrorTrace == 
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
at_light |-> TRUE,
light |-> "red",
pc |-> [light |-> "Cycle", car |-> "Drive"]
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Cycle",
   location |-> "line 41, col 10 to line 47, col 30 of module traffic"
 ],
at_light |-> TRUE,
light |-> "green",
pc |-> [light |-> "Cycle", car |-> "Drive"]
],
<Back to state 1>
>>
```
explain:
- if only the car is fair, then the light might never cycle.
- if only the light is fair, it will eventually cycle to green, but the car might never move.
- if both are fair: if the light keeps cycling between green and red, the `Drive` action is enabled, then disabled, then enabled again, ad infinitum.
Weak fairness only guarantees the action will happen if it stays enabled.
If the light is always green, the car will eventually drive through, but since it can keep cycling, the car is stuck.

- **strong fairness**: a strongly fair action, if it's *repeatedly enabled*, will eventually happen.
There can be gaps in between, but as long as there's some cycle where it keeps getting enabled again, it will happen.

we can make a process strongly fair by calling it a `fair+ process`.

> [!example] make a process strongly fair
```TLA+ hl_lines="1"
fair+ process car = "car"
begin
    Drive:
        when light = "green";
        at_light := FALSE;
end process;    
```

result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 6
DistinctStates == 4

(* TLC Errors *)
Error == "no"
```

explain:
- this will always terminate.
- even if the light keeps cycling, the `Drive` action is repeatedly enabled and so is guaranteed to happen.
- this require the light to be weakly fair: if it's unfair, it can simply cycle to red and stay there.

> [!tip] make invididual actions in a process fair
>
in an unfair process: `A:+` makes it weakly fair.
>
in a weakly fair porcess: `A:+` makes it strongly fair.

> [!tip] make the spec globally fair
>
`--fair algorithm`
## 6.2 The Temporal Operators
`P` and `Q` are boolean statements.
### 6.2.1 `[]`
`[]` is **always**.
- `[]P` means that for `P` is true for all states in all behaviors.
Saying `P` is an invariant is an optimized way of saying that `[]P` is a temporal property, and in fact TLC uses a much faster algorithm to evaluate invariants.
- `~[]P` means that `P` will be false for at least one state.
### 6.2.2 `<>`
`<>` is **eventually**.
- `<>P` means that for every behavior, there is at least one state where `P` is true. 
It may be false before, and it may be false after, but what matters is that it was at some point true.

In the traffic example , `<>(light = "green")` is a satisfied temporal property, but if we instead wrote
```TLA+
variables
at_light = TRUE,
light = "green";
```

then `<>(light = "red")` would be an unsatisfied temporal property: TLC can find a possible execution where the light is never red.

- `~<>P` means that `P` is never true: `[]~P`.
- `<>P` is formally defined as `~[]~P`.

> [!note] Termination
>
Termination is defined as *eventually all processes are done*: 
```TLA+
Termination == <>(\A self \in ProcSet: pc[self] = "Done")
```

Current TLC cannot check set membership of a *variable set* as part of a property with `<>`: we can write `<>(set = {})`, but if write `<>(x \in set)`, then `set` must be a constant or a parameterless operator.
### 6.2.3 `~>`
`~>` is **leads-to**.
- `P ~> Q` means that if there is some state where `P` is true, then `Q` is either true now or in some future state.
Once this is set, it's *irreversible*: even if `P` is later false, `Q` still must happen.

```TLA+
L == (light = "green") ~> ~at_light
```

`L` is true if `light` never becomes `green` or if the light turns green and at some point after the car is no longer at the light.

Unlike `<>`, `~>` is triggered every time `P` is true.
In the base spec, `(light = "red") ~> (light = "green")` holds. But if we write
```TLA+
Cycle:
while at_light do
    light := NextColor(light);
end while;
light := "red"; \* second time
```

then it would not hold.
The first time the light turns red, it later turns green, which is fine (first time: initial state). 
But the second time it turns red it doesn't eventually turn green again, so the property is false.

`~(P ~> Q)` makes TLC explode.

- `P ~> []Q` means if `P` is true, then there is some state where `Q` becomes ture and forever stays true.
### 6.2.4 `[]<>` and `<>[]`
- `[]<>P` means that `P` is *always eventually* true.
- `<>[]P` means that `P` is *eventually always* true.

For a *finite* spec, they mean the same thing: `P` is true at termination.
For an *infinite* spec, 
`<>[]P` means that there is some point where `P` becomes true and forever stays true; 
`[]<>P` means that if `P` ever becomes false, it will eventually become true again.
`[]<>P <=> (~P ~> P)`: `P` being false leads to `P` being true later.

In out current version of the traffic spec, bothe `[]<>(light = "green")` and `<>[](light = "green")` are true, while `[]<>(light = "red")` and `<>[](light = "red")` are false.

If we write
```TLA+
while TRUE do
light := NextColor(light);
end while;
```
then `<>[](light = "green")` becomes false and `[]<>(light = "red")` becomes true.

> TODO: need more explainations or materials here.

As with `<>`, current TLC cannot check set membership of a variable set as part of a property with `<>[]` or `[]<>`.

## 6.3 Limitations of Liveness
From a practical perspective, the main limitation of temporal properties is that checking liveness is slow.
There is one other, extremely important limitation of temporal properties: do not combine temporal properties and sysmetry sets.
## 6.4 Example

> [!example] Dekker's Algorithm
>
> Dekker's Algorithm was, historically, the first successful algorithm to allow two threads to share a single resource without having a race condtion.
> 
> It guarantees that both threads will eventually perform their update, but not at the same time, and without using any CPU-specfic feature.
> The only thing you need is some shared memory.

```TLA+
---------- MODULE dekker ----------
EXTENDS TLC, Integers
CONSTANT Threads \* <- 1..2

(*--algorithm dekker
variables
    flag = [t \in Threads |-> FALSE],
    next_thread \in Threads;

define
    \* at most one thread is in the critial section at a time
    AtMostOneCritical ==
        \A t1, t2 \in Threads:
            t1 /= t2 => ~(pc[t1] = "CS" /\ pc[t2] = "CS")
    Liveness ==
        \A t \in Threads:
            <>(pc[t] = "CS")
end define;

\* simulate atomicity by using a new label for every sinle line
fair process thread \in Threads
begin
    P1: flag[self] := TRUE;
    P2: 
        while \E t \in Threads \ {self}: flag[t] do
            P2_1:
                if next_thread /= self then
                    P2_1_1: flag[self] := FALSE;
                    P2_1_2: await next_thread = self;
                    P2_1_3: flag[self] := TRUE;
                end if;
        end while;
    CS: skip; \* the critical section
    P3: 
        with t \in Threads \ {self} do
            next_thread := t;
        end with;
    P4: flag[self] := FALSE;
    P5: goto P1;
end process;

end algorithm; *)
===============================
```

MC:
```
# MC.tla
const_166101127154117000 == 
1..2

# MC.cfg
CONSTANT
Threads <- const_166101127154117000
SPECIFICATION
Spec
INVARIANT
AtMostOneCritical
PROPERTY
Liveness
```


# 7 Algorithms
This chapter is about how we can write and verify algorithms with TLA+.
While we will be implementing them, our focus is on the *verification*, not the implementation.
By *algorithm*, we **assume** that algorithms are code intended to *terminate* and *produce an output*, rather than run forever or continuously interact with its environment.
## 7.1 Single-Process Algorithms

most single-process algorithm specification template:
```TLA+
---------- MODULE name ----------
EXTENDS \* whatever

Expected(input) == \* ...

Helper == \* ...

(*--algorithm name
variables
input \in \* ...
output; \*
\* helper variables

begin
\* algorithm implementation
assert output = Expected(input);
end algorithm; *)
===============================
```

> TODO: add description.

> [!example] add

## 7.2 Max
> [!example] "max"
> Given a sequence of numbers, return the largest element of that sequence.
>   
> For example, `max(<<1,1,2,01>>) = 2`. 

## 7.3 Leftpad
> [!example] leftpad
> Given a character, a length n, and a string, return a string padded on the left with that character to length n.
If n is less than the length of the string, output the original string.
>  
> For example, `LeftPad(" ", 5, "foo") = "  foo"`, `LeftPad(" ", 1, "foo") = "foo"`.

## 7.4 Properties of Algorithms
verifying *correctness* is easy enough: just run the spec and confirm we have the right result at the end.
verifying other properties like *performance characteristics or bounds* are more difficult: we can sometimes handle this by adding auxiliary variables and asserting their values at the end. 

> [!example] definitely binary search
```TLA+ linenums="1" hl_lines="40"
\*
EXTENDS Integers, Sequences, TLC
PT == INSTANCE PT

OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq):
            seq[x] >= seq[x-1] }

Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2 * f[x-1]
    IN f[n]

MaxInt == 4

(*--algorithm definitely_binary_search
variables
    i = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    target \in 1..MaxInt,
    found_index = 0,
    counter = 0;
    
begin
    Search:
        while i <= Len(seq) do
            counter := counter + 1;
            if seq[i] = target then
                found_index := i;
                goto Result;
            else
                i := i + 1;
            end if;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter-1) <= Len(seq); \* for performance
        end if;
        if target \in PT!Range(seq) then
            assert seq[found_index] = target;
        else
            \* 0 is out of DOMAIN seq, so can represent "not found"
            assert found_index = 0;
        end if;
end algorithm; *)
```    

result:
```TLA+ linenums="1" hl_lines="28 30 41 43 53 55 57"
(* Model Checking Results *)
StatesFound == 1173
DistinctStates == 1081

(* TLC Errors *)
Error == "The first argument of Assert evaluated to FALSE; the second argument was: Failure of assertion at line 40, column 13."
ErrorTrace == 
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
counter |-> 0,
found_index |-> 0,
i |-> 1,
pc |-> "Search",
seq |-> <<1, 1, 2>>,
target |-> 2
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Search",
   location |-> "line 62, col 11 to line 74, col 40 of module definitely_binary_search"
 ],
counter |-> 1,
found_index |-> 0,
i |-> 2,
pc |-> "Search",
seq |-> <<1, 1, 2>>,
target |-> 2
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Search",
   location |-> "line 62, col 11 to line 74, col 40 of module definitely_binary_search"
 ],
counter |-> 2,
found_index |-> 0,
i |-> 3,
pc |-> "Search",
seq |-> <<1, 1, 2>>,
target |-> 2
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Search",
   location |-> "line 62, col 11 to line 74, col 40 of module definitely_binary_search"
 ],
counter |-> 3,
found_index |-> 3,
i |-> 3,
pc |-> "Result",
seq |-> <<1, 1, 2>>,
target |-> 2
]
>>
```

> [!example] binary search
```TLA+
EXTENDS Integers, Sequences, TLC
PT == INSTANCE PT

OrderedSeqOf(set, n) ==
    { seq \in PT!SeqOf(set, n):
        \A x \in 2..Len(seq):
            seq[x] >= seq[x-1] }

Pow2(n) ==
    LET f[x \in 0..n] ==
        IF x = 0
        THEN 1
        ELSE 2 * f[x-1]
    IN f[n]

MaxInt == 4

(*--algorithm binary_search
variables
    low = 1,
    seq \in OrderedSeqOf(1..MaxInt, MaxInt),
    high = Len(seq),
    target \in 1..MaxInt,
    found_index = 0,
    counter = 0;

begin
    Search:
        while low <= high do
            counter := counter + 1;
            with
                m = (low + high) \div 2
            do
                if seq[m] = target then
                    found_index := m;
                    goto Result;
                elsif seq[m] < target then
                    low := m + 1;
                else
                    high := m - 1;
                end if;
            end with;
        end while;
    Result:
        if Len(seq) > 0 then
            assert Pow2(counter-1) <= Len(seq); \* for performance
        end if;
        if target \in PT!Range(seq) then
            assert seq[found_index] = target;
        else
            \* 0 is out of DOMAIN seq, so can represent "not found"
            assert found_index = 0;
        end if;
end algorithm; *)
```    

result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 1483
DistinctStates == 1203

(* TLC Errors *)
Error == "no"
```

## 7.5 Multiprocess Algorithm
multiprocess algorithms are similar to single-process algorithms, except that we want to check our assertion when all of the processes terminate.
instead of hard-coding an assertion in, we should use *eventually always* (`<>[]`) operator to check that the algorithm ends with a certain thing being true.

*remember to use fair processes if we don't want to simulate algorithm crashing midway through*.

> [!example] An example of multiprocess algorithm.
```TLA+
EXTENDS Integers, Sequences, TLC

(*--algorithm counter_incrementer
variables
    counter = 0,
    goal = 3;

define
    Success == <>[](counter = goal)
end define;


fair process incrementer \in 1..3
variable local = 0
begin
    \* case 1: Get then Increment
\*    Get:
\*        local := counter;
\*    Increment:
\*        counter := local + 1;
    \* case 2: GetAndIncrement
    GetAndIncrement:
        local := counter;
        counter := local + 1;
end process;

end algorithm; *)
```

case 1:
```TLA+ linenums="1" hl_lines="29 40 51 59 62 73 84"
(* Model Checking Results *)
StatesFound == 128
DistinctStates == 84

(* TLC Errors *)
Error == "Temporal properties were violated."
ErrorTrace == 
<<
[
 _TEAction |-> [
   position |-> 1,
   name |-> "Initial predicate",
   location |-> "Unknown location"
 ],
counter |-> 0,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Get", "Get", "Get">>
],
[
 _TEAction |-> [
   position |-> 2,
   name |-> "Get",
   location |-> "line 50, col 14 to line 53, col 45 of module counter_incrementer"
 ],
counter |-> 0,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Get", "Get", "Increment">>
],
[
 _TEAction |-> [
   position |-> 3,
   name |-> "Get",
   location |-> "line 50, col 14 to line 53, col 45 of module counter_incrementer"
 ],
counter |-> 0,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Get", "Increment", "Increment">>
],
[
 _TEAction |-> [
   position |-> 4,
   name |-> "Get",
   location |-> "line 50, col 14 to line 53, col 45 of module counter_incrementer"
 ],
counter |-> 0,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Increment", "Increment", "Increment">>
],
[
 _TEAction |-> [
   position |-> 5,
   name |-> "Increment",
   location |-> "line 55, col 20 to line 58, col 49 of module counter_incrementer"
 ],
counter |-> 1,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Increment", "Done", "Increment">>
],
[
 _TEAction |-> [
   position |-> 6,
   name |-> "Increment",
   location |-> "line 55, col 20 to line 58, col 49 of module counter_incrementer"
 ],
counter |-> 1,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Increment", "Done", "Done">>
],
[
 _TEAction |-> [
   position |-> 7,
   name |-> "Increment",
   location |-> "line 55, col 20 to line 58, col 49 of module counter_incrementer"
 ],
counter |-> 1,
goal |-> 3,
local |-> <<0, 0, 0>>,
pc |-> <<"Done", "Done", "Done">>
],
<Stuttering>
>>
```

case 2:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 22
DistinctStates == 16

(* TLC Errors *)
Error == "no"
```


# 8 Data Structures
When we want to write a specification involving some data structure, we need some sort of definition of the data structure.
Further, we need one that's independent of the algorithm.

Use the *linked list* as the example: module `LinkedLists.tla`.

> [!quote] write data structures as separate modules
>
> When making a new specification for this, do not make `LinkedLists.tla` the root file, instead, make the root file something else, sunch as `main.tla`, then add `LinkedLists.tla` as a secondary module.
>
> 'File' - 'Open Module' - 'Add TLA+ Module'.

A linked list (LL) is a low-level data structure where each element (node) of the LL is a data structure containing the data and a pointer to the next node.
The last node in the list points to a null element, which is how we know it's the last one.
If the *last* element point to an earlier element, this is called having a *cycle*.

In TLA+, we generally *represent data structures as functions or structures*.
By convention, the module should have a `LinkedLists(Nodes)` operator that generates all matching functions where `Nodes` is the set of memory addresses.

> [!example] LinkedLists.tla
```TLA+ title="LinkedLists.tla"
---------- MODULE LinkedLists ----------
CONSTANT NULL

LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Sequences
LOCAL INSTANCE TLC
LOCAL INSTANCE Integers

LOCAL PointerMaps(Nodes) == [Nodes -> Nodes \union {NULL}]

LOCAL Range(f) == {f[x]: x \in DOMAIN f}

LOCAL isLinkedList(PointerMap) ==
LET
nodes == DOMAIN PointerMap
all_seqs == [1..Cardinality(nodes) -> nodes]
IN \E ordering \in all_seqs:
\* each node points to the next node in the ordering
/\ \A i \in 1..Len(ordering)-1:
PointerMap[ordering[i]] = ordering[i+1]
\* all nodes in the mapping appear in the ordering
/\ nodes \subseteq Range(ordering)

LinkedLists(Nodes) ==
IF NULL \in Nodes 
THEN Assert(FALSE, "NULL cannot be in Nodes")
ELSE
LET
node_subsets == (SUBSET Nodes \ {{}})
\* a set of set of functions
pointer_maps_sets == {PointerMaps(subn): subn \in node_subsets}
all_pointer_maps == UNION pointer_maps_sets
IN {pm \in all_pointer_maps: isLinkedList(pm)}

\* CHOOSE ll \in LinkedLists({"a", "b"}): {"a", "b"} \subseteq Range(ll)
\* [a |-> "b", b |-> "a"]


Cyclic(LL) == NULL \notin Range(LL)
Ring(LL) == (DOMAIN LL = Range(LL))

\* CHOOSE ll \in LinkedLists({"a", "b"}): Cyclic(ll) /\ ~Ring(ll)
\* [a |-> "a", b |-> "a"]

First(LL) ==
IF Ring(LL)
THEN CHOOSE node \in DOMAIN LL: TRUE
ELSE CHOOSE node \in DOMAIN LL: node \notin Range(LL)
===============================
```
## 8.1 Validation
See next.
## 8.2 Example
> [!example] Tortoise and the Hare algorithm
>
>Start 2 iterators, a slow *tortoise* and a fast *hare* at the beginning of the LL.
>At every step, we move the tortoise one node and the hare two nodes.
>
>If the two pointers ever land on the same node, the LL has a cycle.
```TLA+ title="tortoise_and_hare.tla"
---------- MODULE tortoise_and_hare ----------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANTS Nodes, NULL
\* NULL <- [ model value ]
\* Nodes <- [ model value ] {a, b, c, d}
INSTANCE LinkedLists WITH NULL <- NULL

AllLinkedLists == LinkedLists(Nodes)

CycleImpilesTwoParents(ll) ==
Cyclic(ll) <=>
\/ Ring(ll)
\/ \E n \in DOMAIN ll:
Cardinality({p \in DOMAIN ll: ll[p] = n}) = 2

Valid ==
/\ \A ll \in AllLinkedLists:
/\ Assert(CycleImpilesTwoParents(ll), <<"Counterexample:", ll>>)

\* Valid
\* TRUE

(* detect cycles in linked lists. *)
(*--fair algorithm tortoise_and_hare
variables
ll \in LinkedLists(Nodes),
tortoise = First(ll),
hare = tortoise;

macro advance(pointer) begin
pointer := ll[pointer];
if pointer = NULL then
assert ~Cyclic(ll);
goto Done;
end if
end macro;

begin
while TRUE do
advance(tortoise);
advance(hare);
advance(hare);
if tortoise = hare then
assert Cyclic(ll);
goto Done;
end if;
end while;
end algorithm; *)
===============================
```

```
NULL <- [ model value ]
Nodes <- [ model value ] {a, b, c, d}
```

'Model Overview' - 'What to check?' - 'Properties' - 'Termination'.

result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 2248
DistinctStates == 2028

(* TLC Errors *)
Error == "no"
```


# 9 State Machines
Specifications are more expressive than code, it's not always clear how to go from a specification to reality.

A technique for handling this is to write a very abstract spec, and expand it into a more detailed lower-level *implementation* that is closer to the program that will be writing.
One common pattern for doing this is to use a **state machine**.

## 9.1 State Machines

A *state machine* is a system with a finite set of internal *states* along with a set of *transitions* between states.
outside *events* can trigger these transitions.

we can write the state machine as a giant `either-or` chain.

> [!example] "door1: open/closed, locked/unlocked"
```TLA+
(* A door may be locked or unlocked, 
   and it may be open or closed. 
   
   we can only open an unlocked door.
*)

(*--algorithm door1
variables
    open = FALSE,
    locked = FALSE;
    
begin
    Event:
        either  \* unlock
            await locked;
            locked := FALSE;
        or      \* lock
            await ~locked;
            locked := TRUE;
        or      \* open
            await ~locked;
            await ~open;
            open := TRUE;
        or      \* close
            await open;
            open := FALSE;
        end either;
    goto Event; \* loop
end algorithm; *)
```
result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 8
DistinctStates == 4

(* TLC Errors *)
Error == "no"
```

> [!example] "door2: add key"
```TLA+
(* A door may be locked or unlocked, 
   and it may be open or closed. 
   
   we can only open an unlocked door.
*)

(* If the door is closed, we need a key to lock or unlock it.
   If the door is open, we can lock and unlock it without the key.
*)

(*--algorithm door2
variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;
    
begin
    Event:
        either  \* unlock
            await locked /\ (open \/ key);
            locked := FALSE;
        or      \* lock
            await ~locked /\ (open \/ key);
            locked := TRUE;
        or      \* open
            await ~locked /\ ~open;
            open := TRUE;
        or      \* close
            await open /\ ~locked;
            open := FALSE;
        end either;
    goto Event; \* loop
end algorithm; *)
```
result:
```TLA+ linenums="1" hl_lines="25 28"
(* Model Checking Results *)
StatesFound == 14
DistinctStates == 7

(* TLC Errors *)
Error == "no"
```

> [!example] "door: add process"
```TLA+
(*--algorithm door
variables
    open = FALSE,
    locked = FALSE,
    key \in BOOLEAN;

process open_door = "Open Door"
begin
    OpenDoor:
        await open;
        either  \* lock/unlock
            locked := ~locked;
        or      \* close
            await ~locked;
            open := FALSE;
        end either;
    goto OpenDoor; \* loop
end process;


process closed_door = "Closed Door"
begin
    ClosedDoor:
        await ~open;
        either  \* lock/unlock
            await key;
            locked := ~locked;
        or      \* open
            await ~locked;
            open := TRUE;
        end either;
    goto ClosedDoor;
end process;

end algorithm; *)
```
result:
```TLA+ linenums="1" hl_lines="25 28"
(* Model Checking Results *)
StatesFound == 12
DistinctStates == 7

(* TLC Errors *)
Error == "no"
```

## 9.2 Scaffolding Implementations

Most real-life problem are not explicitly state machines, but can be abstractly specified as state machines.
Then we can implement our spec *off that state machine*, filling in the details on how the transitions are actually implemented in code and making sure it preserves the same invariants.

> [!quote] "Refinement"
>
>TLA+ formalizes the concept of scaffolding with *refinement*.
>We refine a spec by writing a second, more detailed spec and showing that every valid behavior of the detailed spec is also a valid behavior of the general spec.

But this requires some tooling we donot have access to in PlusCal.

example: a simple data pattern, some clients can read from and write to a databse.

1. first specify this as a state machine without a database.
2. then progress to a more-detailed one that more accurately model how, exeactly the clients *read* and *write*.

> [!example] "database: as a state machine"
```TLA+
EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients
\* Clients <- [ model value ] {c1}
\* NULL    <- [ model value ]
\* Data    <- [ model value ] {d1, d2}

(*--algorithm database1
variables
    db_value \in Data;

process clients \in Clients
variables
    result = NULL;

begin
    Client:
        either  \* read
            result := db_value;
            assert result = db_value;
        or      \* write
            with d \in Data do
                db_value := d;
            end with;
        end either;
        goto Client; \* loop
end process;
end algorithm; *)
```   
result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 20
DistinctStates == 6

(* TLC Errors *)
Error == "no"
``` 

> [!example] "database: with more details"
```TLA+
(* client show communicate with the database for reading and writing. *)

EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients
\* Clients <- [ model value ] {c1}
\* NULL    <- [ model value ]
\* Data    <- [ model value ] {d1, d2}

(*--algorithm database
variables
    query = [c \in Clients |-> NULL],
    db_value \in Data;
    
define
    Exists(val) == val /= NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
    query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;

process clients \in Clients
variables
    result = NULL;
begin
    Request:
        while TRUE do
            either  \* read
                request([request |-> "read"]);
                Confirm:
                    wait_for_response();
                    result := query[self].result;
                assert result = db_value;
            or      \* write
                with d \in Data do
                    request([request |-> "write", data |-> d]);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;
end process;

process database = "Database"
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            if q.request = "write" then
                db_value := q.data;
            elsif q.request = "read" then
                skip;
            else
                assert FALSE;
            end if;
            query[client] := [type |-> "response", result |-> db_value];
        end with;
    goto DB; \* loop
end process;

end algorithm; *)
```
result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 56
DistinctStates == 38

(* TLC Errors *)
Error == "no"
```

## 9.3 Ghost Variables

Contextual data that we track to *verify invariants* is called **auxiliary**, or **ghost** data.
we can also have ghost operators, ghost processes, etc.

> [!example] "database: with ghost variables"
```TLA+
(* client show communicate with the database for reading and writing. *)

(* using ghost data: client receives that data at the time of the request. *)

EXTENDS Integers, Sequences, TLC
CONSTANTS Data, NULL, Clients
\* Clients <- [ model value ] {c1}
\* NULL    <- [ model value ]
\* Data    <- [ model value ] {d1, d2}

(*--algorithm database_g
variables
    query = [c \in Clients |-> NULL],
    ghost_db_history = [c \in Clients |-> NULL];
    
define
    Exists(val) == val /= NULL
    RequestingClients == {c \in Clients: Exists(query[c]) /\ query[c].type = "request"}
end define;

macro request(data) begin
    query[self] := [type |-> "request"] @@ data;
end macro;

macro wait_for_response() begin
    await query[self].type = "response";
end macro;

process clients \in Clients
variables
    result = NULL;
begin
    Request:
        while TRUE do
            either  \* read
                request([request |-> "read"]);
                Confirm:
                    wait_for_response();
                    result := query[self].result;
                assert result = ghost_db_history[self];
            or      \* write
                with d \in Data do
                    request([request |-> "write", data |-> d]);
                end with;
                Wait:
                    wait_for_response();
            end either;
        end while;
end process;

process database = "Database"
variables
    db_value \in Data;
begin
    DB:
        with client \in RequestingClients, q = query[client] do
            if q.request = "write" then
                db_value := q.data;
            elsif q.request = "read" then
                skip;
            else
                assert FALSE;
            end if;
            ghost_db_history[client] := db_value;
            query[client] := [type |-> "response", result |-> db_value];
        end with;
    goto DB; \* loop
end process;

end algorithm; *)
```
result:
```TLA+ linenums="1"
(* Model Checking Results *)
StatesFound == 62
DistinctStates == 44

(* TLC Errors *)
Error == "no"
``` 


# 10 Business Logic
## 10.1 The Requirements
### 10.1.1 Adding Invariants
### 10.1.2 Adding Liveness
## 10.2 Adding Reservations
### 10.2.1 Updating Assumptions
### 10.2.2 Expiring Reservations

# 11 MapReduce
## 11.1 Problem Overview
## 11.2 Part One: Basics
## 11.3 Part Two: Liveness
## 11.4 Part Three: Statuses
## 11.5 Exercise

# A Math
## A.1 Propositional Logic
### A.1.1 Evaluating Propositions in TLA+
## A.2 Sets
## A.3 Predicate Logic
### A.3.1 Evaluating Predicates in TLA+

# B The PT Module


# C PlusCal to TLA+
## C.1 Temporal Logic
## C.2 Actions
## C.3 TLA
## C.4 Limitations of PlusCal

