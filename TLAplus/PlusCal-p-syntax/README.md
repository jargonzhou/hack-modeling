# Code of 'A PlusCal User's Manaual - P-Syntax'

Actions:

- [Euclid.tla](./Euclid.tla): Euclid's algorithm.
  - `assert` check result, termination check.
- [FastMutex.tla](./FastMutex.tla): Fast Mutual Exclusion Algorithm.
  - example of multiprocess algorithm.

```c
// process i
// <...>: atomic operations/steps
// := means assignment
// /= and = means equality test

  ncs: noncritial section;
start: <b[i] := true>;
       <x := i>;
       if <y /= 0> then <b[i] := false>;
                        await <y = 0>;
                        goto start fi;
       <y := i>;
       if <x /= i> then <b[i] := false>;
                        for j := 1 to N do await <~b[j]> od;
                        if <y /= i> then await <y = 0>;
                                         goto start fi fi;
       critical section;
       <y := 0>;
       <b[i] := false>;
       goto ncs
```