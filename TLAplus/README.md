# TLA+
- https://lamport.azurewebsites.net/tla/tla.html

Tools:
- TLA+ Toolbox
- vscode-tlaplus

TLA+ Template example:
```TLA+
---------------------- MODULE HourClock ----------------------
(************************************************************)
(* This module specifies ...                                *)
(************************************************************)
EXTENDS Naturals \* comments
VARIABLE hr
HCini == hr \in (1 .. 12)
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC == HCini /\ [][HCnxt]_hr
--------------------------------------------------------------
THEOREM HC => []HCini
==============================================================
```

TLA+ with PlusCal Template:
```TLA+
---- MODULE <module-name> ----
\* EXTENDS TLC, Integers, Sequences
\* CONSTANTS N

(**--algorithm <algorithm-name>
\* VarDecls
\* Definitions
\* Macro
\* Procedure
\* AlgorithmBody or Process
end algorithm;*)
====
```

Actions:
- [vscode-tlaplus](./vscode-tlaplus/README.md)
- [Practical TLA+](./PTLAplus/REAME.md)
