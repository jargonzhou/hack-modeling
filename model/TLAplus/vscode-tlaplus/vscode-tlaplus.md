# vscode-tlaplus
- https://github.com/tlaplus/vscode-tlaplus

TLA+ for Visual Studio Code:
- TLA+: Parse module
- TLA+: Check model with TLC
- TLA+: Evaluate expression...

Convention:
- `VSCODE_TLAPLUS_PATH`: ex `c:\Users\zhouj\.vscode\extensions\alygin.vscode-tlaplus-1.5.4`.

## CommunityModules
- https://github.com/tlaplus/CommunityModules
- CommunityModules.tla

Java options:
```shell
# release: 202405171516
-cp $VSCODE_TLAPLUS_PATH/tools/CommunityModules.jar:$VSCODE_TLAPLUS_PATH/tools/CommunityModules-deps.jar
```

Replace `xxx\tla2tools.jar` with release [v1.8.0](https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar).

## Other Modules
- ThirdModules.tla

ex: [PT.tla](https://github.com/Apress/practical-tla-plus/blob/master/PT/PT.tla)

Java options:
```shell
# https://github.com/tlaplus/tlaplus/issues/374
# https://github.com/tlaplus/CommunityModules
# Put PT.tla in the following folder
-DTLA-Library=$VSCODE_TLAPLUS_PATH/lib
```
