# SDKMAN!
* https://sdkman.io/

> The Software Development Kit Manager
>
> Meet SDKMAN! – your reliable companion for effortlessly managing multiple Software Development Kits on Unix systems. Imagine having different versions of SDKs and needing a stress-free way to switch between them. SDKMAN! steps in with its easy-to-use Command Line Interface (CLI) and API. Formerly known as GVM, the Groovy enVironment Manager, SDKMAN! draws inspiration from familiar tools like apt, pip, RVM, and rbenv and even Git. Think of it as your helpful toolkit friend, ready to streamline SDK management for you.

# Usages
## Windows

use Git Bash:

ZX

```shell
$ sdk list java
$ sdk install 21.0.5-tem
$ sdk default java 17.0.9-tem

$ sdk install ant
$ sdk install maven
$ sdk install gradle
```

offline mode:

ZX

```shell
$ sdk offline enable
Offline mode enabled.

$ sdk list java
--------------------------------------------------------------------------------
Offline: only showing installed java versions
--------------------------------------------------------------------------------
 * 8.0.402-tem
 * 17.0.9-tem
 * 17.0.9-graalce
 * 11.0.22-tem
--------------------------------------------------------------------------------
* - installed
> - currently in use
--------------------------------------------------------------------------------

$ sdk offline disable
Online mode re-enabled!
```