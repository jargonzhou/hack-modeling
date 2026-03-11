# LSP: Language Server Protocol
* https://microsoft.github.io/language-server-protocol/
* [Language Server Protocol Specification - 3.17](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/)
  * [Meta Model of the LSP protocol](https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#metaModel): Since 3.17 there is a meta model describing the LSP protocol.

> The Language Server Protocol (LSP) defines the protocol used between an editor or IDE and a language server that provides language features like auto complete, go to definition, find all references etc. The goal of the Language Server Index Format (LSIF, pronounced like "else if") is to support rich code navigation in development tools or a Web UI without needing a local copy of the source code.

# Participants

1. Language Server: prodive language-specific smarts inside a server.
2. Development Tools: provide features like autocomplete, goto definition, documentation on hover for a programming language.
3. Language Server Protocol(LSP): The communication protocol for IPC among **Language Servers** and **Development Tools**.

demonstration usages:

![](https://microsoft.github.io/language-server-protocol/overviews/lsp/img/language-server-sequence.png)

![](https://microsoft.github.io/language-server-protocol/overviews/lsp/img/language-server.png)

# The LSP Specification

* protocol definition
  * Message
  * shared JSON Structures
* document synchronization
* features
  * Language
  * Workspace
  * Window
