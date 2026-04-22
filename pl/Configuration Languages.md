# Configuration Languages
* [Domain-specific language - wikipedia](https://en.wikipedia.org/wiki/Domain-specific_language)
* [A reasonable configuration language](https://news.ycombinator.com/item?id=39250320)



# Dhall
* https://dhall-lang.org/

> The Dhall configuration language
> 
> Dhall is a programmable configuration language that you can think of as: JSON + functions + types + imports

# HCL
* https://github.com/hashicorp/hcl

> HCL is the HashiCorp configuration language.
> 
> HCL is a toolkit for creating structured configuration languages that are both human- and machine-friendly, for use with command-line tools. Although intended to be generally useful, it is primarily targeted towards devops tools, servers, etc.

# HOCON
* https://github.com/lightbend/config
* [Specification](https://github.com/lightbend/config/blob/master/HOCON.md)

> HOCON (Human-Optimized Config Object Notation)
> 
> Configuration library for JVM languages.

# INI
[INI file - wikipedia](https://en.wikipedia.org/wiki/INI_file)

> An INI file is a configuration file for computer software that consists of a text-based content with a structure and syntax comprising key–value pairs for properties, and sections that organize the properties.[1] The name of these configuration files comes from the filename extension INI, for initialization, used in the MS-DOS operating system which popularized this method of software configuration. The format has become an informal standard in many contexts of configuration, but many applications on other operating systems use different file name extensions, such as conf and cfg.

# JSON
* [JSON - wikipedia](https://en.wikipedia.org/wiki/JSON), supersets:
	- [YAML](https://yaml.org/)
	- CSON
	- [HOCON (Human-Optimized Config Object Notation)](https://github.com/lightbend/config/blob/master/HOCON.md)
	- JSON5
	- JSONC

# Pkl
* https://pkl-lang.org/index.html

> Pkl — pronounced Pickle — is an embeddable configuration language which provides rich support for data templating and validation. It can be used from the command line, integrated in a build pipeline, or embedded in a program. Pkl scales from small to large, simple to complex, ad-hoc to repetitive configuration tasks.

# Starlark
* https://github.com/bazelbuild/starlark
* [Starlark Language Specification](https://github.com/bazelbuild/starlark/blob/master/spec.md)

> Starlark (formerly known as Skylark) is a language intended for use as a configuration language. It was designed for the [Bazel](https://bazel.build/) build system, but may be useful for other projects as well. This repository is where Starlark features are proposed, discussed, and specified. It contains information about the language, including the [specification](https://github.com/bazelbuild/starlark/blob/master/spec.md). There are [multiple implementations of Starlark](https://github.com/bazelbuild/starlark/blob/master/users.md).
>
> Starlark is a dialect of [Python](https://www.python.org/). Like Python, it is a dynamically typed language with high-level data types, first-class functions with lexical scope, and garbage collection. Independent Starlark threads execute in parallel, so Starlark workloads scale well on parallel machines. Starlark is a small and simple language with a familiar and highly readable syntax. You can use it as an expressive notation for structured data, defining functions to eliminate repetition, or you can use it to add scripting capabilities to an existing application.
> 
> A Starlark interpreter is typically embedded within a larger application, and the application may define additional domain-specific functions and data types beyond those provided by the core language. For example, Starlark was originally developed for the Bazel build tool. Bazel uses Starlark as the notation both for its BUILD files (like Makefiles, these declare the executables, libraries, and tests in a directory) and for its macro language, through which Bazel is extended with custom logic to support new languages and compilers.


# TOML
* [TOML](https://toml.io/en/): Tom's Obvious Minimal Language

> TOML: A config file format for humans.
TOML aims to be a minimal configuration file format that's easy to read due to obvious semantics. TOML is designed to map unambiguously to a hash table. TOML should be easy to parse into data structures in a wide variety of languages.

see [Even Better TOML](https://github.com/tamasfe/taplo) in [Python tools - Poetry](https://github.com/jargonzhou/learning-python/blob/main/tools/poetry/Poetry.md) 

# YAML
* [YAML](./confLang/YAML.md)