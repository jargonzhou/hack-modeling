# YAML
* https://yaml.org/

> YAML(YAML Ain't Markup Language™) - [wikipedia](https://en.wikipedia.org/wiki/YAML)
> 
> YAML (/ˈjæməl/) is a human-readable data serialization language. It is commonly used for configuration files and in applications where data are being stored or transmitted. YAML targets many of the same communications applications as Extensible Markup Language (XML) but has a minimal syntax that intentionally differs from Standard Generalized Markup Language (SGML). It uses Python-style indentation to indicate nesting and does not require quotes around most string values (it also supports JSON style `[...]` and `}` mixed in the same file).

# Revision 1.2.2 (2021-10-01)
* https://yaml.org/spec/1.2.2

## 1. Introduction to YAML
- 1.1. Goals
- 1.2. YAML History
- 1.3. Terminology
## 2. Language Overview
- 2.1. Collections/集合
- 2.2. Structures/结构
- 2.3. Scalars/标量
- 2.4. Tags/标记
- 2.5. Full Length Example
## 3. Processes and Models/处理和模型
- 3.1. Processes
  - 3.1.1. Dump
  - 3.1.2. Load
- 3.2. Information Models/信息模型
  - 3.2.1. **Representation** Graph/表示图
    - 3.2.1.1. Nodes
    - 3.2.1.2. Tags
    - 3.2.1.3. Node Comparison
  - 3.2.2. **Serialization** Tree/序列化树
    - 3.2.2.1. Mapping Key Order
    - 3.2.2.2. Anchors and Aliases
  - 3.2.3. **Presentation** Stream/演示流
    - 3.2.3.1. Node Styles
    - 3.2.3.2. Scalar Formats
    - 3.2.3.3. Comments
    - 3.2.3.4. Directives
- 3.3. Loading Failure Points
  - 3.3.1. Well-Formed Streams and Identified Aliases
  - 3.3.2. Resolved Tags
  - 3.3.3. Recognized and Valid Tags
  - 3.3.4. Available Tags
## 4. Syntax Conventions/语法约定
- 4.1. Production Syntax/产生式语法
- 4.2. Production Parameters/产生式参数
- 4.3. Production Naming Conventions
## 5. Character Productions/字符产生式
- 5.1. Character Set
- 5.2. Character Encodings
- 5.3. Indicator Characters
- 5.4. Line Break Characters
- 5.5. White Space Characters
- 5.6. Miscellaneous Characters
- 5.7. Escaped Characters
## 6. Structural Productions/结构产生式
- 6.1. Indentation Spaces
- 6.2. Separation Spaces
- 6.3. Line Prefixes
- 6.4. Empty Lines
- 6.5. Line Folding
- 6.6. Comments
- 6.7. Separation Lines
- 6.8. Directives
  - 6.8.1. “YAML” Directives
  - 6.8.2. “TAG” Directives
    - 6.8.2.1. Tag Handles
    - 6.8.2.2. Tag Prefixes
- 6.9. Node Properties
  - 6.9.1. Node Tags
  - 6.9.2. Node Anchors
## 7. Flow Style Productions/流风格产生式
- 7.1. Alias Nodes
- 7.2. Empty Nodes
- 7.3. Flow Scalar Styles
  - 7.3.1. Double-Quoted Style
  - 7.3.2. Single-Quoted Style
  - 7.3.3. Plain Style
- 7.4. Flow Collection Styles
  - 7.4.1. Flow Sequences
  - 7.4.2. Flow Mappings
- 7.5. Flow Nodes
## 8. Block Style Productions/块风格产生式
- 8.1. Block Scalar Styles
  - 8.1.1. Block Scalar Headers
    - 8.1.1.1. Block Indentation Indicator
    - 8.1.1.2. Block Chomping Indicator
  - 8.1.2. Literal Style
  - 8.1.3. Folded Style
- 8.2. Block Collection Styles
  - 8.2.1. Block Sequences
  - 8.2.2. Block Mappings
  - 8.2.3. Block Nodes
## 9. Document Stream Productions/文档流产生式
- 9.1. Documents
  - 9.1.1. Document Prefix
  - 9.1.2. Document Markers
  - 9.1.3. Bare Documents
  - 9.1.4. Explicit Documents
  - 9.1.5. Directives Documents
- 9.2. Streams
## 10. Recommended Schemas/推荐的模式
- 10.1. Failsafe Schema/安全失败模式
  - 10.1.1. Tags
    - 10.1.1.1. Generic Mapping
    - 10.1.1.2. Generic Sequence
    - 10.1.1.3. Generic String
  - 10.1.2. Tag Resolution
- 10.2. JSON Schema/JSON模式
  - 10.2.1. Tags
    - 10.2.1.1. Null
    - 10.2.1.2. Boolean
    - 10.2.1.3. Integer
    - 10.2.1.4. Floating Point
  - 10.2.2. Tag Resolution
- 10.3. Core Schema/核心模式
  - 10.3.1. Tags
  - 10.3.2. Tag Resolution
- 10.4. Other Schemas/其他模式

# See Also

Tutorials
* [YAML Tutorial : A Complete Language Guide with Examples](https://spacelift.io/blog/yaml) - 2024-09
* [What is YAML?](https://www.redhat.com/en/topics/automation/what-is-yaml) - 2023-03, used in Ansible, Kubernetes
> A common question for YAML beginners is “What do the 3 dashes mean?” 3 dashes (`---`) are used to signal the start of a document, while each document ends with three dots (`...`). 

multiline wrap without space
* [YAML multiline wrap without space](https://stackoverflow.com/questions/19168734/yaml-multiline-wrap-without-space)
```yaml
"abcdefghi\
jklmnopqr\
stuvwxyz"
```