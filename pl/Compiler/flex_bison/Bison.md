# Bison
* https://www.gnu.org/software/bison/

Bison is a general-purpose parser generator that converts an annotated context-free grammar into a deterministic LR or generalized LR (GLR) parser employing LALR(1) parser tables. As an experimental feature, Bison can also generate IELR(1) or canonical LR(1) parser tables. Once you are proficient with Bison, you can use it to develop a wide range of language parsers, from those used in simple desk calculators to complex programming languages.

Bison is upward compatible with Yacc: all properly-written Yacc grammars ought to work with Bison with no change. Anyone familiar with Yacc should be able to use Bison with little trouble. You need to be fluent in C or C++ programming in order to use Bison. Java is also supported as an experimental feature.

# Manual

## 1 Bison文法的结构

Bison文法由三部分构成: 定义段、规则段和用户例程段

```
<definition section>
%%
<rules section>
%%
<user subroutines>
```

各段之间用`%%`分隔. 前两个段是必须的, 段可以为空. 第三段和前缀的`%%`可以省略.

### 1.1 符号

bison文法是从符号(symbol)构造的, 符号是文法的单词(word). 符号是字符、数字、`.`和`_`的序列, 不以数字开始. 符号错误被保留用于错误恢复, 否则bison不会给任何符号附加固定的含义.

由词法器产生的符号称为终结符号(terminal symbol)或token. 在规则LHS定义的符号称为非终结符号(nonterminal symbols或nonterminals).

token可以是`""`包裹的字面量字符串. 一个广泛采用的约定是token名称全大写, 非终结符号全小写. 本书中采用这一约定.

### 1.2 定义段
### 1.3 规则段
### 1.4 用户例程段

## 2 Actions
### 2.1 Embedded Actions
### 2.2 Symbol Types for Embedded Actions

## 3 Ambiguity and Conflicts
### 3.1 Types of Conflicts
### 3.2 Shift/Reduce Conflicts
### 3.3 Reduce/Reduce Conflicts
### 3.4 %expect
### 3.5 GLR Parsers

## 4 Bugs in Bison Programs
### 4.1 Infinite Recursion
### 4.2 Interchanging Precedence
### 4.3 Embedded Actions

## 5 C++ Parsers

## 6 %code Blocks

## 7 End Marker

## 8 Error Token and Error Recovery
### 8.1 %destructor

## 9 Inherited Attributes ($0)
### 9.1 Symbol Types for Inherited Attributes

## 10 %initial-action

## 11 Lexical Feedback

## 12 Literal Block

## 13 Literal Tokens

## 14 Locations

## 15 %parse-param

## 16 Portability of Bison Parsers
### 16.1 Porting Bison Grammars
### 16.2 Porting Generated C Parsers
### 16.3 Libraries
### 16.4 Character Codes

## 17 Precedence and Associativity Declarations
### 17.1 Precedence
### 17.2 Associativity
### 17.3 Precedence Declarations
### 17.4 Using Precedence and Associativity to Resolve Conflicts
### 17.5 Typical Uses of Precedence

## 18 Recursive Rules
### 18.1 Left and Right Recursion

## 19 Rules

## 20 Special Characters

## 21 %start Declaration

## 22 Symbol Values
### 22.1 Declaring Symbol Types
### 22.2 Explicit Symbol Types

## 23 Tokens
### 23.1 Token Numbers
### 23.2 Token Values
### 23.3 %type Declaration
### 23.4 %union Declaration

## 24 Variant and Multiple Grammars
### 24.1 Combined Parsers

## 25 Multiple Parsers
### 25.1 Using %name-prefix or the -p Flag
### 25.2 Lexers for Multiple Parsers
### 25.3 Pure Parsers

## 26 y.output Files

## 27 Bison Library
### 27.1 main()
### 27.2 yyerror()

## 28 YYABORT

## 29 YYACCEPT

## 30 YYBACKUP

## 31 yyclearin

## 32 yydebug and YYDEBUG
### 32.1 YYDEBUG
### 32.2 yydebug

## 33 yyerrok

## 34 YYERROR

## 35 yyerror()

## 36 yyparse()

## 37 YYRECOVERING()

# See Also
* [Yacc](https://en.wikipedia.org/wiki/Yacc)