# ANTLR based language parsing

## Conventions

- put toy grammars in `src/main/grammar`.
- put complete grammars in `src/main/antlr4` and put in packages under `gen`.

## MySQL

文法: https://github.com/antlr/grammars-v4/tree/master/sql/mysql

大小写处理: [Case-Insensitive Lexing](https://github.com/antlr/antlr4/blob/master/doc/case-insensitive-lexing.md#custom-character-streams-approach)

## SPARQL

文法: https://github.com/antlr/grammars-v4/tree/master/sparql

## Java

文法: https://github.com/antlr/grammars-v4/tree/master/java/java

## FAQ

- antlr4-maven-plugin NOT generate visitor

run with:

```shell script
mvn antlr4:antlr4 -Dantlr4.visitor=true --debug

[DEBUG] -----------------------------------------------------------------------
[DEBUG] Goal:          org.antlr:antlr4-maven-plugin:4.7.1:antlr4 (default-cli)
[DEBUG] Style:         Regular
[DEBUG] Configuration: <?xml version="1.0" encoding="UTF-8"?>
<configuration>
  <atn default-value="false">${antlr4.atn}</atn>
  <forceATN default-value="false">${antlr4.forceATN}</forceATN>
  <generateTestSources default-value="false">${antlr4.generateTestSources}</generateTestSources>
  <inputEncoding>${project.build.sourceEncoding}</inputEncoding>
  <libDirectory default-value="${basedir}/src/main/antlr4/imports"/>
  <listener default-value="true">${antlr4.listener}</listener>
  <outputDirectory default-value="${project.build.directory}/generated-sources/antlr4"/>
  <outputEncoding>${project.build.sourceEncoding}</outputEncoding>
  <project>${project}</project>
  <sourceDirectory default-value="${basedir}/src/main/antlr4"/>
  <statusDirectory default-value="${project.build.directory}/maven-status/antlr4"/>
  <treatWarningsAsErrors default-value="false">${antlr4.treatWarningsAsErrors}</treatWarningsAsErrors>
  <visitor default-value="false">${antlr4.visitor}</visitor>
</configuration>

[DEBUG] Configuring mojo org.antlr:antlr4-maven-plugin:4.7.1:antlr4 from plugin realm ClassRealm[plugin>org.antlr:antlr4-maven-plugin:4.7.1, parent: sun.misc.Launcher$AppClassLoader@4e25154f]
[DEBUG] Configuring mojo 'org.antlr:antlr4-maven-plugin:4.7.1:antlr4' with basic configurator -->
[DEBUG]   (f) atn = false
[DEBUG]   (f) forceATN = false
[DEBUG]   (f) generateTestSources = false
[DEBUG]   (f) inputEncoding = UTF-8
[DEBUG]   (f) libDirectory = D:\workspace\learning-algorithms\codes\compiler\antlr\src\main\antlr4\imports
[DEBUG]   (f) listener = true
[DEBUG]   (f) outputDirectory = D:\workspace\learning-algorithms\codes\compiler\antlr\target\generated-sources\antlr4
[DEBUG]   (f) outputEncoding = UTF-8
[DEBUG]   (f) project = MavenProject: com.spike.antlr:antlr-examples:1.0-SNAPSHOT @ D:\workspace\learning-algorithms\codes\compiler\antlr\pom.xml
[DEBUG]   (f) sourceDirectory = D:\workspace\learning-algorithms\codes\compiler\antlr\src\main\antlr4
[DEBUG]   (f) statusDirectory = D:\workspace\learning-algorithms\codes\compiler\antlr\target\maven-status\antlr4
[DEBUG]   (f) treatWarningsAsErrors = false
[DEBUG]   (f) visitor = true
[DEBUG] -- end configuration --
```

- IDEA file size limit

`bin/idea.properties`:

```properties
#---------------------------------------------------------------------
# Maximum file size (kilobytes) IDE should provide code assistance for.
# The larger file is the slower its editor works and higher overall system memory requirements are
# if code assistance is enabled. Remove this property or set to very large number if you need
# code assistance for any files available regardless their size.
#---------------------------------------------------------------------
idea.max.intellisense.filesize=25000

#---------------------------------------------------------------------
# Maximum file size (kilobytes) IDE is able to open.
#---------------------------------------------------------------------
idea.max.content.load.filesize=200000
```