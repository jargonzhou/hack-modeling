# Gradle
* https://gradle.org/
* https://github.com/gradle/gradle

> Gradle is a highly scalable build automation tool designed to handle everything from large, multi-project enterprise builds to quick development tasks across various languages. Gradle’s modular, performance-oriented architecture seamlessly integrates with development environments, making it a go-to solution for building, testing, and deploying applications on Java, Kotlin, Scala, Android, Groovy, C++, and Swift.

books
* Benjamin Muschko. **Gradle in Action**. Manning Publications: 2014.

UML
* [gradle.uxf](./gradle.uxf)

# Skaffold

Installation with sdkman
```shell
$ sdk install gradle

$ gradle --version

------------------------------------------------------------
Gradle 8.12.1
------------------------------------------------------------

Build time:    2025-01-24 12:55:12 UTC
Revision:      0b1ee1ff81d1f4a26574ff4a362ac9180852b140

Kotlin:        2.0.21
Groovy:        3.0.22
Ant:           Apache Ant(TM) version 1.10.15 compiled on August 25 2024
Launcher JVM:  17.0.9 (Eclipse Adoptium 17.0.9+9)
Daemon JVM:    C:\Users\zhouj\.sdkman\candidates\java\current (no JDK specified, using current Java home)
OS:            Windows 11 10.0 amd64
```

Create project
```shell
$ mkdir example
$ cd example

$ gradle init

Select type of build to generate:
  1: Application
  2: Library
  3: Gradle plugin
  4: Basic (build structure only)
Enter selection (default: Application) [1..4] 1

Select implementation language:
  1: Java
  2: Kotlin
  3: Groovy
  4: Scala
  5: C++
  6: Swift
Enter selection (default: Java) [1..6] 1

Enter target Java version (min: 7, default: 21): 17

Project name (default: example):

Select application structure:
  1: Single application project
  2: Application and library project
Enter selection (default: Single application project) [1..2] 2

Select build script DSL:
  1: Kotlin
  2: Groovy
Enter selection (default: Kotlin) [1..2] 2

Generate build using new APIs and behavior (some features may change in the next minor release)? (default: no) [yes, no]
```
```shell
$ tree
.
|-- app
|   |-- build.gradle
|   `-- src
|       |-- main
|       |   |-- java
|       |   |   `-- org
|       |   |       `-- example
|       |   |           `-- app
|       |   |               |-- App.java
|       |   |               `-- MessageUtils.java
|       |   `-- resources
|       `-- test
|           |-- java
|           |   `-- org
|           |       `-- example
|           |           `-- app
|           |               `-- MessageUtilsTest.java
|           `-- resources
|-- build
|   `-- reports
|       |-- configuration-cache
|       |   |-- 1lvm5i0qp88860746eg0kfcef
|       |   |   `-- d7z3rnkck05xxhfh21hng5u0f
|       |   |       `-- configuration-cache-report.html
|       |   `-- 4zqv8ruffwk50ac86un023k8p
|       |       `-- 3khmy9wg0e61aifrn37cv26nb
|       |           `-- configuration-cache-report.html
|       `-- problems
|           `-- problems-report.html
|-- buildSrc
|   |-- build.gradle
|   |-- settings.gradle
|   `-- src
|       `-- main
|           `-- groovy
|               |-- buildlogic.java-application-conventions.gradle
|               |-- buildlogic.java-common-conventions.gradle
|               `-- buildlogic.java-library-conventions.gradle
|-- gradle
|   |-- libs.versions.toml
|   `-- wrapper
|       |-- gradle-wrapper.jar
|       `-- gradle-wrapper.properties
|-- gradle.properties
|-- gradlew
|-- gradlew.bat
|-- list
|   |-- build.gradle
|   `-- src
|       |-- main
|       |   |-- java
|       |   |   `-- org
|       |   |       `-- example
|       |   |           `-- list
|       |   |               `-- LinkedList.java
|       |   `-- resources
|       `-- test
|           |-- java
|           |   `-- org
|           |       `-- example
|           |           `-- list
|           |               `-- LinkedListTest.java
|           `-- resources
|-- settings.gradle
`-- utilities
    |-- build.gradle
    `-- src
        |-- main
        |   |-- java
        |   |   `-- org
        |   |       `-- example
        |   |           `-- utilities
        |   |               |-- JoinUtils.java
        |   |               |-- SplitUtils.java
        |   |               `-- StringUtils.java
        |   `-- resources
        `-- test
            `-- resources

52 directories, 26 files
```

# Getting Started

Gradle for Software Engineers
- 1. Learn how to run Gradle Builds/运行Gradle构建
  - 1. Core Concepts
  - 2. Wrapper Basics
  - 3. Command Line Interface Basics
  - 4. Settings File Basics
  - 5. Build Files Basics
  - 6. Dependencies and Dependency Management Basics
  - 7. Tasks Basics
  - 8. Incremental Builds and Build Caching Basics
  - 9. Plugins Basics
  - 10. Build Scan
- 2. Beginner Gradle Tutorial/入门教程
  - 1. Initializing the Project
  - 2. Running Tasks
  - 3. Understanding Dependencies
  - 4. Applying Plugins
  - 5. Exploring Incremental Builds
  - 6. Enabling the Cache

Gradle for Build Engineers
- 1. Learn how to write Gradle scripts/编写Gradle脚本
  - 1. Anatomy of a Gradle Build
  - 2. Structuring Multi-Project Builds
  - 3. Gradle Build Lifecycle
  - 4. Writing Build Scripts
  - 5. Gradle Managed Types
  - 6. Declaring and Managing Dependencies
  - 7. Creating and Registering Tasks
  - 8. Working With Plugins
- 2. Intermediate Gradle Tutorial/中级教程
  - 1. Initializing the Project
  - 2. Understanding the Build Lifecycle
  - 3. Multi-Project Builds
  - 6. Writing the Settings File
  - 5. Writing Build Scripts
  - 6. Writing Tasks
  - 7. Writing Plugins

Gradle for Plugin Developers
- 1. Learn how to develop Gradle Plugins/开发Gradle插件
  - 1. Plugin Introduction
  - 2. Pre-Compiled Script Plugins
  - 3. Binary Plugins
  - 4. Binary Plugin Development
  - 5. Binary Plugin Publishing
- 2. Advanced Gradle Tutorial/高级教程
  - 1. Initializing the Project
  - 2. Adding an Extension
  - 3. Creating a Custom Task
  - 6. Writing a Unit Test
  - 5. Adding a DataFlow Action
  - 6. Writing a Functional Test
  - 7. Using a Consumer Project
  - 8. Publishing the Plugin

# Gradle Fundamentals

* [Settings File Basics](https://docs.gradle.org/current/userguide/settings_file_basics.html): `settings.gradle(.kts)`
* [Build File Basics](https://docs.gradle.org/current/userguide/build_file_basics.html): `build.gradle(.kts)`

# Gradle Reference

* [Build Environment Configuration](https://docs.gradle.org/current/userguide/build_environment.html): `gradle.properties`

# Gradle plugins
* https://plugins.gradle.org/

