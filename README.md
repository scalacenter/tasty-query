# TASTy Query

TASTy Query is a compiler-independent library to semantically analyze TASTy - an intermediate representation of Scala 3 code.

It scans the classpath to build a map of all definitions in a project, whether they are defined in Java, Scala 2 or Scala 3.
Its API allows users to query semantic information about the project:

* Find classes, methods, fields, and type definitions.
* Resolve symbol references.
* Inspect types, and make semantic operations on them such as type equivalence and subtyping.
* Follow overriding relationships across classes.

In addition, for Scala 3 code, it provides access to the full Trees, allowing for deeper inspection of the code.

## Usage

Add the following dependency to your build:

```scala
libraryDependencies += "ch.epfl.scala" %% "tasty-query" % "<latest-version>"
// or %%% from Scala.js
```

You can find the latest release in the Releases list on GitHub.

Head over to the [latest API docs](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery.html) to see what's available.
To get started, create a [`Classpath`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Classpaths$.html) using [`ClasspathLoaders.read`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/jdk/ClasspathLoaders$.html).
Please note that TASTy Query requires that all classes, such as the JRE, must be explicitly added to the classpath.
On the JDK versions >= 9, the JRE classpath can be obtained on the JVM platform with `FileSystems.getFileSystem(java.net.URI.create("jrt:/")).getPath("modules", "java.base")`.
On the JavaScript plaform the contents of this path need to be saved as a JAR file in the real file system.
Then, create a [`Context`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Contexts$$Context.html) object using [`Context.initialize(classpath)`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Contexts$$Context$.html#initialize-a22).
From there, follow the available methods to access [`Symbols`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Symbols$.html), [`Types`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Types$.html) and [`Trees`](https://javadoc.io/page/ch.epfl.scala/tasty-query_3/latest/tastyquery/Trees$.html).

## Motivation

### Preamble: TASTy and separate compilation

When compiling a codebase, a Scala compiler combines the source files of a project with the "binaries" of its dependencies.
Since the project source files can reference symbols (all kinds of definitions in a Scala program, like `val`s and `class`es) from the dependencies, the compiler builds a representation of the dependencies.

In Scala 2, this representation is limited to public definitions and their API-level types (also protected and package-private, but for the intent of this explanation, we refer to all of that as "public").
This information is stored in Scala 2 class files as "pickles".
The bodies of methods are excluded from this treatment.

In Scala 3, this representation is stored in so-called [TASTy files](https://docs.scala-lang.org/scala3/guides/tasty-overview.html).
They contain the complete AST of the program, with all their public definitions *and their bodies*.
Or to be precise, enough information is stored to be able to *reconstruct* everything (in particular, the types of subexpressions in method bodies).

This representation is used to type-check (and further "elaborate") the project source files.
In Scala 3, it is also used to process `inline def`s, which is why the full trees for method bodies are required.

### Definitions

* Symbol: the identity of any definition in a Scala or Java program.
  Examples include class definitions, local or member val/def definitions.
  There is only symbol per *definition*: multiple references to the same local val all refer to the same symbol.
* Tree: an Abstract Syntax Tree (AST) or a subtree thereof.
  In the context of tasty-query, they refer to TASTy trees, which carry their symbol and type information.
* Type: a type in a Scala program, such as `Int`, `List[String]` or `Bar { type Foo <: Baz[String] }`.
* Pickle: the public symbol and type information stored in Scala 2 binaries.
* Elaboration: the process of turning a Scala source program into a typed AST with TASTy-level information.
  Elaboration includes type inference, implicit resolution, overload resolution and macro expansion.
  It is the process that gives *semantics* (meaning) to a Scala program.
  Because of the nature of Scala, it is impossible to only *typecheck* a source program; it must be fully *elaborated*.
* TASTy: fully elaborated abstract syntax trees for Scala 3 programs.

### Reading TASTy files

[TASTy files](https://docs.scala-lang.org/scala3/guides/tasty-overview.html) are complex beasts.
They represent everything there is to know about the semantics of a Scala 3 program, as well as some non-semantic information (like positions).
Whereas Java class files can be read in isolation, and processed to some extent without knowing the classpath context, it is virtually impossible to make any sense of TASTy files without a full classpath.
There are several reasons for that, including the following:

* TASTy files inherently contains *cycles* between symbols, trees, and types.
* They leave some information implicit, to be reconstructed later, such as the type of most expression trees.

Reading TASTy files is therefore complex, and requires a full classpath to make sense of it.
The product is a multi-dimensional graph involving symbols, trees and types.

tasty-query's job is to read TASTy files for you, and present the information it contains (explicitly or implicitly) in as convenient a way as possible.

## Use cases

### TASTy-MiMa

In order to perform its job, [TASTy-MiMa](https://github.com/scalacenter/tasty-mima) needs to load TASTy files and extract semantic information out of them.
This is precisely what tasty-query is built for.

Like MiMa, TASTy-MiMa faces a particular challenge that the compiler itself is not built to handle: the ability to load symbols and types from different classpaths and somehow relate them.
This is the most critical reason for which we cannot use the compiler's own ability to read TASTy files to implement TASTy-MiMa.

TASTy-MiMa needs the following "features" from tasty-query:

* Read the public symbols and types
* Iterate through all the symbols defined in a library (a set of TASTy files within a classpath)
* Semantically compare types for equivalence and subtyping
* Identify which methods in super classes and super traits a given method implements or overrides
* List the direct children of sealed traits and classes

### Other use cases

Here are a few other use cases for tasty-query:

* Debuggers, for example to implement a "smart step into" feature
* Static analysis tools, from linters to verification tools
* A TASTy interpreter

The very existence of tasty-query also keeps the compiler honest about what TASTy really *is*, how it is defined, and what it means.
We can build a "TASTy verifier" that only performs type *checking*, and verify that the compiler's output abides by the rules.

## Contributing

Thank you for wanting to contribute! Please read our [contributing guide](CONTRIBUTING.md).
