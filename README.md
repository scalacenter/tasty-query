# TASTy Query

TASTy Query is a compiler-independent library to semantically analyze TASTy - an intermediate representation of Scala 3 code.

It scans the classpath to build a map of all definitions in a project, whether they are defined in Java, Scala 2 or Scala 3.
Its API allows users to query semantic information about the project:

* Find classes, methods, fields, and type definitions.
* Resolve symbol references.
* Inspect types, and make semantic operations on them such as type equivalence and subtyping.
* Follow overriding relationships across classes.

In addition, for Scala 3 code, it provides access to the full Trees, allowing for deeper inspection of the code.

TASTy Query is still in development, so it is not unlikely that you will encounter bugs.
Feel free to file them in our bug tracker.
Nevertheless, it should already be usable for the most part.

## Usage

Add the following dependency to your build:

```scala
libraryDependencies += "ch.epfl.scala" %% "tasty-query" % "<latest-version>"
// or %%% from Scala.js
```

You can find the latest release in the Releases list on GitHub.

Head over to the [latest API docs](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery.html) to see what's available.
To get started, create a [`Classpath`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Classpaths$$Classpath.html) using [`ClasspathLoaders.read`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/jdk/ClasspathLoaders$.html).
Then, create a [`Context`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Contexts$$Context.html) object using [`Contexts.init(classpath)`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Contexts$.html#init-fffffe7c).
From there, follow the available methods to access [`Symbols`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Symbols$.html), [`Types`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Types$.html) and [`Trees`](https://javadoc.io/doc/ch.epfl.scala/tasty-query_3/latest/tastyquery/Trees$.html).

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

tasty-query's job is to read TASTy files for you, and present the information it contains (explicitly or implicitly) in as convenient way as possible.

### Compatibility

In general, we can talk about the compatibility between two "environments" A and B.
Assuming B comes *after* A (for some definition of "after" such as version-based), then we can define *backward* and *forward* compatibility:

* *Backward* compatibility: if something "works" with environment A, it also works with environment B.
* *Forward* compatibility: if something works with environment B, it also works with environment A.

By default, and otherwise specified, we refer to *backward* compatibility.

In the Scala 2 ecosystem, there were two kinds of compatibility: *source* and *binary* compatibility.

* Source compatibility: if a program source successfully compiles with environment A, then it also successfully compiles, with the same meaning, with environment B.
* Binary compatibility: if a program's classfiles successfully link with environment A, then they also successfully link, with the same meaning, with environment B.

On the JVM, linking errors materialize as various forms of `LinkageError` at run-time.
In Scala.js and Scala Native, they materialize as error messages at link time, i.e., at the time of producing a `.js` file or an executable.

Scala 3 adds a third kind of compatibility:

* TASTy compatibility: if a program's TASTy files successfully retypecheck with environment A, then they also successfully retypecheck, with the same meaning, with environment B.

As we will see later, "retypechecking" errors typically materialize during macro or `inline def` expansion.

Because of [reasons](https://www.youtube.com/watch?v=2wkEX6MCxJs), it is not practical nor useful to guarantee source compatibility.
The Scala 2 ecosystem is therefore organized around *binary* compatibility.
The Scala 3 ecosystem, however, has to be organized around *both* binary and TASTy compatibility.

### MiMa and the consequences of binary incompatibility

[MiMa](https://github.com/lightbend/mima) is a tool to automatically catch binary incompatibilities between two versions of a library.
MiMa has been instrumental in building a reliable ecosystem for Scala, which avoids [dependency hell](https://en.wikipedia.org/wiki/Dependency_hell).

Oftentimes, as humans not necessarily privy to all the compilation strategies of the Scala compiler, we think that a change will be compatible, although it is not.
A typical example is the addition of a `private var` in a `trait`, e.g., going from

```scala
trait A {
  var x: Int = 1
  def foo(): Int = x
}
```

to

```scala
trait A {
  var x: Int = 1
  private var y: Int = 2
  def foo(): Int = x + y
}
```

When mixing `A` into a class `C`, the compiler needs to create a field for `y` in `C`.
If `C` was compiled against the former version of `A`, but is linked against the latter, linking breaks.

MiMa detects that this change is invalid, and reports it so that it can be fixed before shipping erroneous versions of a library.

### Consequences of TASTy incompatibility

Similarly to binaries, changes in a Scala program can be TASTy incompatible even though we think they are compatible.
For example, adding a `super` call within the body of a trait method, or switching between a `Seq` and a vararg parameter.

Breaking TASTy compatibility in the API of a library `L` can cause issues when retypechecking the library with another library `M` that depends on it, when used from a project `P` that depends on both.
In particular, problems can arise if `M` has `inline def`s that call into the API of `L`.

Here is a concrete example.

```scala
// L.scala
object L {
  def list(xs: Seq[Int]): List[Int] = xs.toList
}
```

```scala
// M.scala
object M {
  inline def foo(): String =
    L.list(Seq(1, 2, 3)).sum.toString
}
```

```scala
// Test.Scala
object Test {
  def main(args: Array[String]): Unit = {
    println(M.foo())
  }
}
```

We first compile everything, and we even verify that it runs:

```
$ cs launch scalac:3.1.2 -- -d bin/ L.scala M.scala Test.scala
$ cs launch scala:3.1.2 -- -cp bin/ Test
6
```

Then, we change `xs: Seq[Int]` into `xs: Int*` in `L.scala`:

```scala
// L.scala
object L {
  def list(xs: Int*): List[Int] = xs.toList
}
```

and recompile only `L`:

```
$ cs launch scalac:3.1.2 -- -d bin L.scala
```

This change is not detected by MiMa, as it is binary compatible.

Finally we try to recompile only `Test`:

```
$ cs launch scalac:3.1.2 -- -cp bin/ -d bin/ Test.scala
-- [E007] Type Mismatch Error: Test.scala:3:17 ---------------------------------
3 |    println(M.foo())
  |            ^^^^^^^
  |            Found:    Seq[Int]
  |            Required: Int
  | This location contains code that was inlined from M.scala:3

longer explanation available when compiling with `-explain`
1 error found
```

This happens even though, from the point of view of `Test`, the change of `L` is both source and binary compatible, because it is not TASTy-compatible.
When inlining the body of `M.foo()` inside `main`, it gets *retypechecked* (but not re-*elaborated*) in the context of `main`.
Retypechecking fails because it is not valid to pass a `Seq[Int]` to a method that expects `Int*` varargs.

For a non-`inline` method, this wouldn't cause any issue, since there would be no reason for the compiler to retypecheck its body.

To guard against this kind of situation, we will need an equivalent of MiMa that checks TASTy-compatibility.
This is what TASTy-MiMa will be.

### TASTy-MiMa as use case of tasty-query

To implement TASTy-MiMa, we need a way to load TASTy files and extract semantic information out of them.
This is precisely what tasty-query is built for.

Like MiMa, TASTy-MiMa faces a particular challenge that the compiler itself is not built to handle: the ability to load symbols and types from different classpaths and somehow relate them.
This is the most critical reason for which we cannot use the compiler's own ability to read TASTy files to implement TASTy-MiMa.

TASTy-MiMa needs the following "features" from tasty-query:

* Read the public symbols and types
* Iterate through all the symbols defined in a library (a set of TASTy files within a classpath)
* Semantically compare types for equivalence and subtyping
* Identify which methods in super classes and super traits a given method implements or overrides

### Other use cases

Here are a few other use cases for tasty-query:

* Debuggers, for example to implement a "smart step into" feature
* Static analysis tools, from linters to verification tools
* A TASTy interpreter

The very existence of tasty-query also keeps the compiler honest about what TASTy really *is*, how it is defined, and what it means.
We can build a "TASTy verifier" that only performs type *checking*, and verify that the compiler's output abides by the rules.

## Contributing

Thank you for wanting to contribute! Please read our [contributing guide](CONTRIBUTING.md).
