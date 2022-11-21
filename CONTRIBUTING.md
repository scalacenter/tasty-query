# Contributing

Thank you for wanting to contribute to TASTy query!

We are looking for both code and documentation contributions, or perhaps your can [report a bug](https://github.com/scalacenter/tasty-query/issues).

You can contribute to TASTy Query by reading the steps in this document and making a pull request.
Core maintainers will then read your contribution and offer constructive feedback and we will work with you to merge your contribution!

We also use a continuous integration (CI) system to automate some of the checking.

## Prerequisites
- You will need a GitHub account to make pull requests to this repository.
- You should be familiar with the [code of conduct](https://scala-lang.org/conduct/)

## Tools Needed To Begin
The following tools can be installed following our [Scala getting started guide](https://docs.scala-lang.org/getting-started/index.html):
- JVM 1.8+
- [Node.js](https://nodejs.org/en/download/) (optional)
- [sbt](https://www.scala-sbt.org/download.html)

A text editor is also useful, we recommend [VS Code](https://code.visualstudio.com) with the [Metals IDE extension](https://marketplace.visualstudio.com/items?itemName=scalameta.metals).

## Try your setup / Running Tests
To test that everything is working, you can run the tests.
In a terminal, navigate to the directory of this project and start `sbt` with the command:
```
$ sbt
[...]
sbt:root>
```

All the other commands in this document are assumed to be done within `sbt`.

To run all the tests on the JVM:
```
sbt:root> tastyQueryJVM/test
[...]
[success] Total time: 5 s, completed Nov 2, 2022 2:31:15 PM
```

You can also test the JS version, assuming you have installed Node.js, with:
```
sbt:root> tastyQueryJS/test
[...]
[success] Total time: 8 s, completed Nov 2, 2022 2:32:35 PM
```

## Structure of the project

* `tasty-query/`: source code and tests for tasty-query itself
  * `shared/src/main/`: main, portable sources
  * `shared/src/test`: test sources
  * `jvm/`: JVM-specific sources and tests
  * `js/`: JS-specific sources and tests
* `test-sources/`: source files used as input in the test cases of `tasty-query/`

## Procedure

1. First, read our [issues](https://github.com/scalacenter/tasty-query/issues) to see if there is something already actionable, (labelled with `bug`, `enhancement`, `documentation`, `good first issue`, or `help wanted`)
2. If you are adding code, make sure to add tests that validate each code addition.
3. Format the code.

## Adding Tests

We have several test suites to add to, depending on the contribution type:

* `ReadTreeSuite`: tests for reading specific kinds of TASTy trees
* `TypeSuite`: tests about computing the types of symbols and trees
* `SubtypingSuite`: tests about `tp1.isSubtype(tp2)` and `tp1.isSameType(tp2)`
* `PositionSuite`: tests for reading the positions (`Spans`) of trees
* `SignatureSuite` tests for the `signedName` of methods (and indirectly for the *erasure* of types)
* `SymbolSuite`: tests for reaching symbols in an isolated way (this is probably *not* where you want to add tests)

Take inspiration from existing tests in the appropriate test suite to write your own.

## Formatting Code
We use [Scalafmt](https://scalameta.org/scalafmt/) to format our code, and pull requests are validated by CI to ensure that code is formatted correctly.

To format your code before making a PR, run Scalafmt with:

```script
sbt:root> scalafmtAll
```

#### Edit Scalafmt Config:
You can edit the [config](https://scalameta.org/scalafmt/docs/configuration.html) in the file [.scalafmt.conf](.scalafmt.conf)

## Publishing a Release

We use [sbt-ci-release] and [sbt-version-policy].

1. Push a tag starting with `v` (e.g., `v1.2.3`)
2. After the release succeeds and the artifacts are publicly available, push a
   commit to reset the compatibility intention in `build.sbt`:
   ~~~ scala
   versionPolicyIntention := Compatibility.SourceAndBinaryCompatible
   ~~~

### How to Introduce Breaking Changes

If you try to introduce a breaking change, the task `versionPolicyCheck` fails
with a message like “Module xxx is not binary compatible with version x.y.z. You
have to relax your compatibility intention by changing the value of
`versionPolicyIntention`”.

To fix the issue, configure the key `versionPolicyIntention` according to the
nature of the breaking changes:

~~~ scala
// to introduce a source incompatibility
versionPolicyIntention := Compatibility.BinaryCompatible
// or, to introduce a binary incompatibility
versionPolicyIntention := Compatibility.None
~~~

[sbt-ci-release]: https://github.com/sbt/sbt-ci-release
[sbt-version-policy]: https://github.com/scalacenter/sbt-version-policy
