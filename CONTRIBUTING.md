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
- [sbt](https://www.scala-sbt.org/download.html)

A text editor is also useful, we recommend [VS Code](https://code.visualstudio.com) with the [Metals IDE extension](https://marketplace.visualstudio.com/items?itemName=scalameta.metals).

## Try your setup
To test that everything is working, you can run the tests. In a terminal, navigate to the directory of this project and use the command:
```script
sbt test
```

## Procedure

1. First, read our [issues](https://github.com/scalacenter/tasty-query/issues) to see if there is something already actionable, (labelled with `bug`, `enhancement`, `documentation`, `good first issue`, or `help wanted`)
2. If you are adding code, make sure to add tests that validate each code addition.
3. Format the code.

## Adding Tests

We have several test suites to add to, depending on the contribution type:
- For additions of new TASTy tree kinds, please add to [ReadTreeSuite](jvm/src/test/scala/tastyquery/ReadTreeSuite.scala)
- To test symbol structure of self-contained TASTy files, please add to [SymbolSuite][jvm/src/test/scala/tastyquery/SymbolSuite.scala]
  - `SymbolSuite` is best avoided unless you are specifically testing reading of symbols defined in TASTy files.
- To test symbol structure and types of TASTy files, and reading of external dependencies, please add to [TypeSuite][jvm/src/test/scala/tastyquery/TypeSuite.scala]

for each test suite, it is usually sufficient to copy a pre-existing test and change it for your needs.

## Formatting Code
We use [Scalafmt](https://scalameta.org/scalafmt/) to format our code, and pull requests are validated by CI to ensure that code is formatted correctly.

To format your code before making a PR, run Scalafmt with:

```script
sbt scalafmtAll
```

#### Edit Scalafmt Config:
You can edit the [config](https://scalameta.org/scalafmt/docs/configuration.html) in the file [.scalafmt.conf](.scalafmt.conf)
