# TASTy Query

TASTy Query will be the basis for all compiler-independent tools that analyze TASTy - an intermediate representation of Scala 3 code.

It scans the classpath to build a map of all definitions in a project. Its API will allow users to query the code for a class, inspect signatures of methods, values and types, and compare them.

## Contributing

Thank you for wanting to contribute! Please read our [contributing guide](CONTRIBUTING.md).

## Example Usage

to scan the TASTy of a several classes, and print the definitions contained within:

```shell
sbt "tastyQueryJVM/run -cp app.jar:lib.jar lib.Foo app.Bar"
```
