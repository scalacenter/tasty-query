This is a work-in-progress reader of Scala 3 projects from their .tasty files. Run

```shell
sbt "tastyQueryJVM/run -cp whitespace-separated-project-classpath"
```

to read a project or


```shell
sbt "tastyQueryJVM/run --standalone path-to-.tasty-file"
```
to unpickle a single .tasty file.
