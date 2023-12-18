package simple_trees

object InlinedPath:
  trait Foo:
    type Inner

  transparent inline def foo(using x: Foo): x.type = x
end InlinedPath

class InlinedPath:
  import InlinedPath.*

  def test(using x: Foo)(inner: foo.Inner): foo.Inner = inner
end InlinedPath
