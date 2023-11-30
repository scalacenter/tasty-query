package simple_trees

import javax.annotation.processing.SupportedAnnotationTypes

class MissingAnnotations:
  @SupportedAnnotationTypes(Array("foo.bar"))
  def foo(): String = "hello"
end MissingAnnotations

object MissingAnnotationsTest:
  def test(): Unit =
    // This used to fail to resolve under JDK 11+, because the annotation is not available in java.base
    new MissingAnnotations().foo()
  end test
end MissingAnnotationsTest
