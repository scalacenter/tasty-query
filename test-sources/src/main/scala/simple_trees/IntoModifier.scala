package simple_trees

import scala.Conversion.into

class IntoModifier {
  def methodWithIntoString(x: into[String]): Unit = ()

  into class IntoClass

  into trait IntoTrait

  into enum IntoEnum {
    case Foo
  }
}
