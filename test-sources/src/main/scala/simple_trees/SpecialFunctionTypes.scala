package simple_trees

class SpecialFunctionTypes:
  def contextFunction(f: String ?=> Unit): Unit = f(using "Hello")

  def contextFunctionResult(s: String): String ?=> Int = summon[String].toInt

  def polyFunction(t: (Int, String), f: [T] => T => Option[T]): (Option[Int], Option[String]) =
    ???

  def calls(): Unit =
    contextFunction {
      summon[String].toInt
    }

    contextFunctionResult("hello")(using "foo")
    val f: String ?=> Int = contextFunctionResult("hello")
    f(using "foo")

    polyFunction((1, "foo"), [T] => (x: T) => Some(x))
  end calls
end SpecialFunctionTypes
