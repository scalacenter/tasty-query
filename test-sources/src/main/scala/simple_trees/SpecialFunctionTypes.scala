package simple_trees

class SpecialFunctionTypes:
  def contextFunction(f: String ?=> Unit): Unit = f(using "Hello")

  def contextFunctionResult(s: String): String ?=> Int = summon[String].toInt

  def calls(): Unit =
    contextFunction {
      summon[String].toInt
    }

    contextFunctionResult("hello")(using "foo")
    val f: String ?=> Int = contextFunctionResult("hello")
    f(using "foo")
  end calls
end SpecialFunctionTypes
