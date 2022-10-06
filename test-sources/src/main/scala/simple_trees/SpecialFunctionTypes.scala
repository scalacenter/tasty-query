package simple_trees

class SpecialFunctionTypes:
  def contextFunction(f: String ?=> Unit): Unit = f(using "Hello")
end SpecialFunctionTypes
