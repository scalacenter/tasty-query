package simple_trees

class EtaExpansion {
  def takesFunction(f: Int => Int): Int = f(0)
  def intMethod(x: Int): Int            = 0

  takesFunction(intMethod)
}
