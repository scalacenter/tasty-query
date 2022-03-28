package simple_trees

class RecApply {

  class Num private {
    def % (that: Num): Num = ???
  }

  object Num {
    val Zero: Num = Num()
  }

  def gcd(a: Num, b: Num): Num = {
    if b == Num.Zero then a else gcd(b, a % b)
  }
}
