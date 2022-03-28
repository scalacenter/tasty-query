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

  class Bool private {
    infix def xor(that: Bool): Bool = ???
  }

  enum Expr[+T] {
    case ILit(n: Num) extends Expr[Num]
    case BLit(b: Bool) extends Expr[Bool]
    case Rem(l: Expr[Num], r: Expr[Num]) extends Expr[Num]
    case Xor(l: Expr[Bool], r: Expr[Bool]) extends Expr[Bool]
  }

  def eval[T](e: Expr[T]): T = (e: @unchecked) match {
    case Expr.ILit(i) => i
    case Expr.BLit(b) => b
    case Expr.Rem(l, r) => eval(l) % eval(r)
    case Expr.Xor(l, r) => eval(l) xor eval(r)
  }
}
