package simple_trees

class Match {
  def f(x: Int): Int = x match {
    case 0 => 0
    case 1 | -1 | 2 => x + 1
    case 7 if x == 7 => x - 1
    case 3 | 4 | 5 if x < 5 => 0
    case _ if (x % 2 == 0) => x / 2
    case _ => -x
  }

  def g(xs: Seq[Int]): Int = xs match
    case List(elems: _*) => 0
    case _               => 1
}
