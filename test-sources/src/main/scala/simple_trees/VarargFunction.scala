package simple_trees

class VarargFunction {
  def takesVarargs(xs: Int*): Seq[Int] = xs

  def givesVarargs(xs: Seq[Int]): Seq[Int] =
    takesVarargs(xs*)

  def givesSeqLiteral(x: Int): Seq[Int] =
    takesVarargs(x, 1)

  def givesSeqToJava(xs: Seq[Int]): java.util.List[Int] =
    java.util.Arrays.asList(xs*)

  def givesSeqLiteralToJava(x: Int): java.util.List[Int] =
    java.util.Arrays.asList(x, 1)

  def givesSeqToScala2(xs: Seq[Int]): Vector[Int] =
    Vector(xs*)

  def givesSeqLiteralToScala2(x: Int): Vector[Int] =
    Vector(x, 1)
}
