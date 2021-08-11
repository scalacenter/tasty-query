package simple_trees

class TryCatch {
  def withTry(): Int =
    try {
      ThrowException().f()
      1
    } catch {
      case _ => 0
    } finally {
      ()
    }
}
