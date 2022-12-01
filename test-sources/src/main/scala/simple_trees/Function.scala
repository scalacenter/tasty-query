package simple_trees

class Function {
  val functionLambda = (x: Int) => x + 1

  val samLambda: Runnable = () => ()

  val polyID: [T] => T => T = [T] => (x: T) => x

  val dependentID: (x: Any) => x.type = x => x
}
