package simple_trees

class WithPrintAndStatus {
  def print(): Unit = ()
  def status: Unit  = ()
}

class WithStatus {
  def status: Unit = ()
}

class WithGivens {
  given Int = 0
  given AnyRef = null
}

class Export {
  private val first = WithPrintAndStatus()
  private val second = WithStatus()
  private val givens = WithGivens()

  export first.status
  export second.{status => _, *}
  export givens.given AnyRef
}
