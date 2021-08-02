package simple_trees

class WithPrintAndStatus {
  def print(): Unit = ()
  def status: Unit  = ()
}

class WithStatus {
  def status: Unit = ()
}

class Export {
  private val first = WithPrintAndStatus()
  private val second = WithStatus()

  export first.status
  export second.{status => _, *}
}
