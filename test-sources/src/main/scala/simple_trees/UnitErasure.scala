package simple_trees

class UnitErasure:
  val unitVal: Unit = ()

  var unitVar: Unit = ()

  def unitParamelessDef: Unit = ()

  def unitResult(): Unit = ()

  def unitParam(x: Unit): Any = x

  def calls(): Unit =
    val _ = unitVal
    val _ = unitVar
    unitVar = ()
    unitParamelessDef
    unitResult()
    unitParam(())
  end calls
end UnitErasure
