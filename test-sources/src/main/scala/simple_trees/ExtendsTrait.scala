package simple_trees

trait AbstractTrait {
  def abstractMethod: Unit
}

class ExtendsTrait extends AbstractTrait {
  override def abstractMethod: Unit = ()
}
