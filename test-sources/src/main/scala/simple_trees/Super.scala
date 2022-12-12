package simple_trees

class Base {
  def classF(): Unit = ()
  def classG: Int = 1

  def commonF(): Unit = ()
  def commonG: Int = 1
}

trait BaseTrait extends Base {
  override def commonF(): Unit = ()
  override def commonG: Int = 4

  def traitF(): Unit = ()
  def traitG: Int = 5
}

class Super extends Base with BaseTrait {
  override def classF(): Unit = ()
  override def classG: Int = 3

  override def commonF(): Unit = ()
  override def commonG: Int = 7

  override def traitF(): Unit = ()
  override def traitG: Int = 8

  def callMyClassF(): Unit = classF()
  def callBareSuperClassF(): Unit = super.classF()
  def callQualifiedSuperClassF(): Unit = super[Base].classF()

  def callMyClassG(): Int = classG
  def callBareSuperClassG(): Int = super.classG
  def callQualifiedSuperClassG(): Int = super[Base].classG

  def callMyCommonF(): Unit = commonF()
  def callBareSuperCommonF(): Unit = super.commonF()
  def callQualifiedBaseSuperCommonF(): Unit = super[Base].commonF()
  def callQualifiedBaseTraitSuperCommonF(): Unit = super[BaseTrait].commonF()

  def callMyCommonG(): Int = commonG
  def callBareSuperCommonG(): Int = super.commonG
  def callQualifiedBaseSuperCommonG(): Int = super[Base].commonG
  def callQualifiedBaseTraitSuperCommonG(): Int = super[BaseTrait].commonG

  def callMyTraitF(): Unit = traitF()
  def callBareSuperTraitF(): Unit = super.traitF()
  def callQualifiedSuperTraitF(): Unit = super[BaseTrait].traitF()

  def callMyTraitG(): Int = traitG
  def callBareSuperTraitG(): Int = super.traitG
  def callQualifiedSuperTraitG(): Int = super[BaseTrait].traitG
}
