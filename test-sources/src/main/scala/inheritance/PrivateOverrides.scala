package inheritance

object PrivateOverrides:
  class Parent:
    val y = 2

  class Child(y: Int) extends Parent:
    def readLocalY: Int = y + this.y

  def testSetup(): Int =
    val child = new Child(4)
    child.y
end PrivateOverrides
