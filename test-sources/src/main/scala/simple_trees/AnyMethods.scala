package simple_trees

class AnyMethods:
  def testEqEq(x: Any, y: Any): Any = x == y
  def testNEq(x: Any, y: Any): Any = x != y
  def testHashHash(x: Any): Any = x.##

  def testEquals(x: Any, y: Any): Any = x.equals(y)
  def testHashCode(x: Any): Any = x.hashCode()

  def testToString(x: Any): Any = x.toString()

  def testIsInstanceOfInt(x: Any): Any = x.isInstanceOf[Int]
  def testIsInstanceOfProduct(x: Any): Any = x.isInstanceOf[Product]

  def testAsInstanceOfInt(x: Any): Any = x.asInstanceOf[Int]
  def testAsInstanceOfProduct(x: Any): Any = x.asInstanceOf[Product]

  class Bag extends scala.reflect.Selectable

  def testTypeCast(bag: Bag { val m: Int }): Any = bag.m // bag.selectDynamic("m").$asInstanceOf$[Int]

  def testGetClassAny(x: Any): Any = x.getClass()
  def testGetClassProduct(x: Product): Class[_ <: Product] = x.getClass()
  def testGetClassInt(x: Int): Class[Int] = x.getClass() // nonsensical, but what can we do?
end AnyMethods
