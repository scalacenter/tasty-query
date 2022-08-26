package simple_trees

class PolySelect:
  def testField(x: GenericClass[Int]): Int = x.field

  def testGetter(x: GenericClass[Int]): Int = x.getter

  def testMethod(x: GenericClass[Int]): Int = x.method(5)

  def testGenericMethod(x: GenericMethod): Int = x.identity(5)
