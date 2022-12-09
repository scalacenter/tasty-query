package simple_trees

class ObjectMethods:
  def testEq(x: AnyRef, y: AnyRef): Any = x eq y
  def testNe(x: AnyRef, y: AnyRef): Any = x ne y

  def testSynchronized(x: AnyRef): Any = x.synchronized(5)

  // Two of the regular public methods of java.lang.Object
  def testNotifyAll(x: AnyRef): Any = x.notifyAll()
  def testWait(x: AnyRef): Any = x.wait()

  // One of the regular protected methods of java.lang.Object
  def testClone(): Any = this.clone()
end ObjectMethods
