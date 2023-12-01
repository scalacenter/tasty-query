package inheritance

class MyFlags(val bits: Long) extends AnyVal:
  def merge(that: MyFlags): MyFlags = MyFlags(bits | that.bits)

object MyFlags:
  val Private: MyFlags = new MyFlags(1L << 0)

  def mergeAll(xs: Array[MyFlags]): MyFlags = xs.reduce(_.merge(_))
end MyFlags

object MyFlagsTest:
  def test(): Unit =
    MyFlags.mergeAll(Array(MyFlags.Private))
  end test
end MyFlagsTest
