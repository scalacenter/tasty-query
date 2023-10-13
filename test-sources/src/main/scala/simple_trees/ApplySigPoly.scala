package simple_trees

import java.lang.invoke.*
import java.lang.invoke.MethodType.methodType

class ApplySigPoly:
  import ApplySigPoly.*

  def test(): Unit =
    val l = MethodHandles.lookup()
    val self = new Foo()

    val mhNeg = l.findVirtual(classOf[Foo], "neg", methodType(classOf[Int], classOf[Int]))
    val mhRev = l.findVirtual(classOf[Foo], "rev", methodType(classOf[String], classOf[String]))
    val mhOverL = l.findVirtual(classOf[Foo], "over", methodType(classOf[String], classOf[Long]))
    val mhOverI = l.findVirtual(classOf[Foo], "over", methodType(classOf[String], classOf[Int]))
    val mhUnit = l.findVirtual(classOf[Foo], "unit", methodType(classOf[Unit], classOf[String]))
    val mhObj = l.findVirtual(classOf[Foo], "obj", methodType(classOf[Any], classOf[String]))

    val resNeg = (mhNeg.invokeExact(self, 42): Int)
    val resRev = (mhRev.invokeExact(self, "foo"): String)

    val resOverL = (mhOverL.invokeExact(self, 1L): String)
    val resOverI = (mhOverI.invokeExact(self, 1): String)

    { mhUnit.invokeExact(self, "hi"): Unit; () }

    val resObj = mhObj.invokeExact(self, "any2")
  end test
end ApplySigPoly

object ApplySigPoly:
  class Foo:
    def neg(x: Int): Int = -x
    def rev(s: String): String = s.reverse
    def over(l: Long): String = "long"
    def over(i: Int): String  = "int"
    def unit(s: String): Unit = ()
    def obj(s: String): Object = s
  end Foo
end ApplySigPoly
