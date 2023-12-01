package simple_trees

final class ValueClassWithDependentErasure[T](val value: T) extends AnyVal

object ValueClassWithDependentErasure:
  def ofGeneric[T](vc: ValueClassWithDependentErasure[T]): T = vc.value

  def ofString(vc: ValueClassWithDependentErasure[String]): String = vc.value

  def ofInt(vc: ValueClassWithDependentErasure[Int]): Int = vc.value

  def arrayOfGeneric[T](vcs: Array[ValueClassWithDependentErasure[T]]): T = vcs(0).value

  def arrayOfString(vcs: Array[ValueClassWithDependentErasure[String]]): String = vcs(0).value

  def arrayOfInt(vcs: Array[ValueClassWithDependentErasure[Int]]): Int = vcs(0).value

  def ofGenericArray[T](vc: ValueClassWithDependentErasure[Array[T]]): Array[T] = vc.value

  def ofGenericSeqArray[T](vc: ValueClassWithDependentErasure[Array[? <: Seq[T]]]): Array[? <: Seq[T]] = vc.value

  def ofStringArray(vc: ValueClassWithDependentErasure[Array[String]]): Array[String] = vc.value

  def ofIntArray(vc: ValueClassWithDependentErasure[Array[Int]]): Array[Int] = vc.value
end ValueClassWithDependentErasure

object ValueClassWithDependentErasureTest:
  def test(): Unit =
    ValueClassWithDependentErasure.ofGeneric(new ValueClassWithDependentErasure(Some(5)))
    ValueClassWithDependentErasure.ofGeneric(new ValueClassWithDependentErasure(5))
    ValueClassWithDependentErasure.ofString(new ValueClassWithDependentErasure("hello"))
    ValueClassWithDependentErasure.ofInt(new ValueClassWithDependentErasure(5))

    ValueClassWithDependentErasure.arrayOfGeneric(Array(new ValueClassWithDependentErasure(Some(5))))
    ValueClassWithDependentErasure.arrayOfGeneric(Array(new ValueClassWithDependentErasure(5)))
    ValueClassWithDependentErasure.arrayOfString(Array(new ValueClassWithDependentErasure("hello")))
    ValueClassWithDependentErasure.arrayOfInt(Array(new ValueClassWithDependentErasure(5)))

    ValueClassWithDependentErasure.ofGenericArray(new ValueClassWithDependentErasure(Array(Some(5))))
    ValueClassWithDependentErasure.ofGenericArray(new ValueClassWithDependentErasure(Array(5)))
    ValueClassWithDependentErasure.ofGenericSeqArray(new ValueClassWithDependentErasure(Array(List(3))))
    ValueClassWithDependentErasure.ofStringArray(new ValueClassWithDependentErasure(Array("hello")))
    ValueClassWithDependentErasure.ofIntArray(new ValueClassWithDependentErasure(Array(5)))
  end test
end ValueClassWithDependentErasureTest
