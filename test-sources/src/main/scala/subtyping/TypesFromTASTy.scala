package subtyping

class TypesFromTASTy:
  import TypesFromTASTy.*

  val listDefaultImport: List[Int] = Nil
  val listFullyQualified: scala.collection.immutable.List[Int] = Nil
  val listPackageAlias: scala.List[Int] = Nil

  val orType: Int | String = 1
  val andType: Product & Serializable = Nil

  type TToTType[T] = T => T

  val iarrayOfInt: IArray[Int] = IArray(1)

  val invariantOpaqueOfInt: InvariantOpaque[Int] = makeInvariantOpaque(5)
end TypesFromTASTy

object TypesFromTASTy:
  opaque type InvariantOpaque[A] = A

  def makeInvariantOpaque[A](x: A): InvariantOpaque[A] = x
end TypesFromTASTy
