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

  /* This explicit selection generates a
   * Select(PackageRef(crosspackagetasty), TopLevelOpaqueTypeAlias)
   * in TASTy, without any mention of the enclosing package object.
   * So we have to find it by iterating on all the possible package objects.
   */
  val toplevelOpaqueTypeAlias: crosspackagetasty.TopLevelOpaqueTypeAlias =
    crosspackagetasty.TopLevelOpaqueTypeAlias(5)

  def higherKinded[F[_], T](x: F[T]): F[T] = x
end TypesFromTASTy

object TypesFromTASTy:
  opaque type InvariantOpaque[A] = A

  def makeInvariantOpaque[A](x: A): InvariantOpaque[A] = x
end TypesFromTASTy
