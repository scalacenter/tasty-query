package subtyping

class TypesFromTASTy:
  import TypesFromTASTy.*

  type TypeMember

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

  type MatchTypeMono2[T] = T match
    case Int     => String
    case Boolean => Double

  type MatchTypeMono2Bounded[T] <: AnyVal = T match
    case Int    => Boolean
    case String => Int

  type MatchTypeMono2Subtype[T] = T match
    case Int     => String { type Foo = Int }
    case Boolean => Double

  type MatchTypeMono2WithDefault[T] = T match
    case Int     => String
    case Boolean => Double
    case _       => Product

  type MatchTypePoly2[T] = T match
    case List[t]     => t
    case Inv[t]      => t
    case Consumer[t] => t

  type MatchTypeLiterals[T <: Int] = T match
    case 1 => Int
    case 3 => String
    case 5 => Boolean

  type MatchTypeEnums[T <: MyEnum[Any]] = T match
    case MyEnum.Singleton1.type => Int
    case MyEnum.Parametric[Int] => Double
    case MyEnum.Singleton2.type => String
    case MyEnum.Parametric[t]   => t

  type MatchTypeOldStyleEnums[T <: OldStyleEnum[Any]] = T match
    case OldStyleEnum.Singleton1.type => Int
    case OldStyleEnum.Parametric[Int] => Double
    case OldStyleEnum.Singleton2.type => String
    case OldStyleEnum.Parametric[t]   => t
end TypesFromTASTy

object TypesFromTASTy:
  final class Inv[A]

  final class Consumer[-A]

  opaque type InvariantOpaque[A] = A

  def makeInvariantOpaque[A](x: A): InvariantOpaque[A] = x

  enum MyEnum[+T]:
    case Singleton1, Singleton2
    case Parametric(x: T)

  sealed abstract class OldStyleEnum[+T]

  object OldStyleEnum:
    case object Singleton1 extends OldStyleEnum[Nothing]
    case object Singleton2 extends OldStyleEnum[Nothing]
    case class Parametric[+T](x: T) extends OldStyleEnum[T]
  end OldStyleEnum
end TypesFromTASTy
