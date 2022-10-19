package subtyping.paths

object Setup:
  def simplePaths(x: SimplePaths, y: SimplePaths, z: OtherSimplePaths): Unit =
    val xAlias: x.type = x
  end simplePaths

  def subclassPaths(x: SimplePaths, y: ConcreteSimplePathsChild, z: ConcreteSimplePathsChild): Unit =
    val yAlias: y.type = y
  end subclassPaths
end Setup

trait A
trait B extends A
class C extends B
class D extends B

class SimplePaths:
  type AbstractType
  type AbstractTypeWithBounds >: C <: A

  type AliasOfAbstractType = AbstractType
  type AliasOfAbstractTypeWithBounds = AbstractTypeWithBounds
end SimplePaths

// With members of the same shape as SimplePaths
class OtherSimplePaths:
  type AbstractType
  type AliasOfAbstractTypeWithBounds >: C <: A
end OtherSimplePaths

class ConcreteSimplePathsChild extends SimplePaths:
  type AbstractType = String
  type AbstractTypeWithBounds = B
end ConcreteSimplePathsChild
