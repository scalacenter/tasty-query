package simple_trees

abstract class TypeMember {
  type TypeMember = Int
  type AbstractType
  type AbstractWithBounds >: Null <: Product
  opaque type Opaque = Int
  opaque type OpaqueWithBounds >: Null <: Product = Null

  def mTypeAlias(x: TypeMember): TypeMember = x
  def mAbstractType(x: AbstractType): AbstractType = x
  def mAbstractTypeWithBounds(x: AbstractWithBounds): AbstractWithBounds = x
  def mOpaque(x: Opaque): Opaque = x
  def mOpaqueWithBounds(x: OpaqueWithBounds): OpaqueWithBounds = x
}
