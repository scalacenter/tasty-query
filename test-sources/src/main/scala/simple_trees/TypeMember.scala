package simple_trees

abstract class TypeMember {
  type TypeMember = Int
  type AbstractType
  type AbstractWithBounds >: Null <: AnyRef
  opaque type Opaque = Int
  opaque type OpaqueWithBounds >: Null <: AnyRef = Null
}
