package simple_trees

class GenericMethodWithTypeParamDependencies:
  def foo[A, B >: D <: A, C <: B, D](): Int = 1
end GenericMethodWithTypeParamDependencies
