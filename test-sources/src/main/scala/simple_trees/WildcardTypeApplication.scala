package simple_trees

class GenericWithTypeBound[T <: AnyKind]

class WildcardTypeApplication(anyList: List[_]) extends GenericWithTypeBound[_]
