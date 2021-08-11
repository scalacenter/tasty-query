package simple_trees

class DefaultParamsInConstructor(first: List[Int] = List(1), second: Int = 2, third: Int = 3)

class ChildCallsParentWithDefaultParameter extends DefaultParamsInConstructor(first = List(0), third = 0)
