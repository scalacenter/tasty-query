package simple_trees

class TypeRefIn {
  def withArray[U](arr: Array[U]): Unit = ()

  def withArrayOfSubtype[T](arr: Array[_ <: T]) = withArray(arr)
}
