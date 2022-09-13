package simple_trees

class TypeRefIn {
  def withArray[U](arr: Array[U]): Unit = ()

  def withArrayOfSubtype[T](arr: Array[_ <: T]): Unit = withArray(arr)

  def withArrayAnyRef[U <: AnyRef](arr: Array[U]): Unit = ()

  def withArrayOfSubtypeAnyRef[T <: AnyRef](arr: Array[_ <: T]): Unit = withArrayAnyRef(arr)

  def withArrayAnyVal[U <: AnyVal](arr: Array[U]): Unit = ()

  def withArrayOfSubtypeAnyVal[T <: AnyVal](arr: Array[_ <: T]): Unit = withArrayAnyVal(arr)

  def withArrayList[U <: List[?]](arr: Array[U]): Unit = ()

  def withArrayOfSubtypeList[T <: List[?]](arr: Array[_ <: T]): Unit = withArrayList(arr)
}
