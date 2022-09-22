package inheritance

class MyArrayOps[T](val value: Array[T]) extends AnyVal

object MyArrayOps:
  def genericArrayOps[T](xs: Array[T]): MyArrayOps[T] = new MyArrayOps(xs)
