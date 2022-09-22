package inheritance

class MyArrayOps[T](val value: Array[T]) extends AnyVal

object MyArrayOps:
  def intArrayOps(xs: Array[Int]): MyArrayOps[Int] = new MyArrayOps(xs)
  def genericArrayOps[T](xs: Array[T]): MyArrayOps[T] = new MyArrayOps(xs)
