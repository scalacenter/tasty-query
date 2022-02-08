package tastyquery.util

import scala.reflect.ClassTag

inline def loop(times: Int)(inline op: => Unit): Unit = {
  var i = 0
  while (i < times) {
    op
    i += 1
  }
}

inline def accumulate[T: ClassTag](size: Int)(inline op: => T): IArray[T] = {
  val arr = new Array[T](size)
  var i = 0
  while (i < size) {
    arr(i) = op
    i += 1
  }
  IArray.unsafeFromArray(arr)
}
