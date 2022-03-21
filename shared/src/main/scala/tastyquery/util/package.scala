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

/** Forward-ported from the explicit-nulls branch. */
extension [T](x: T | Null)
  /** Should be used when we know from the context that `x` is not null.
    *  Flow-typing under explicit nulls will automatically insert many necessary
    *  occurrences of uncheckedNN.
    */
  inline def uncheckedNN: T = x.asInstanceOf[T]

  inline def toOption: Option[T] =
    if x == null then None else Some(x.asInstanceOf[T])
end extension
