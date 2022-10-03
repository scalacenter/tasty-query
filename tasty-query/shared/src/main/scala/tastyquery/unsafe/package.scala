package tastyquery.unsafe

/** Returns a mutable `Array` backed by the same memory as the given `IArray`.
  * You must not use the original `IArray` after calling this method, unless the
  * returned array will be used in read-only operations.
  */
def asByteArray(iarray: IArray[Byte]): Array[Byte] = iarray.asInstanceOf[Array[Byte]]
