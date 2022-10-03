package tastyquery.reader.pickles

/** Fixed length byte array, with methods for basic unpickling.
  *
  *  @param bytes The pickle bytes.
  *  @param from The first index where defined data are found
  *  @param to   The first index where new data can be written
  */
private[pickles] class PickleBuffer(val bytes: IArray[Byte], from: Int) {

  var readIndex = from

  // -- Basic input routines --------------------------------------------

  /** Read a byte */
  def readByte(): Int = {
    val x = bytes(readIndex).toInt; readIndex += 1; x
  }

  /** Read a natural number in big endian format, base 128.
    *  All but the last digits have bit 0x80 set.
    */
  def readNat(): Int = readLongNat().toInt

  def readLongNat(): Long = {
    var b = 0L
    var x = 0L
    while {
      b = readByte().toLong
      x = (x << 7) + (b & 0x7f)
      (b & 0x80) != 0L
    } do ()
    x
  }

  /** Read a long number in signed big endian format, base 256. */
  def readLong(len: Int): Long = {
    var x = 0L
    var i = 0
    while (i < len) {
      x = (x << 8) + (readByte() & 0xff)
      i += 1
    }
    val leading = 64 - (len << 3)
    x << leading >> leading
  }

  /** Returns the buffer as a sequence of (Int, Array[Byte]) representing
    *  (tag, data) of the individual entries.  Saves and restores buffer state.
    */

  def toIndexedSeq: IndexedSeq[(Int, IArray[Byte])] = {
    val saved = readIndex
    readIndex = 0
    readNat(); readNat() // discarding version
    val result = new Array[(Int, IArray[Byte])](readNat())

    result.indices foreach { index =>
      val tag = readNat()
      val len = readNat()
      val bytes0 = bytes.slice(readIndex, len + readIndex)
      readIndex += len

      result(index) = tag -> bytes0
    }

    readIndex = saved
    result.toIndexedSeq
  }

  /** Perform operation `op` until the condition
    *  `readIndex == end` is satisfied.
    *  Concatenate results into a list.
    */
  def until[T](end: Int, op: () => T): List[T] =
    if (readIndex == end) List() else op() :: until(end, op)

  /** Perform operation `op` the number of
    *  times specified.  Concatenate the results into a list.
    */
  def times[T](n: Int, op: () => T): List[T] =
    if (n == 0) List() else op() :: times(n - 1, op)

  /** Pickle = majorVersion_Nat minorVersion_Nat nbEntries_Nat {Entry}
    *  Entry  = type_Nat length_Nat [actual entries]
    *
    *  Assumes that the ..Version_Nat are already consumed.
    *
    *  @return an array mapping entry numbers to locations in
    *  the byte array where the entries start.
    */
  def createIndex(): IArray[Int] = {
    val index = new Array[Int](readNat()) // nbEntries_Nat
    for i <- index.indices do {
      index(i) = readIndex
      readByte() // skip type_Nat
      readIndex = readNat() + readIndex // read length_Nat, jump to next entry
    }
    IArray.unsafeFromArray(index)
  }
}
