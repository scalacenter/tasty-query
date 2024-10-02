package tastyquery.reader.tasties

import scala.collection.mutable

private[tasties] object TastyReader:

  /** An address pointing to an index in a Tasty buffer's byte array */
  final case class Addr(index: Int) extends AnyVal:
    def -(delta: Int): Addr = Addr(this.index - delta)
    def +(delta: Int): Addr = Addr(this.index + delta)

    def ==(that: Addr): Boolean = this.index == that.index
    def !=(that: Addr): Boolean = this.index != that.index
  end Addr

  /** An address referring to a serialized name */
  final case class NameRef(index: Int) extends AnyVal
end TastyReader

/** A byte array buffer that can be filled with bytes or natural numbers in TASTY format,
  * and that supports reading and patching addresses represented as natural numbers.
  *
  * @param bytes    The array containing data
  * @param start    The position from which to read
  * @param end      The position one greater than the last byte to be read
  * @param base     The index referenced by the logical zero address Addr(0)
  */
private[tasties] class TastyReader(val bytes: Array[Byte], start: Int, end: Int, val base: Int = 0):
  def this(bytes: Array[Byte]) = this(bytes, 0, bytes.length)

  import TastyReader.*

  private var bp: Int = start

  def addr(idx: Int): Addr = Addr(idx - base)
  def index(addr: Addr): Int = addr.index + base

  /** The address of the first byte to read, respectively byte that was read */
  def startAddr: Addr = addr(start)

  /** The address of the next byte to read */
  def currentAddr: Addr = addr(bp)

  /** the address one greater than the last brte to read */
  def endAddr: Addr = addr(end)

  /** Have all bytes been read? */
  def isAtEnd: Boolean = bp == end

  /** A new reader over the same array with the same address base, but with
    * specified start and end positions
    */
  def subReader(start: Addr, end: Addr): TastyReader =
    new TastyReader(bytes, index(start), index(end), base)

  /** Read a byte of data. */
  def readByte(): Int =
    val result = bytes(bp) & 0xff
    bp += 1
    result
  end readByte

  /** Returns the next byte of data as a natural number without advancing the read position */
  def nextByte: Int = bytes(bp) & 0xff

  /** Read the next `n` bytes of `data`. */
  def readBytes(n: Int): Array[Byte] =
    val result = new Array[Byte](n)
    System.arraycopy(bytes, bp, result, 0, n)
    bp += n
    result
  end readBytes

  /** Read a natural number fitting in an Int in big endian format, base 128.
    * All but the last digits have bit 0x80 set.
    */
  def readNat(): Int = readLongNat().toInt

  /** Read an integer number in 2's complement big endian format, base 128.
    * All but the last digits have bit 0x80 set.
    */
  def readInt(): Int = readLongInt().toInt

  /** Read a natural number fitting in a Long in big endian format, base 128.
    * All but the last digits have bit 0x80 set.
    */
  def readLongNat(): Long =
    var b = 0L
    var x = 0L
    while
      b = bytes(bp)
      x = (x << 7) | (b & 0x7f)
      bp += 1
      (b & 0x80) == 0
    do ()
    x
  end readLongNat

  /** Read a long integer number in 2's complement big endian format, base 128. */
  def readLongInt(): Long =
    var b = bytes(bp)
    var x: Long = (b << 1).toByte >> 1 // sign extend with bit 6.
    bp += 1
    while (b & 0x80) == 0 do
      b = bytes(bp)
      x = (x << 7) | (b & 0x7f)
      bp += 1
    end while
    x
  end readLongInt

  /** Read an uncompressed Long stored in 8 bytes in big endian format */
  def readUncompressedLong(): Long =
    var x: Long = 0
    for i <- 0 to 7 do x = (x << 8) | (readByte() & 0xff)
    x
  end readUncompressedLong

  /** Read a natural number and return as a NameRef */
  def readNameRef(): NameRef = NameRef(readNat())

  /** Read a natural number and return as an address */
  def readAddr(): Addr = Addr(readNat())

  /** Read a length number and return the absolute end address implied by it,
    * given as <address following length field> + <length-value-read>.
    */
  def readEnd(): Addr = addr(readNat() + bp)

  /** Set read position to the one pointed to by `addr` */
  def goto(addr: Addr): Unit =
    bp = index(addr)

  /** Is the current read address before the given end address? */
  def isBefore(end: Addr): Boolean =
    bp < index(end)

  /** Perform `op` until `end` address is reached and collect results in a list. */
  def until[T](end: Addr)(op: => T): List[T] =
    val buf = new mutable.ListBuffer[T]
    while isBefore(end) do buf += op
    assert(bp == index(end))
    buf.toList
  end until

  /** If before given `end` address, the result of `op`, otherwise `default` */
  def ifBefore[T](end: Addr)(op: => T, default: T): T =
    if isBefore(end) then op
    else default

  /** Perform `op` while cindition `cond` holds and collect results in a list. */
  def collectWhile[T](cond: => Boolean)(op: => T): List[T] =
    val buf = new mutable.ListBuffer[T]
    while cond do buf += op
    buf.toList
  end collectWhile
end TastyReader
