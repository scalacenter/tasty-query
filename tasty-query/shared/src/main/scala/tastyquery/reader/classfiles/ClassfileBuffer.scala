package tastyquery.reader.classfiles

import java.nio.charset.StandardCharsets

import tastyquery.util.Forked
import tastyquery.util.syntax.chaining.given
import tastyquery.unsafe

import ClassfileReader.DataStream

object ClassfileBuffer {
  final class Root(bytes: IArray[Byte], offset: Int) extends Forked[DataStream] {
    override def use[T](op: DataStream ?=> T): T = op(using Child(bytes, offset))
  }

  final class Child(bytes: IArray[Byte], init: Int) extends DataStream { self =>

    private var bp: Int = init

    def readU1(): Int = (bytes(bp) & 0xff) andThen { bp += 1 }

    def readU2(): Int = (readU1() << 8) | readU1()

    def readU4(): Int = (readU1() << 24) | (readU1() << 16) | (readU1() << 8) | readU1()

    def readU4f(): Float = java.lang.Float.intBitsToFloat(readU4())

    def readU8(): Long = (readU4().toLong << 32) | readU4().toLong

    def readU8f(): Double = java.lang.Double.longBitsToDouble(readU8())

    def readUTF8(): String = {
      val size = readU2()
      val start = bp
      val arr = unsafe.asByteArray(bytes)
      String(arr, start, size, StandardCharsets.UTF_8) andThen { bp += size }
    }

    def fork: Root = Root(bytes, bp)

    def readSlice(length: Int): IArray[Byte] = bytes.slice(bp, bp + length) andThen { bp += length }

    final def skip(bytes: Int): Unit = bp += bytes

    final def consumedFully: Boolean = bp == bytes.length
  }
}
