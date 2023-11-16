package tastyquery

import scala.annotation.switch

import scala.compiletime.asMatchable

import tastyquery.Contexts.*
import tastyquery.Types.Type

object Constants {
  final val NoTag = 0
  final val UnitTag = 1
  final val BooleanTag = 2
  final val ByteTag = 3
  final val ShortTag = 4
  final val CharTag = 5
  final val IntTag = 6
  final val LongTag = 7
  final val FloatTag = 8
  final val DoubleTag = 9
  final val StringTag = 10
  final val NullTag = 11
  final val ClazzTag = 12

  final class Constant private (val value: Matchable, val tag: Int, internal: Boolean) {
    @deprecated("this constructor is unsafe; use the `apply` methods in the companion instead", since = "1.1.0")
    def this(value: Matchable, tag: Int) =
      this(value, tag, internal = true)

      // Check that the tag matches the value:
      val valid = (tag: @switch) match
        case UnitTag    => value == ()
        case BooleanTag => value.isInstanceOf[Boolean]
        case CharTag    => value.isInstanceOf[Char]
        case ByteTag    => value.isInstanceOf[Byte]
        case ShortTag   => value.isInstanceOf[Short]
        case IntTag     => value.isInstanceOf[Int]
        case LongTag    => value.isInstanceOf[Long]
        case FloatTag   => value.isInstanceOf[Float]
        case DoubleTag  => value.isInstanceOf[Double]
        case StringTag  => value.isInstanceOf[String]
        case NullTag    => value == null
        case ClazzTag   => value.isInstanceOf[Type]
        case _          => false

      require(valid, s"Illegal combination of value and tag for Constant($value, $tag)")
    end this

    def wideType(using Context): Type = tag match
      case UnitTag    => defn.UnitType
      case BooleanTag => defn.BooleanType
      case CharTag    => defn.CharType
      case ByteTag    => defn.ByteType
      case ShortTag   => defn.ShortType
      case IntTag     => defn.IntType
      case LongTag    => defn.LongType
      case FloatTag   => defn.FloatType
      case DoubleTag  => defn.DoubleType
      case StringTag  => defn.StringType
      case NullTag    => defn.NullType
      case ClazzTag   => defn.ClassTypeOf(typeValue)

    def isByteRange: Boolean = isIntRange && Byte.MinValue <= intValue && intValue <= Byte.MaxValue
    def isShortRange: Boolean = isIntRange && Short.MinValue <= intValue && intValue <= Short.MaxValue
    def isCharRange: Boolean = isIntRange && Char.MinValue <= intValue && intValue <= Char.MaxValue
    def isIntRange: Boolean = ByteTag <= tag && tag <= IntTag
    def isLongRange: Boolean = ByteTag <= tag && tag <= LongTag
    def isFloatRange: Boolean = ByteTag <= tag && tag <= FloatTag
    def isNumeric: Boolean = ByteTag <= tag && tag <= DoubleTag
    def isNonUnitAnyVal: Boolean = BooleanTag <= tag && tag <= DoubleTag
    def isAnyVal: Boolean = UnitTag <= tag && tag <= DoubleTag

    /** We need the equals method to take account of tags as well as values. */
    override def equals(other: Any): Boolean = other.asMatchable match {
      case that: Constant =>
        this.tag == that.tag && java.util.Objects.equals(value, that.value)
      case _ => false
    }

    def isNaN: Boolean = value match {
      case f: Float  => f.isNaN
      case d: Double => d.isNaN
      case _         => false
    }

    def booleanValue: Boolean =
      if (tag == BooleanTag) value.asInstanceOf[Boolean]
      else throw new Error("value " + value + " is not a boolean")

    def byteValue: Byte = tag match {
      case ByteTag   => value.asInstanceOf[Byte]
      case ShortTag  => value.asInstanceOf[Short].toByte
      case CharTag   => value.asInstanceOf[Char].toByte
      case IntTag    => value.asInstanceOf[Int].toByte
      case LongTag   => value.asInstanceOf[Long].toByte
      case FloatTag  => value.asInstanceOf[Float].toByte
      case DoubleTag => value.asInstanceOf[Double].toByte
      case _         => throw new Error("value " + value + " is not a Byte")
    }

    def shortValue: Short = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toShort
      case ShortTag  => value.asInstanceOf[Short]
      case CharTag   => value.asInstanceOf[Char].toShort
      case IntTag    => value.asInstanceOf[Int].toShort
      case LongTag   => value.asInstanceOf[Long].toShort
      case FloatTag  => value.asInstanceOf[Float].toShort
      case DoubleTag => value.asInstanceOf[Double].toShort
      case _         => throw new Error("value " + value + " is not a Short")
    }

    def charValue: Char = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toChar
      case ShortTag  => value.asInstanceOf[Short].toChar
      case CharTag   => value.asInstanceOf[Char]
      case IntTag    => value.asInstanceOf[Int].toChar
      case LongTag   => value.asInstanceOf[Long].toChar
      case FloatTag  => value.asInstanceOf[Float].toChar
      case DoubleTag => value.asInstanceOf[Double].toChar
      case _         => throw new Error("value " + value + " is not a Char")
    }

    def intValue: Int = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toInt
      case ShortTag  => value.asInstanceOf[Short].toInt
      case CharTag   => value.asInstanceOf[Char].toInt
      case IntTag    => value.asInstanceOf[Int]
      case LongTag   => value.asInstanceOf[Long].toInt
      case FloatTag  => value.asInstanceOf[Float].toInt
      case DoubleTag => value.asInstanceOf[Double].toInt
      case _         => throw new Error("value " + value + " is not an Int")
    }

    def longValue: Long = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toLong
      case ShortTag  => value.asInstanceOf[Short].toLong
      case CharTag   => value.asInstanceOf[Char].toLong
      case IntTag    => value.asInstanceOf[Int].toLong
      case LongTag   => value.asInstanceOf[Long]
      case FloatTag  => value.asInstanceOf[Float].toLong
      case DoubleTag => value.asInstanceOf[Double].toLong
      case _         => throw new Error("value " + value + " is not a Long")
    }

    def floatValue: Float = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toFloat
      case ShortTag  => value.asInstanceOf[Short].toFloat
      case CharTag   => value.asInstanceOf[Char].toFloat
      case IntTag    => value.asInstanceOf[Int].toFloat
      case LongTag   => value.asInstanceOf[Long].toFloat
      case FloatTag  => value.asInstanceOf[Float]
      case DoubleTag => value.asInstanceOf[Double].toFloat
      case _         => throw new Error("value " + value + " is not a Float")
    }

    def doubleValue: Double = tag match {
      case ByteTag   => value.asInstanceOf[Byte].toDouble
      case ShortTag  => value.asInstanceOf[Short].toDouble
      case CharTag   => value.asInstanceOf[Char].toDouble
      case IntTag    => value.asInstanceOf[Int].toDouble
      case LongTag   => value.asInstanceOf[Long].toDouble
      case FloatTag  => value.asInstanceOf[Float].toDouble
      case DoubleTag => value.asInstanceOf[Double]
      case _         => throw new Error("value " + value + " is not a Double")
    }

    def stringValue: String = if tag == NullTag then "null" else value.toString

    /** The class type value of a `classOf` constant.
      *
      * This must be a "possibly parametrized class type" according to the
      * specification of the language. If the class is polymorphic, it may be
      * applied (making it a proper type) or not (in which case it is not a
      * proper type).
      */
    def typeValue: Type = value.asInstanceOf[Type]

    override def hashCode: Int = {
      import scala.util.hashing.MurmurHash3.*
      val seed = 17
      var h = seed
      h = mix(h, tag.##) // include tag in the hash, otherwise 0, 0d, 0L, 0f collide.
      if tag != NullTag then h = mix(h, value.hashCode) // use hashCode instead of ## to correctly handle Float/Double
      finalizeHash(h, length = 2)
    }

    override def toString: String = s"Constant($value)"
    def canEqual(x: Any): Boolean = true
    def get: Any = value
    def isEmpty: Boolean = false
    def _1: Any = value
  }

  object Constant {
    def apply(x: Null): Constant = new Constant(x, NullTag, internal = true)
    def apply(x: Unit): Constant = new Constant(x, UnitTag, internal = true)
    def apply(x: Boolean): Constant = new Constant(x, BooleanTag, internal = true)
    def apply(x: Byte): Constant = new Constant(x, ByteTag, internal = true)
    def apply(x: Short): Constant = new Constant(x, ShortTag, internal = true)
    def apply(x: Int): Constant = new Constant(x, IntTag, internal = true)
    def apply(x: Long): Constant = new Constant(x, LongTag, internal = true)
    def apply(x: Float): Constant = new Constant(x, FloatTag, internal = true)
    def apply(x: Double): Constant = new Constant(x, DoubleTag, internal = true)
    def apply(x: String): Constant = new Constant(x, StringTag, internal = true)
    def apply(x: Char): Constant = new Constant(x, CharTag, internal = true)
    def apply(x: Type): Constant = new Constant(x, ClazzTag, internal = true)

    def unapply(c: Constant): Constant = c
  }
}
