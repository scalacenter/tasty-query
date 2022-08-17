package tastyquery.ast

import tastyquery.util.syntax.chaining.given

object Flags:

  opaque type FlagSet = Long
  opaque type Flag <: FlagSet = Long

  extension (flags: FlagSet)
    private def bits: Long = flags

    def isEmpty: Boolean = bits == 0L
    def is(flag: Flag): Boolean = (bits & flag) != 0L

    def isAllOf(testFlags: FlagSet): Boolean = (flags & testFlags) == testFlags
    def isAnyOf(testFlags: FlagSet): Boolean = !(flags & testFlags).isEmpty

    def |(otherFlags: FlagSet): FlagSet = bits | otherFlags.bits
    def &(otherFlags: FlagSet): FlagSet = bits & otherFlags.bits
  end extension

  private var flagIdx = 0
  private def newFlag(): Flag = {
    assert(flagIdx <= 63)
    1 << flagIdx andThen { flagIdx += 1 }
  }

  val EmptyFlagSet: FlagSet = 0L

  val Contravariant: Flag = newFlag()
  val Covariant: Flag = newFlag()
  val Method: Flag = newFlag()
  val Opaque: Flag = newFlag()
  val Private: Flag = newFlag()
  val TypeParam: Flag = newFlag()

  val VarianceFlags: FlagSet = Covariant | Contravariant

  /** A symbol is a class' type parameter iff it has all of these flags. */
  val ClassTypeParam: FlagSet = Private | TypeParam
