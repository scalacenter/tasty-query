package tastyquery.ast

import tastyquery.util.syntax.chaining.given

object Flags:

  opaque type FlagSet = Long
  opaque type Flag <: FlagSet = Long

  extension (flags: FlagSet)
    def isEmpty: Boolean = flags == EmptyFlagSet
    def is(flag: Flag): Boolean = (flags & flag) != 0

  private var flagIdx = 0
  private def newFlag(): Flag = {
    assert(flagIdx <= 63)
    1 << flagIdx andThen { flagIdx += 1 }
  }

  val EmptyFlagSet: FlagSet = 0L
  val Method: Flag = newFlag()
