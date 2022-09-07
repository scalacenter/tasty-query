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
    1.toLong << flagIdx andThen { flagIdx += 1 }
  }

  val EmptyFlagSet: FlagSet = 0L

  val AbsOverride: Flag = newFlag()
  val Abstract: Flag = newFlag()
  val Accessor: Flag = newFlag()
  val Artifact: Flag = newFlag()
  val Case: Flag = newFlag()
  val CaseAccessor: Flag = newFlag()
  val Contravariant: Flag = newFlag()
  val Covariant: Flag = newFlag()
  val Deferred: Flag = newFlag()
  val Enum: Flag = newFlag()
  val Erased: Flag = newFlag()
  val Exported: Flag = newFlag()
  val Extension: Flag = newFlag()
  val Final: Flag = newFlag()
  val Given: Flag = newFlag()
  val Implicit: Flag = newFlag()
  val Infix: Flag = newFlag()
  val Inline: Flag = newFlag()
  val InlineProxy: Flag = newFlag()
  val Lazy: Flag = newFlag()
  val Local: Flag = newFlag()
  val Macro: Flag = newFlag()
  val Method: Flag = newFlag()
  val Module: Flag = newFlag()
  val ModuleVal: Flag = newFlag()
  val ModuleClass: Flag = newFlag()
  val Mutable: Flag = newFlag()
  val NoInitsInterface: Flag = newFlag()
  val Opaque: Flag = newFlag()
  val Open: Flag = newFlag()
  val Override: Flag = newFlag()
  val ParamAccessor: Flag = newFlag()
  val Private: Flag = newFlag()
  val Protected: Flag = newFlag()
  val Sealed: Flag = newFlag()
  val SuperParamAlias: Flag = newFlag()
  val Static: Flag = newFlag()
  private[tastyquery] val StableRealizable: Flag = newFlag()
  val Synthetic: Flag = newFlag()
  val Trait: Flag = newFlag()
  val Transparent: Flag = newFlag()
  val TypeParameter: Flag = newFlag()

  val VarianceFlags: FlagSet = Covariant | Contravariant

  /** A symbol is a class' type parameter iff it has all of these flags. */
  val ClassTypeParam: FlagSet = Private | TypeParameter

  /** Modules always have these flags set */
  val ModuleValCreationFlags: FlagSet = ModuleVal | Lazy | Final | StableRealizable

  /** Module classes always have these flags set */
  val ModuleClassCreationFlags: FlagSet = ModuleClass | Final
