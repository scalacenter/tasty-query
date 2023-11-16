package tastyquery

private[tastyquery] object Flags:

  opaque type FlagSet = Long
  opaque type Flag <: FlagSet = Long

  extension (flags: FlagSet)
    private def bits: Long = flags

    def isEmpty: Boolean = bits == 0L
    def is(flag: Flag): Boolean = (bits & flag) != 0L

    def isAllOf(testFlags: FlagSet): Boolean = (flags & testFlags) == testFlags
    def isAnyOf(testFlags: FlagSet): Boolean = !(flags & testFlags).isEmpty

    def isAllOf(testFlags: FlagSet, butNotAnyOf: FlagSet): Boolean =
      (flags & (testFlags | butNotAnyOf)) == testFlags

    def |(otherFlags: FlagSet): FlagSet = bits | otherFlags.bits
    def &(otherFlags: FlagSet): FlagSet = bits & otherFlags.bits
    def &~(otherFlags: FlagSet): FlagSet = bits & ~otherFlags.bits

    def show: String =
      val result = new java.lang.StringBuilder
      for (flag, name) <- allFlags if is(flag) do result.append(" " + name)
      result.toString().drop(1)
    end show
  end extension

  private val allFlags = scala.collection.mutable.ArrayBuffer.empty[(Flag, String)]

  private var lastFlagIdx = 0
  private def newFlag(name: String): Flag = {
    lastFlagIdx += 1
    assert(lastFlagIdx <= 63)
    val flag: Flag = 1.toLong << lastFlagIdx
    allFlags += flag -> name
    flag
  }

  val EmptyFlagSet: FlagSet = 0L

  val AbsOverride: Flag = newFlag("AbsOverride")
  val Abstract: Flag = newFlag("Abstract")
  val Accessor: Flag = newFlag("Accessor")
  val Artifact: Flag = newFlag("Artifact")
  val Case: Flag = newFlag("Case")
  val CaseAccessor: Flag = newFlag("CaseAccessor")
  val Contravariant: Flag = newFlag("Contravariant")
  val Covariant: Flag = newFlag("Covariant")
  val Enum: Flag = newFlag("Enum")
  val Erased: Flag = newFlag("Erased")
  val Exported: Flag = newFlag("Exported")
  val Extension: Flag = newFlag("Extension")
  val Final: Flag = newFlag("Final")
  val Given: Flag = newFlag("Given")
  val HasDefault: Flag = newFlag("HasDefault")
  val Implicit: Flag = newFlag("Implicit")
  val Infix: Flag = newFlag("Infix")
  val Inline: Flag = newFlag("Inline")
  val InlineProxy: Flag = newFlag("InlineProxy")
  val JavaDefined: Flag = newFlag("JavaDefined")
  val Lazy: Flag = newFlag("Lazy")
  val Local: Flag = newFlag("Local")
  val Macro: Flag = newFlag("Macro")
  val Method: Flag = newFlag("Method")
  val Module: Flag = newFlag("Module")
  val Mutable: Flag = newFlag("Mutable")
  val NoInitsInterface: Flag = newFlag("NoInitsInterface")
  val Opaque: Flag = newFlag("Opaque")
  val Open: Flag = newFlag("Open")
  val Override: Flag = newFlag("Override")
  val ParamAccessor: Flag = newFlag("ParamAccessor")
  val Private: Flag = newFlag("Private")
  val Protected: Flag = newFlag("Protected")
  val Scala2Defined: Flag = newFlag("Scala2Defined")
  val Sealed: Flag = newFlag("Sealed")
  val SignaturePolymorphic: Flag = newFlag("SignaturePolymorphic")
  val SuperParamAlias: Flag = newFlag("SuperParamAlias")
  val Static: Flag = newFlag("Static")
  val StableRealizable: Flag = newFlag("StableRealizable")
  val Synthetic: Flag = newFlag("Synthetic")
  val Trait: Flag = newFlag("Trait")
  val Transparent: Flag = newFlag("Transparent")

  /** Modules always have these flags set */
  val ModuleValCreationFlags: FlagSet = Module | Lazy | Final | StableRealizable

  /** Module classes always have these flags set */
  val ModuleClassCreationFlags: FlagSet = Module | Final
end Flags
