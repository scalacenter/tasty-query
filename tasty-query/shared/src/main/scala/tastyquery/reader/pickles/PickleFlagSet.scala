package tastyquery.reader.pickles

private[pickles] class PickleFlagSet(rawFlags: Long, val isType: Boolean):
  private def hasFlag(flag: Long): Boolean = (rawFlags & flag) != 0L

  def isImplicit: Boolean = hasFlag(0x00000001)
  def isFinal: Boolean = hasFlag(0x00000002)
  def isPrivate: Boolean = hasFlag(0x00000004)
  def isProtected: Boolean = hasFlag(0x00000008)

  def isSealed: Boolean = hasFlag(0x00000010)
  def isOverride: Boolean = hasFlag(0x00000020)
  def isCase: Boolean = hasFlag(0x00000040)
  def isAbstract: Boolean = hasFlag(0x00000080)

  def isDeferred: Boolean = hasFlag(0x00000100)
  def isMethod: Boolean = hasFlag(0x00000200)
  def isModule: Boolean = hasFlag(0x00000400)
  def isInterface: Boolean = hasFlag(0x00000800)

  def isMutable: Boolean = hasFlag(0x00001000)
  def isParam: Boolean = hasFlag(0x00002000)
  def isPackage: Boolean = hasFlag(0x00004000)
  def isMacro: Boolean = hasFlag(0x00008000)

  def isCovariant: Boolean = isType && hasFlag(0x00010000)
  def isCaptured: Boolean = !isType && hasFlag(0x00010000)

  def isByNameParam: Boolean = hasFlag(0x00010000)
  def isContravariant: Boolean = isType && hasFlag(0x00020000)
  // method symbol is a label. Set by TailCall
  def isLabel: Boolean = !isType && hasFlag(0x00020000)

  // Solution for constructors
  // class symbol is defined in this/superclass constructor
  def isInConstructor: Boolean = hasFlag(0x00020000)

  def isAbstractOverride: Boolean = hasFlag(0x00040000)
  def isLocal: Boolean = hasFlag(0x00080000)

  def isJava: Boolean = hasFlag(0x00100000)
  // Same as in the java debug => doesn't work as intended
  def isSynthetic: Boolean = hasFlag(0x00200000)

  def isStable: Boolean = hasFlag(0x00400000)
  def isStatic: Boolean = hasFlag(0x00800000)

  def isCaseAccessor: Boolean = hasFlag(0x01000000)
  // Should work for traits, not sure
  def isTrait: Boolean = isType && hasFlag(0x02000000)
  def hasDefault: Boolean = !isType && hasFlag(0x02000000)

  // Solution for bridges
  def isBridge: Boolean = hasFlag(0x04000000)
  def isAccessor: Boolean = hasFlag(0x08000000)

  def isSuperAccessor: Boolean = hasFlag(0x10000000)
  def isParamAccessor: Boolean = hasFlag(0x20000000)

  // for variables: is the variable caching a module value
  def isModuleVar: Boolean = hasFlag(0x40000000)
  // Probably a solution for synthetic
  // for methods: synthetic method, but without SYNTHETIC flag
  def isSyntheticMethod: Boolean = hasFlag(0x40000000)
  // for type symbols: does not have type parameters
  def isMonomorphic: Boolean = hasFlag(0x40000000)
  // symbol is a lazy val. can't have MUTABLE unless transformed by typer
  def isLazy: Boolean = hasFlag(0x80000000L)

  def isError: Boolean = hasFlag(0x100000000L)
  def isOverloaded: Boolean = hasFlag(0x200000000L)
  def isLifted: Boolean = hasFlag(0x400000000L)

  // TODO: Test for mixin
  def isMixedIn: Boolean = !isType && hasFlag(0x800000000L)
  def isExistential: Boolean = isType && hasFlag(0x800000000L)

  def isExpandedName: Boolean = hasFlag(0x1000000000L)
  def isImplementationClass: Boolean = hasFlag(0x2000000000L)
  def isPreSuper: Boolean = hasFlag(0x2000000000L)

  def isSpecialized: Boolean = hasFlag(0x10000000000L)
  def isVBridge: Boolean = hasFlag(0x40000000000L)
  def isJavaVarargs: Boolean = hasFlag(0x80000000000L)
  def isEnum: Boolean = hasFlag(0x1000000000000L)
