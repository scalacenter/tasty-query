package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Modifiers.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Spans.*
import tastyquery.Trees.*
import tastyquery.Types.*

import tastyquery.reader.Loaders.Loader

/** Symbols for all kinds of definitions in Scala programs.
  *
  * Every definition, like `class`es, `def`s, `type`s and type parameters, is
  * associated with a `Symbol`. `Symbol`s are organized in a hierarchy,
  * depending on what kind of definitions they represent.
  *
  * ```none
  * Symbol
  *  |
  *  +- PackageSymbol                   any package, including the root package, the empty package, and nested packages
  *  |
  *  +- TermOrTypeSymbol                   any term or type symbol, i.e., not a package
  *     |
  *     +- TermSymbol                      any term definition:
  *     |                                  `val`, `var`, `def`, term param, term capture, `object` value
  *     |
  *     +- TypeSymbol                      any definition for a type
  *        +- ClassSymbol                  definition for a `class`, `trait`, or the module class of an `object`
  *        +- TypeSymbolWithBounds         any other kind of type: `type` definitions, type params, type captures
  *           +- TypeMemberSymbol          `type` definition, further refined through its `typeDef`
  *           +- TypeParamSymbol
  *              +- ClassTypeParamSymbol   type parameter of a class
  *              +- LocalTypeParamSymbol   any other type parameter
  * ```
  *
  * Additionally, `PackageSymbol` and `ClassSymbol` extend `DeclaringSymbol`.
  * Declaring symbols are the ones that contain declarations, which can be
  * looked up with their `name`s.
  *
  * `TypeMemberSymbol`s exist in 3 flavors, indicated by their `typeDef` field,
  * of type `TypeMemberDefinition`:
  *
  * - `TypeAlias(alias)`: type alias of the form `type T = alias`
  * - `AbstractType(bounds)`: abstract type member of the form `type T >: bounds.low <: bounds.high`
  * - `OpaqueTypeAlias(bounds, alias)`: opaque type alias of the form `type T >: bounds.low <: bounds.high = alias`
  *
  * The main property a `TermSymbol` is its `declaredType`, which is a `Type`.
  * All `TypeSymbolWithBounds` have `bounds` of type `TypeBounds`, which are
  * often used as their primary characteristic. `ClassSymbol`s are entirely
  * defined by themselves.
  *
  * With the exception of the root package symbol, all symbols have an `owner`
  * which is another `Symbol`.
  *
  * All symbols also have a `name`. It is a `TypeName` for `TypeSymbol`s, and a
  * `TermName` for `TermSymbol`s and `PackageSymbol`s.
  */
object Symbols {

  sealed abstract class Symbol protected (val owner: Symbol | Null) {
    type ThisNameType <: Name
    type DefiningTreeType <: DefTree

    val name: ThisNameType

    private var isFlagsInitialized = false
    private var myFlags: FlagSet = Flags.EmptyFlagSet
    private var myTree: Option[DefiningTreeType] = None
    private var myPrivateWithin: Option[DeclaringSymbol] = None
    private var myAnnotations: List[Annotation] | Null = null

    /** Checks that this `Symbol` has been completely initialized.
      *
      * This method is called by the various file readers after reading each
      * file, for all the `Symbol`s created while reading that file.
      */
    private[tastyquery] final def checkCompleted(): Unit =
      doCheckCompleted()

    protected final def failNotCompleted(details: String): Nothing =
      throw IllegalStateException(s"$this of class ${this.getClass().getName()} was not completed: $details")

    /** This method is overridden in every subclass to perform their own checks.
      *
      * Every override is expected to call `super.doCheckCompleted()` first.
      * If a check fail, it should be reported with [[failNotCompleted]].
      */
    protected def doCheckCompleted(): Unit =
      if !isFlagsInitialized then throw failNotCompleted("flags were not initialized")
      if myAnnotations == null then throw failNotCompleted("annotations were not initialized")

    private[tastyquery] def withTree(t: DefiningTreeType): this.type =
      require(!isPackage, s"Multiple trees correspond to one package, a single tree cannot be assigned")
      myTree = Some(t)
      this

    final def tree: Option[DefiningTreeType] =
      myTree

    private[tastyquery] final def withFlags(flags: FlagSet, privateWithin: Option[DeclaringSymbol]): this.type =
      if isFlagsInitialized then throw IllegalStateException(s"reassignment of flags to $this")
      else
        isFlagsInitialized = true
        myFlags = flags
        myPrivateWithin = privateWithin
        this

    private[tastyquery] final def setAnnotations(annots: List[Annotation]): this.type =
      if myAnnotations != null then throw IllegalStateException(s"reassignment of annotations to $this")
      else
        myAnnotations = annots
        this

    final def annotations: List[Annotation] =
      val local = myAnnotations
      if local != null then local
      else throw IllegalStateException(s"annotations of $this have not been initialized")

    protected final def privateWithin: Option[DeclaringSymbol] =
      if isFlagsInitialized then myPrivateWithin
      else throw IllegalStateException(s"flags of $this have not been initialized")

    protected final def flags: FlagSet =
      if isFlagsInitialized then myFlags
      else throw IllegalStateException(s"flags of $this have not been initialized")

    final def enclosingDecl: DeclaringSymbol = owner match {
      case owner: DeclaringSymbol => owner
      case _: Symbol | null =>
        assert(false, s"cannot access owner, ${this.name} is local or not declared within any scope")
    }

    /** The closest enclosing package of this symbol.
      * Returns this if this is a package.
      */
    private[tastyquery] final def closestPackage: PackageSymbol = this match
      case pkg: PackageSymbol    => pkg
      case sym: TermOrTypeSymbol => sym.owner.closestPackage

    private[Symbols] final def addDeclIfDeclaringSym(decl: TermOrTypeSymbol): decl.type =
      this match
        case declaring: DeclaringSymbol => declaring.addDecl(decl)
        case _                          => ()
      decl

    private[tastyquery] final def isStatic: Boolean =
      if owner == null then true
      else owner.isStaticOwner

    @tailrec
    private def isStaticOwner: Boolean = this match
      case _: PackageSymbol => true
      case cls: ClassSymbol => cls.isModuleClass && cls.owner.isStaticOwner
      case _                => false

    private[Symbols] final def staticOwnerPrefix(using Context): NonEmptyPrefix = this match
      case pkg: PackageSymbol =>
        pkg.packageRef
      case cls: ClassSymbol if cls.isModuleClass =>
        cls.owner.staticOwnerPrefix.select(cls.moduleValue.get)
      case _ =>
        throw AssertionError(s"Cannot construct static owner prefix for non-static-owner symbol $this")
    end staticOwnerPrefix

    private def nameWithPrefix(addPrefix: Symbol => Boolean): FullyQualifiedName =
      if isPackage && (owner == null || name == nme.EmptyPackageName) then FullyQualifiedName.rootPackageName
      else
        val pre = owner
        if pre != null && addPrefix(pre) then pre.nameWithPrefix(addPrefix).mapLastOption(_.toTermName).select(name)
        else FullyQualifiedName(name :: Nil)

    final def fullName: FullyQualifiedName = nameWithPrefix(_.isStatic)

    final def isType: Boolean = this.isInstanceOf[TypeSymbol]
    final def isTerm: Boolean = this.isInstanceOf[TermSymbol]
    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageSymbol]

    final def asType: TypeSymbol = this.asInstanceOf[TypeSymbol]
    final def asTerm: TermSymbol = this.asInstanceOf[TermSymbol]
    final def asClass: ClassSymbol = this.asInstanceOf[ClassSymbol]
    final def asPackage: PackageSymbol = this.asInstanceOf[PackageSymbol]

    final def hasAnnotation(annotClass: ClassSymbol)(using Context): Boolean =
      annotations.exists(_.symbol == annotClass)

    final def getAnnotations(annotClass: ClassSymbol)(using Context): List[Annotation] =
      annotations.filter(_.symbol == annotClass)

    final def getAnnotation(annotClass: ClassSymbol)(using Context): Option[Annotation] =
      annotations.find(_.symbol == annotClass)

    override def toString: String = {
      val ownerPrefix = owner match
        case owner: DeclaringSymbol => s"${owner.name}."
        case owner: Symbol          => s"${owner.name}>"
        case null                   => ""
      val kind = this match
        case _: PackageSymbol => "package "
        case _: ClassSymbol   => if name.toTypeName.wrapsObjectName then "object class " else "class "
        case _                => if isFlagsInitialized && flags.is(Module) then "object " else ""
      s"symbol[$kind$ownerPrefix$name]"
    }
    def toDebugString = toString
  }

  sealed abstract class TermOrTypeSymbol(override val owner: Symbol) extends Symbol(owner):
    type MatchingSymbolType >: this.type <: TermOrTypeSymbol

    /** The source language in which this symbol was defined.
      *
      * The source language of a symbol may have an influence on how it is
      * erased, and therefore on how its signature is computed.
      */
    final def sourceLanguage: SourceLanguage =
      if flags.is(JavaDefined) then SourceLanguage.Java
      else if flags.is(Scala2Defined) then SourceLanguage.Scala2
      else SourceLanguage.Scala3

    /** Is this symbol private?
      *
      * A symbol is said *private* if it either `private` without scope or
      * `private[this]`.
      *
      * Private members obey different rules than other members in a number of
      * situations. In particular, they are not inherited and therefore do not
      * participate in overriding relationships.
      *
      * @return
      *   `true` iff `visibility == Visibility.Private || visibility == Visibility.PrivateThis`
      */
    final def isPrivate: Boolean = flags.is(Private)

    /** Is this symbol public?
      *
      * @return `true` iff `visibility == Visibility.Public`
      */
    final def isPublic: Boolean =
      !flags.isAnyOf(Private | Protected | Local) && privateWithin.isEmpty

    private[Symbols] final def isPrivateThis: Boolean =
      flags.isAllOf(Private | Local)

    /** The declared visibility of this symbol. */
    final def visibility: Visibility =
      if flags.is(Private) then
        if flags.is(Local) then Visibility.PrivateThis
        else Visibility.Private
      else if flags.is(Protected) then
        if flags.is(Local) then Visibility.ProtectedThis
        else
          privateWithin match
            case None        => Visibility.Protected
            case Some(scope) => Visibility.ScopedProtected(scope)
      else
        privateWithin match
          case None        => Visibility.Public
          case Some(scope) => Visibility.ScopedPrivate(scope)
    end visibility

    /** Is this symbol a final member, in the sense that it cannot be overridden?
      *
      * Classes are always final members, since Scala 3 does not allow to
      * override (shadow) inner classes.
      *
      * Other symbols are final members iff they have the `final` modifier.
      */
    final def isFinalMember: Boolean = isClass || flags.is(Final)

    /** Is this symbol generated by the compiler? */
    final def isSynthetic: Boolean = flags.is(Synthetic)

    /** Does this symbol have the `infix` modifier? */
    final def isInfix: Boolean = flags.is(Infix)

    // Overriding relationships

    /** The non-private symbol whose name and type matches the type of this symbol in the given class.
      *
      * @param inClass
      *   The class containing the result symbol's definition
      * @param siteClass
      *   The base class from which member types are computed
      */
    protected def matchingDecl(inClass: ClassSymbol, siteClass: ClassSymbol)(using Context): Option[MatchingSymbolType]

    /** If false, this symbol cannot possibly participate in an override, either as overrider or overridee. */
    private final def canMatchInheritedSymbols(using Context): Boolean =
      owner.isClass && memberCanMatchInheritedSymbols

    /** If false, this class member cannot possibly participate in an override, either as overrider or overridee. */
    private final def memberCanMatchInheritedSymbols(using Context): Boolean =
      !isConstructor && !isPrivate

    private final def isConstructor(using Context): Boolean =
      name == nme.Constructor

    /** The symbol, in class `inClass`, that is overridden by this symbol, if any. */
    final def overriddenSymbol(inClass: ClassSymbol)(using Context): Option[MatchingSymbolType] =
      if inClass == owner then Some(this)
      else if canMatchInheritedSymbols then
        val ownerClass = owner.asClass
        if ownerClass.isSubClass(inClass) then matchingDecl(inClass, siteClass = ownerClass)
        else None
      else None

    /** All symbols overridden by this symbol. */
    final def allOverriddenSymbols(using Context): Iterator[MatchingSymbolType] =
      if !canMatchInheritedSymbols then Iterator.empty
      else
        owner.asClass.linearization match
          case _ :: inherited => inherited.iterator.map(overriddenSymbol(_)).flatten
          case Nil            => Iterator.empty
    end allOverriddenSymbols

    /** The first symbol overridden by this symbol, if any. */
    final def nextOverriddenSymbol(using Context): Option[MatchingSymbolType] =
      val overridden = allOverriddenSymbols
      if overridden.hasNext then Some(overridden.next())
      else None
    end nextOverriddenSymbol

    /** The symbol overriding this symbol in given subclass `inClass`, if any. */
    final def overridingSymbol(inClass: ClassSymbol)(using Context): Option[MatchingSymbolType] =
      if inClass == owner then Some(this)
      else if canMatchInheritedSymbols && inClass.isSubClass(owner.asClass) then
        matchingDecl(inClass, siteClass = inClass)
      else None

    /** Returns true iff this symbol override `that` symbol. */
    final def overrides(that: TermOrTypeSymbol)(using Context): Boolean =
      this == that || (
        canMatchInheritedSymbols
          && that.canMatchInheritedSymbols
          && this.overriddenSymbol(that.owner.asClass).contains(that)
      )

    /** The symbol whose name and type matches the type of this symbol in the given class.
      *
      * If `inClass == this.owner`, `matchingSymbol` returns this symbol.
      * Otherwise, private members and constructors are ignored.
      *
      * Unlike the override-related methods `overriddenSymbol` and
      * `overridingSymbol`, this method can return non-empty results when
      * `inClass` and `this.owner` are unrelated.
      *
      * `siteClass` must be a common subclass of `this.owner` and `inClass`.
      *
      * @param inClass
      *   The class in which to look for a matching symbol
      * @param siteClass
      *   The base class from which member types are computed
      * @throws java.lang.IllegalArgumentException
      *   if `owner.isClass` is false, if `siteClass.isSubclass(owner.asClass)`
      *   is false, or if `siteClass.isSubclass(inClass)` is false
      */
    final def matchingSymbol(inClass: ClassSymbol, siteClass: ClassSymbol)(using Context): Option[MatchingSymbolType] =
      require(owner.isClass, s"illegal matchingSymbol on local symbol $this")
      require(siteClass.isSubClass(owner.asClass), s"site class $siteClass must be a subclass of owner $owner")
      require(siteClass.isSubClass(inClass), s"site class $siteClass must be a subclass of target class $inClass")

      if inClass == owner then Some(this)
      else if !canMatchInheritedSymbols then None
      else matchingDecl(inClass, siteClass)
    end matchingSymbol
  end TermOrTypeSymbol

  final class TermSymbol private (val name: TermName, owner: Symbol) extends TermOrTypeSymbol(owner):
    type ThisNameType = TermName
    type DefiningTreeType = ValOrDefDef | Bind
    type MatchingSymbolType = TermSymbol

    // Reference fields (checked in doCheckCompleted)
    private var myDeclaredType: TypeOrMethodic | Null = null

    // Cache fields
    private var mySignature: Signature | Null = null
    private var myTargetName: TermName | Null = null
    private var mySignedName: TermName | Null = null
    private var myParamRefss: List[Either[List[TermParamRef], List[TypeParamRef]]] | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myDeclaredType == null then failNotCompleted("declaredType was not initialized")

    private[tastyquery] final def withDeclaredType(tpe: TypeOrMethodic): this.type =
      if myDeclaredType != null then throw new IllegalStateException(s"reassignment of declared type to $this")
      myDeclaredType = tpe
      this

    def declaredType: TypeOrMethodic =
      val local = myDeclaredType
      if local != null then local
      else throw new IllegalStateException(s"$this was not assigned a declared type")

    /** Is this symbol a module val, i.e., the term of an `object`?
      *
      * @return true iff `kind == TermSymbolKind.Module`
      */
    final def isModuleVal: Boolean = flags.is(Module)

    /** Is this symbol a method, i.e., a `def`?
      *
      * @return true iff `kind == TermSymbolKind.Method`
      */
    final def isMethod: Boolean = flags.is(Method)

    /** The kind of term definition (`val`, `lazy val`, `var`, `def` or `object`).
      *
      * Parameters and bindings declared with none of these keywords are
      * considered `val`s.
      */
    final def kind: TermSymbolKind =
      if flags.is(Module) then TermSymbolKind.Module
      else if flags.is(Method) then TermSymbolKind.Def
      else if flags.is(Mutable) then TermSymbolKind.Var
      else if flags.is(Lazy) then TermSymbolKind.LazyVal
      else TermSymbolKind.Val

    /** Is this term definition an abstract member?
      *
      * An abstract member must be implemented in a subclass of its owner.
      *
      * Note that this is false for `abstract override` members.
      */
    final def isAbstractMember: Boolean = flags.is(Abstract)

    /** Is this term definition `abstract override`? */
    final def isAbstractOverride: Boolean = flags.is(AbsOverride)

    /** Is this symbol the setter of a `var`? */
    final def isSetter: Boolean = flags.isAllOf(Accessor | Method | Mutable)

    /** Is this symbol a case class field accessor? */
    final def isCaseClassAccessor: Boolean = flags.is(CaseAccessor)

    /** Is this symbol an accessor for a constructor parameter?
      *
      * Parameters of primary constructors almost always lead to two symbols:
      * the parameter itself, which is local to the constructor, and a
      * "param accessor", which is a field of the class. The param accessor is
      * private if the parameter is not introduced with `val` or `var`.
      * Otherwise, its visibility is that specified for the `val` or `var`.
      */
    final def isParamAccessor: Boolean = flags.is(ParamAccessor)

    /** Is this symbol a value `case` of an `enum`? */
    final def isEnumCase: Boolean = flags.isAllOf(Case | Enum)

    /** Is this an `extension` method? */
    final def isExtensionMethod: Boolean = flags.is(Extension)

    /** Is this symbol `given` or `using`? */
    final def isGivenOrUsing: Boolean = flags.is(Given)

    /** Is this symbol `implicit`? */
    final def isImplicit: Boolean = flags.is(Implicit)

    /** Is this symbol `inline`? */
    final def isInline: Boolean = flags.is(Inline)

    /** Is this symbol `transparent inline`? */
    final def isTransparentInline: Boolean = flags.isAllOf(Inline | Transparent)

    /** Is this symbol a macro? */
    final def isMacro: Boolean = flags.is(Macro)

    /** Is this symbol an exporter generated by an `export` statement? */
    final def isExport: Boolean = flags.is(Exported)

    /** Get the module class of this module value definition, if it exists:
      * - for `object val C` => `object class C[$]`
      */
    final def moduleClass(using Context): Option[ClassSymbol] =
      if isModuleVal then declaredType.requireType.classSymbol
      else None

    final def staticRef(using Context): TermRef =
      require(isStatic, s"Cannot construct a staticRef for non-static symbol $this")
      TermRef(owner.staticOwnerPrefix, this)

    private[tastyquery] final def declaredTypeAsSeenFrom(prefix: Prefix)(using Context): TypeOrMethodic =
      declaredType.asSeenFrom(prefix, owner)

    private def isConstructor: Boolean =
      owner.isClass && isMethod && name == nme.Constructor

    private[tastyquery] final def needsSignature: Boolean =
      declaredType.isInstanceOf[MethodicType]

    final def signature(using Context): Signature =
      val local = mySignature
      if local != null then local
      else
        val sig = Signature.fromType(declaredType, sourceLanguage, Option.when(isConstructor)(owner.asClass))
        mySignature = sig
        sig
    end signature

    final def targetName(using Context): TermName =
      val local = myTargetName
      if local != null then local
      else
        val computed = computeTargetName()
        myTargetName = computed
        computed
    end targetName

    private def computeTargetName()(using Context): TermName =
      if annotations.isEmpty then name
      else
        defn.targetNameAnnotClass match
          case None => name
          case Some(targetNameAnnotClass) =>
            getAnnotation(targetNameAnnotClass) match
              case None        => name
              case Some(annot) => termName(annot.argIfConstant(0).get.stringValue)
    end computeTargetName

    /** Returns the possibly signed name of this symbol.
      *
      * For methods with at least one term or type parameter list, this returns a `SignedName`.
      * For other terms, the returned name is not a `SignedName`.
      *
      * If the `owner` of this symbol is a `DeclaringSymbol`, then `owner.getDecl(signedName)`
      * will return this symbol. This is not always the case with `name`.
      */
    final def signedName(using Context): TermName =
      val local = mySignedName
      if local != null then local
      else
        val computed =
          if needsSignature then SignedName(name, signature, targetName)
          else name
        mySignedName = computed
        computed
    end signedName

    protected final def matchingDecl(inClass: ClassSymbol, siteClass: ClassSymbol)(using Context): Option[TermSymbol] =
      val candidates = inClass.getAllOverloadedDecls(name).filterNot(_.isPrivate)
      if candidates.isEmpty then None
      else
        val site = siteClass.thisType
        val targetType = this.declaredTypeAsSeenFrom(site)
        candidates.find { candidate =>
          // TODO Also check targetName here
          candidate.declaredTypeAsSeenFrom(site).matches(targetType)
        }
    end matchingDecl

    final def paramRefss(using Context): List[Either[List[TermParamRef], List[TypeParamRef]]] =
      def paramssOfType(tp: TypeOrMethodic): List[Either[List[TermParamRef], List[TypeParamRef]]] = tp match
        case mt: PolyType   => Right(mt.paramRefs) :: paramssOfType(mt.resultType)
        case mt: MethodType => Left(mt.paramRefs) :: paramssOfType(mt.resultType)
        case _              => Nil
      val local = myParamRefss
      if local != null then local
      else
        val refs = paramssOfType(declaredType)
        myParamRefss = refs
        refs
    end paramRefss

    /** Is this term symbol a stable member?
      *
      * A stable member is one that is known to be idempotent.
      */
    final def isStableMember(using Context): Boolean =
      !flags.isAnyOf(Method | Mutable) && !declaredType.isInstanceOf[ByNameType]
  end TermSymbol

  object TermSymbol:
    private[tastyquery] def create(name: TermName, owner: Symbol): TermSymbol =
      owner.addDeclIfDeclaringSym(TermSymbol(name, owner))

    private[tastyquery] def createNotDeclaration(name: TermName, owner: Symbol): TermSymbol =
      TermSymbol(name, owner)
  end TermSymbol

  sealed abstract class TypeSymbol protected (val name: TypeName, owner: Symbol) extends TermOrTypeSymbol(owner):
    type ThisNameType = TypeName
    type DefiningTreeType <: TypeDef | TypeTreeBind
    type MatchingSymbolType = TypeSymbol

    protected final def matchingDecl(inClass: ClassSymbol, siteClass: ClassSymbol)(using Context): Option[TypeSymbol] =
      inClass.getDecl(name).filterNot(_.isPrivate)

    final def isTypeAlias: Boolean = this match
      case sym: TypeMemberSymbol => sym.typeDef.isInstanceOf[TypeMemberDefinition.TypeAlias]
      case _                     => false

    final def isOpaqueTypeAlias: Boolean = flags.is(Opaque)

    private[tastyquery] final def topLevelRef: TypeRef =
      require(owner.isPackage, s"Cannot construct a topLevelRef for non-top-level symbol $this")
      TypeRef(owner.asPackage.packageRef, this)

    final def staticRef(using Context): TypeRef =
      require(isStatic, s"Cannot construct a staticRef for non-static symbol $this")
      TypeRef(owner.staticOwnerPrefix, this)
  end TypeSymbol

  sealed abstract class TypeSymbolWithBounds protected (name: TypeName, owner: Symbol) extends TypeSymbol(name, owner):
    type DefiningTreeType <: TypeMember | TypeParam | TypeTreeBind

    def bounds: TypeBounds

    private[tastyquery] final def boundsAsSeenFrom(prefix: Prefix)(using Context): TypeBounds =
      def default: TypeBounds =
        bounds.mapBounds(_.asSeenFrom(prefix, owner))

      this match
        case sym: ClassTypeParamSymbol =>
          prefix match
            case prefix: ThisType if prefix.cls == owner =>
              bounds
            case prefix: Type =>
              sym.argForParam(prefix, widenAbstract = true) match
                case Some(wild: WildcardTypeArg) => wild.bounds
                case Some(alias: Type)           => TypeAlias(alias)
                case None                        => default
            case NoPrefix | _: PackageRef =>
              throw InvalidProgramStructureException(s"invalid prefix $prefix for class type parameter $this")

        case sym: TypeMemberSymbol =>
          sym.typeDef match
            case TypeMemberDefinition.OpaqueTypeAlias(_, alias) =>
              /* When selecting an opaque type alias on its owner's this type,
               * it is transparent.
               */
              prefix match
                case prefix: ThisType if prefix.cls == sym.owner =>
                  // By definition, asSeenFrom would be a no-op in this case
                  TypeAlias(alias)
                case _ =>
                  default
            case _ =>
              default

        case sym: LocalTypeParamSymbol =>
          default
    end boundsAsSeenFrom
  end TypeSymbolWithBounds

  sealed abstract class TypeParamSymbol protected (name: TypeName, owner: Symbol)
      extends TypeSymbolWithBounds(name, owner):
    type DefiningTreeType >: TypeParam <: TypeParam | TypeTreeBind

    // Reference fields (checked in doCheckCompleted)
    private var myBounds: TypeBounds | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myBounds == null then failNotCompleted("bounds are not initialized")

    private[tastyquery] final def setBounds(bounds: TypeBounds): this.type =
      if myBounds != null then throw IllegalStateException(s"Trying to re-set the bounds of $this")
      myBounds = bounds
      this

    final def bounds: TypeBounds =
      val local = myBounds
      if local == null then throw IllegalStateException(s"$this was not assigned type bounds")
      else local
  end TypeParamSymbol

  final class ClassTypeParamSymbol private (name: TypeName, override val owner: ClassSymbol)
      extends TypeParamSymbol(name, owner)
      with TypeConstructorParam:
    type DefiningTreeType = TypeParam

    def declaredVariance: Variance =
      if flags.is(Covariant) then Variance.Covariant
      else if flags.is(Contravariant) then Variance.Contravariant
      else Variance.Invariant

    def variance(using Context): Variance =
      declaredVariance

    @deprecated("use localRef instead", since = "0.9.0")
    final def typeRef: TypeRef = localRef

    /** A reference to this class type param that is valid within its declaring scope. */
    final def localRef: TypeRef = TypeRef(owner.thisType, this)

    /** The argument corresponding to this class type parameter as seen from prefix `pre`.
      *
      * Can produce a WildcardTypeArg type if `widenAbstract` is true,
      * or prefix is an & or | type and parameter is non-variant.
      * Otherwise, a typebounds argument is dropped and the original type parameter
      * reference is returned.
      */
    private[tastyquery] final def argForParam(pre: Type, widenAbstract: Boolean = false)(
      using Context
    ): Option[TypeOrWildcard] =
      val cls = this.owner
      val base = pre.baseType(cls)
      base match {
        case Some(base: AppliedType) =>
          var tparams = cls.typeParams
          var args = base.args
          var idx = 0
          while (tparams.nonEmpty && args.nonEmpty) {
            if (tparams.head.eq(this))
              return Some(args.head match {
                case _: WildcardTypeArg if !widenAbstract => TypeRef(pre, this)
                case arg                                  => arg
              })
            tparams = tparams.tail
            args = args.tail
            idx += 1
          }
          None

        case Some(base: AndType) =>
          (argForParam(base.first), argForParam(base.second)) match
            case (None, tp2) =>
              tp2
            case (tp1, None) =>
              tp1
            case (Some(tp1), Some(tp2)) =>
              val variance = this.variance.sign
              val result: TypeOrWildcard = (tp1, tp2) match
                case (tp1: Type, tp2: Type) if variance != 0 =>
                  if variance > 0 then tp1 & tp2
                  else tp1 | tp2
                case _ =>
                  // Compute based on bounds, instead of returning the original reference
                  def toBounds(tp: TypeOrWildcard): TypeBounds = tp match
                    case tp: WildcardTypeArg => tp.bounds
                    case tp: Type            => TypeAlias(tp)
                  val bounds1 = toBounds(tp1)
                  val bounds2 = toBounds(tp2)
                  val mergedBounds =
                    if variance >= 0 then bounds1.intersect(bounds2)
                    else bounds1.union(bounds2)
                  mergedBounds match
                    case TypeAlias(alias)  => alias // can happen for variance == 0 if tp1 =:= tp2
                    case _: RealTypeBounds => WildcardTypeArg(mergedBounds)
              end result
              Some(result)
          end match

        /*case base: AndOrType =>
          var tp1 = argForParam(base.tp1)
          var tp2 = argForParam(base.tp2)
          val variance = this.paramVarianceSign
          if (isBounds(tp1) || isBounds(tp2) || variance == 0) {
            // compute argument as a type bounds instead of a point type
            tp1 = tp1.bounds
            tp2 = tp2.bounds
          }
          if (base.isAnd == variance >= 0) tp1 & tp2 else tp1 | tp2*/

        case _ =>
          /*if (pre.termSymbol.isPackage) argForParam(pre.select(nme.PACKAGE))
          else*/
          if (pre.isExactlyNothing) Some(pre)
          else None
      }
    end argForParam
  end ClassTypeParamSymbol

  object ClassTypeParamSymbol:
    private[tastyquery] def create(name: TypeName, owner: ClassSymbol): ClassTypeParamSymbol =
      ClassTypeParamSymbol(name, owner)
  end ClassTypeParamSymbol

  final class LocalTypeParamSymbol private (name: TypeName, owner: Symbol) extends TypeParamSymbol(name, owner):
    type DefiningTreeType = TypeParam | TypeTreeBind
  end LocalTypeParamSymbol

  object LocalTypeParamSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): LocalTypeParamSymbol =
      LocalTypeParamSymbol(name, owner)
  end LocalTypeParamSymbol

  final class TypeMemberSymbol private (name: TypeName, owner: Symbol) extends TypeSymbolWithBounds(name, owner):
    type DefiningTreeType = TypeMember

    // Reference fields (checked in doCheckCompleted)
    private var myDefinition: TypeMemberDefinition | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myDefinition == null then failNotCompleted("type member definition not initialized")

    private[tastyquery] final def withDefinition(definition: TypeMemberDefinition): this.type =
      if myDefinition != null then throw IllegalStateException(s"Reassignment of the definition of $this")
      myDefinition = definition
      this

    final def typeDef: TypeMemberDefinition =
      val local = myDefinition
      if local == null then throw IllegalStateException("$this was not assigned a definition")
      else local

    final def aliasedType: Type =
      typeDef.asInstanceOf[TypeMemberDefinition.TypeAlias].alias

    private[tastyquery] def aliasedTypeAsSeenFrom(pre: Prefix)(using Context): Type =
      aliasedType.asSeenFrom(pre, owner)

    final def bounds: TypeBounds = typeDef match
      case TypeMemberDefinition.TypeAlias(alias)           => TypeAlias(alias)
      case TypeMemberDefinition.AbstractType(bounds)       => bounds
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, _) => bounds
  end TypeMemberSymbol

  object TypeMemberSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): TypeMemberSymbol =
      owner.addDeclIfDeclaringSym(TypeMemberSymbol(name, owner))

    private[tastyquery] def createNotDeclaration(name: TypeName, owner: Symbol): TypeMemberSymbol =
      TypeMemberSymbol(name, owner)
  end TypeMemberSymbol

  enum TypeMemberDefinition:
    case TypeAlias(alias: Type)
    case AbstractType(bounds: TypeBounds)
    case OpaqueTypeAlias(bounds: TypeBounds, alias: Type)
  end TypeMemberDefinition

  sealed trait DeclaringSymbol extends Symbol {
    type DefiningTreeType <: ClassDef // for packages, it is Nothing
    type DeclType >: TermOrTypeSymbol <: Symbol

    private[Symbols] def addDecl(decl: DeclType): Unit

    @deprecated("use ClassSymbol.getAllOverloadedDecls", "0.4.0")
    def getDecls(name: Name)(using Context): List[DeclType]

    def getDecl(name: Name)(using Context): Option[DeclType]

    /** Note: this will force all trees in a package */
    def declarations(using Context): List[DeclType]
  }

  final class ClassSymbol private (name: TypeName, owner: Symbol) extends TypeSymbol(name, owner) with DeclaringSymbol {
    type DefiningTreeType = ClassDef
    type DeclType = TermOrTypeSymbol

    private type SealedChild = ClassSymbol | TermSymbol

    // Reference fields (checked in doCheckCompleted)
    private var myTypeParams: List[ClassTypeParamSymbol] | Null = null
    private var myParentsInit: (() => Context ?=> List[Type]) | Null = null
    private var myParents: List[Type] | Null = null
    private var myGivenSelfType: Option[Type] | Null = null

    // Optional reference fields
    private var mySpecialErasure: Option[() => ErasedTypeRef.ClassRef] = None
    private var myScala2SealedChildren: Option[List[Symbol | Scala2ExternalSymRef]] = None

    // DeclaringSymbol-related fields
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[TermOrTypeSymbol]] =
      mutable.HashMap[Name, mutable.HashSet[TermOrTypeSymbol]]()

    // Cache fields
    private var mySignatureName: FullyQualifiedName | Null = null
    private var myAppliedRef: Type | Null = null
    private var mySelfType: Type | Null = null
    private var myLinearization: List[ClassSymbol] | Null = null
    private var myErasure: ErasedTypeRef.ClassRef | Null = null
    private var mySealedChildren: List[SealedChild] | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myTypeParams == null then failNotCompleted("typeParams not initialized")
      if myParents == null && myParentsInit == null then failNotCompleted("parents not initialized")
      if myGivenSelfType == null then failNotCompleted("givenSelfType not initialized")

    /** The open level of this class (open, closed, sealed or final). */
    final def openLevel: OpenLevel =
      if flags.is(Final) then OpenLevel.Final
      else if flags.is(Sealed) then OpenLevel.Sealed
      else if flags.is(Open) then OpenLevel.Open
      else OpenLevel.Closed
    end openLevel

    /** Is this class a `trait`? */
    final def isTrait: Boolean = flags.is(Trait)

    /** Is this class an `enum`? */
    final def isEnum: Boolean = flags.is(Enum)

    /** Is this class abstract?
      *
      * An abstract class cannot be directly instantiated. It must be extended
      * by a concrete class before doing so.
      *
      * This is true for `trait`s and `abstract class`es.
      */
    final def isAbstractClass: Boolean = flags.isAnyOf(Abstract | Trait)

    /** Is this the hidden class of an `object`? */
    final def isModuleClass: Boolean = flags.is(Module)

    /** Is this class a `case class`? */
    final def isCaseClass: Boolean = flags.is(Case)

    /** Is this a class a `transparent trait`? */
    final def isTransparentTrait: Boolean = flags.isAllOf(Trait | Transparent)

    private[tastyquery] def isValueClass(using Context): Boolean =
      parents.nonEmpty && parents.head.classSymbol.exists(_ == defn.AnyValClass)

    private[tastyquery] def isDerivedValueClass(using Context): Boolean =
      isValueClass && this != defn.AnyValClass && !defn.isPrimitiveValueClass(this)

    /** Get the companion class of this class, if it exists:
      * - for `class C` => `object class C[$]`
      * - for `object class C[$]` => `class C`
      */
    final def companionClass(using Context): Option[ClassSymbol] = owner match
      case scope: DeclaringSymbol =>
        scope.getDecl(this.name.companionName).collect { case sym: ClassSymbol =>
          sym
        }
      case _ => None // not possible yet for local symbols

    /** Get the module value of this module class definition, if it exists:
      * - for `object class C[$]` => `object val C`
      */
    final def moduleValue(using Context): Option[TermSymbol] = owner match
      case scope: DeclaringSymbol if this.isModuleClass =>
        scope.getDecl(this.name.sourceObjectName).collect { case sym: TermSymbol =>
          sym
        }
      case _ => None // not possible yet for local symbols

    /** The name of this class as used in `Signature`s.
      *
      * This needs to match the behavior of `classSymbol.fullName` in dotc.
      * Eventually that goes to `fullNameSeparate(Qualified, Qualified, name)`,
      * which contains this comment:
      *
      * > Drops package objects. Represents each term in the owner chain by a simple `_$`.
      *
      * The code actually represents each *non-class* in the owner chain by a simple `_$`.
      * Moreover, there does not seem to be any code that actually drops package objects,
      * and evidence suggests that it does not.
      */
    private[tastyquery] final def signatureName: FullyQualifiedName =
      def computeErasedName(owner: Symbol, name: TypeName): FullyQualifiedName = owner match
        case owner: PackageSymbol =>
          owner.fullName.select(name)

        case owner: ClassSymbol =>
          owner.signatureName.mapLast(_.toTermName).select(name)

        case owner: TermOrTypeSymbol =>
          // Replace non-class non-package owners by simple `_$`
          val filledName = name.toTermName.asSimpleName.prepend("_$").toTypeName
          computeErasedName(owner.owner, filledName)
      end computeErasedName

      val local = mySignatureName
      if local != null then local
      else
        val computed = computeErasedName(owner, name)
        mySignatureName = computed
        computed
    end signatureName

    private[tastyquery] final def withTypeParams(tparams: List[ClassTypeParamSymbol]): this.type =
      if myTypeParams != null then throw new IllegalStateException(s"reassignment of type parameters to $this")
      myTypeParams = tparams
      this

    final def typeParams: List[ClassTypeParamSymbol] =
      val local = myTypeParams
      if local == null then throw new IllegalStateException(s"type params not initialized for $this")
      else local

    private[tastyquery] final def withParentsDirect(parents: List[Type]): this.type =
      if myParentsInit != null || myParents != null then
        throw IllegalStateException(s"reassignment of parents of $this")
      myParents = parents
      this

    private[tastyquery] final def withParentsDelayed(parentsInit: () => Context ?=> List[Type]): this.type =
      if myParentsInit != null || myParents != null then
        throw IllegalStateException(s"reassignment of parents of $this")
      myParentsInit = parentsInit
      this

    final def parents(using Context): List[Type] =
      val localParents = myParents
      if localParents != null then localParents
      else
        val localParentsInit = myParentsInit
        if localParentsInit != null then
          val parents = localParentsInit()
          myParents = parents
          myParentsInit = null
          parents
        else throw IllegalStateException(s"$this was not assigned parents")
    end parents

    def parentClasses(using Context): List[ClassSymbol] =
      parents.map(tpe =>
        tpe.classSymbol.getOrElse {
          throw InvalidProgramStructureException(s"Non-class type $tpe in parents of $this")
        }
      )

    private[tastyquery] final def withGivenSelfType(givenSelfType: Option[Type]): this.type =
      if myGivenSelfType != null then throw new IllegalStateException(s"reassignment of givenSelfType for $this")
      myGivenSelfType = givenSelfType
      this

    final def givenSelfType: Option[Type] =
      val local = myGivenSelfType
      if local == null then throw new IllegalStateException(s"givenSelfType not initialized for $this")
      else local

    @deprecated("use appliedRefInsideThis instead", since = "0.9.0")
    final def appliedRef: Type = appliedRefInsideThis

    final def appliedRefInsideThis: Type =
      val local = myAppliedRef
      if local != null then local
      else
        val computed =
          if typeParams.isEmpty then localRef
          else AppliedType(localRef, typeParams.map(_.localRef))
        myAppliedRef = computed
        computed
    end appliedRefInsideThis

    final def selfType: Type =
      val local = mySelfType
      if local != null then local
      else
        val computed = givenSelfType match
          case None =>
            appliedRefInsideThis
          case Some(givenSelf) =>
            if isModuleClass then givenSelf
            else AndType(givenSelf, appliedRefInsideThis)
        mySelfType = computed
        computed
    end selfType

    final def linearization(using Context): List[ClassSymbol] =
      val local = myLinearization
      if local != null then local
      else
        val computed = computeLinearization()
        myLinearization = computed
        computed

    private def computeLinearization()(using Context): List[ClassSymbol] =
      val parentsLin = parentClasses.foldLeft[List[ClassSymbol]](Nil) { (lin, parent) =>
        parent.linearization.filter(c => !lin.contains(c)) ::: lin
      }
      this :: parentsLin

    @deprecated("use isSubClass instead", since = "0.9.0")
    final def isSubclass(that: ClassSymbol)(using Context): Boolean =
      isSubClass(that)

    final def isSubClass(that: ClassSymbol)(using Context): Boolean =
      linearization.contains(that)

    private[tastyquery] final def withSpecialErasure(specialErasure: () => ErasedTypeRef.ClassRef): this.type =
      if mySpecialErasure.isDefined then throw IllegalStateException(s"reassignment of the special erasure of $this")
      if myErasure != null then throw IllegalStateException(s"the erasure of $this was already computed")
      mySpecialErasure = Some(specialErasure)
      this

    /** The erasure of this class; nonsensical for `scala.Array`. */
    private[tastyquery] final def erasure(using Context): ErasedTypeRef.ClassRef =
      val local = myErasure
      if local != null then local
      else
        val computed = computeErasure()
        myErasure = computed
        computed
    end erasure

    private def computeErasure()(using Context): ErasedTypeRef.ClassRef =
      mySpecialErasure match
        case Some(special) =>
          special()
        case None =>
          if owner == defn.scalaPackage then
            // The classes with special erasures that are loaded from Scala 2 pickles or .tasty files
            name match
              case tpnme.AnyVal | tpnme.TupleCons    => defn.ObjectClass.erasure
              case tpnme.Tuple | tpnme.NonEmptyTuple => defn.ProductClass.erasure
              case _                                 => ErasedTypeRef.ClassRef(this)
          else ErasedTypeRef.ClassRef(this)
    end computeErasure

    // DeclaringSymbol implementation

    private[Symbols] final def addDecl(decl: TermOrTypeSymbol): Unit =
      val set = myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet)
      if decl.isType then assert(set.isEmpty, s"trying to add a second entry $decl for type name ${decl.name} in $this")
      set += decl

    @deprecated("use getAllOverloadedDecls", "0.4.0")
    final def getDecls(name: Name)(using Context): List[TermOrTypeSymbol] =
      name match
        case name: SignedName => getDecl(name).toList
        case name: TermName   => getAllOverloadedDecls(name)
        case name             => getDecl(name).toList

    final def getDecl(name: Name)(using Context): Option[TermOrTypeSymbol] =
      name match
        case overloaded: SignedName =>
          distinguishOverloaded(overloaded)
        case name =>
          myDeclarations.get(name) match
            case Some(decls) =>
              decls.find {
                case decl: TermSymbol if decl.needsSignature => false
                case _                                       => true
              }
            case _ => None
    end getDecl

    private final def distinguishOverloaded(overloaded: SignedName)(using Context): Option[TermOrTypeSymbol] =
      myDeclarations.get(overloaded.underlying) match
        case Some(overloads) =>
          overloads.find {
            case decl: TermSymbol =>
              overloaded == decl.signedName
            case _ =>
              false
          }
        case None => None
    end distinguishOverloaded

    final def getDecl(name: TypeName)(using Context): Option[TypeSymbol] =
      myDeclarations.get(name) match
        case Some(decls) =>
          assert(decls.sizeIs == 1, decls)
          Some(decls.head.asType)
        case None =>
          None
    end getDecl

    final def getDecl(name: TermName)(using Context): Option[TermSymbol] =
      getDecl(name: Name).map(_.asTerm)

    final def findDecl(name: Name)(using Context): TermOrTypeSymbol =
      getDecl(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    final def findDecl(name: TypeName)(using Context): TypeSymbol =
      getDecl(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    final def findDecl(name: TermName)(using Context): TermSymbol =
      getDecl(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    /** Returns a list of all the overloaded declarations with the given unsigned name.
      *
      * If there is no declaration with the given unsigned name, this method
      * returns `Nil`.
      *
      * @throws java.lang.IllegalArgumentException
      *   if the provided `name` is a [[Names.SignedName]]
      */
    final def getAllOverloadedDecls(name: TermName)(using Context): List[TermSymbol] =
      name match
        case name: SignedName => throw IllegalArgumentException(s"Illegal SignedName argument: $name")
        case _                => myDeclarations.get(name).fold(Nil)(_.toList.map(_.asTerm))
    end getAllOverloadedDecls

    /** Returns a list of all the overloaded declarations with the given unsigned name.
      *
      * @throws tastyquery.Exceptions.MemberNotFoundException
      *   if there is no declaration with the given unsigned name
      * @throws java.lang.IllegalArgumentException
      *   if the provided `name` is a [[Names.SignedName]]
      */
    final def findAllOverloadedDecls(name: TermName)(using Context): List[TermSymbol] =
      getAllOverloadedDecls(name) match
        case Nil   => throw MemberNotFoundException(this, name)
        case decls => decls
    end findAllOverloadedDecls

    /** Convenience method to get a non-overloaded decl from its unsigned name.
      *
      * If there are multiple or no overload with the given unsigned name, this
      * method returns `None`.
      *
      * @throws java.lang.IllegalArgumentException
      *   if the provided `name` is a [[Names.SignedName]]
      */
    final def getNonOverloadedDecl(name: TermName)(using Context): Option[TermSymbol] =
      myDeclarations.get(name) match
        case Some(decls) =>
          if decls.sizeIs == 1 then Some(decls.head.asTerm)
          else None
        case None =>
          name match
            case _: SignedName => throw IllegalArgumentException(s"Illegal SignedName argument: $name")
            case _             => None
    end getNonOverloadedDecl

    /** Convenience method to find a non-overloaded decl from its unsigned name.
      *
      * @throws tastyquery.Exceptions.MemberNotFoundException
      *   if there are multiple or no overload with the given unsigned name
      * @throws java.lang.IllegalArgumentException
      *   if the provided `name` is a [[Names.SignedName]]
      */
    final def findNonOverloadedDecl(name: TermName)(using Context): TermSymbol =
      getNonOverloadedDecl(name).getOrElse {
        throw MemberNotFoundException(this, name, s"Multiple overloads or no overload of '$name' in $this")
      }
    end findNonOverloadedDecl

    final def declarations(using Context): List[TermOrTypeSymbol] =
      myDeclarations.values.toList.flatten

    // Member lookup, including inherited members

    final def getMember(name: Name)(using Context): Option[TermOrTypeSymbol] =
      findMember(appliedRefInsideThis, name)

    final def getMember(name: TermName)(using Context): Option[TermSymbol] =
      getMember(name: Name).map(_.asTerm)

    final def getMember(name: TypeName)(using Context): Option[TypeSymbol] =
      getMember(name: Name).map(_.asType)

    final def findMember(name: Name)(using Context): TermOrTypeSymbol =
      getMember(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    final def findMember(name: TermName)(using Context): TermSymbol =
      getMember(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    final def findMember(name: TypeName)(using Context): TypeSymbol =
      getMember(name).getOrElse {
        throw MemberNotFoundException(this, name)
      }

    // Type-related things

    private[tastyquery] final def initParents: Boolean =
      myTypeParams != null

    // Partial internal guarantee that we follow the right shape
    private type BaseType = TypeRef | AppliedType

    private def asBaseType(tpe: Type): BaseType = tpe match
      case tpe: BaseType => tpe
      case _             => throw AssertionError(s"baseType internally produced an invalid shape: $tpe")
    end asBaseType

    private val baseTypeForClassCache = mutable.AnyRefMap.empty[ClassSymbol, Option[BaseType]]

    /** Cached core lookup of `this.baseTypeOf(clsOwner.this.cls)`.
      *
      * We can safely cache it because it only depends on `this` and `cls`,
      * which are both `ClassSymbol`s, so there is a finite number of them,
      * and they have meaningful equality semantics.
      */
    private def baseTypeForClass(cls: ClassSymbol)(using Context): Option[BaseType] =
      def foldGlb(bt: Option[BaseType], ps: List[Type]): Option[BaseType] =
        ps.foldLeft(bt)((bt, p) => baseTypeCombine(bt, baseTypeOf(p), meet = true))

      baseTypeForClassCache.getOrElseUpdate(
        cls,
        if cls.isSubClass(this) then
          if this.isStatic && this.typeParams.isEmpty then Some(this.localRef)
          else foldGlb(None, cls.parents)
        else None
      )
    end baseTypeForClass

    /** Computes the (unapplied) baseType of a class type constructor.
      *
      * Precondition: `tp.optSymbol == Some(tpCls)`.
      */
    private def baseTypeOfClassTypeRef(tp: TypeRef, tpCls: ClassSymbol)(using Context): Option[BaseType] =
      def isOwnThis = tp.prefix match
        case prefix: ThisType   => prefix.cls == tpCls.owner
        case prefix: PackageRef => prefix.symbol == tpCls.owner
        case NoPrefix           => true
        case _                  => false

      val baseTypeOnOwnThisOpt = baseTypeForClass(tpCls)
      if isOwnThis then baseTypeOnOwnThisOpt
      else
        baseTypeOnOwnThisOpt.map { (baseTypeOnOwnThis: BaseType) =>
          asBaseType(baseTypeOnOwnThis.asSeenFrom(tp.prefix, tpCls.owner.asInstanceOf[DeclaringSymbol]))
        }
    end baseTypeOfClassTypeRef

    /** Compute tp.baseType(this) */
    private[tastyquery] final def baseTypeOf(tp: Type)(using Context): Option[TypeRef | AppliedType] = tp match
      case tp @ TypeRef.OfClass(tpCls) =>
        if tpCls == this then Some(tp)
        else baseTypeOfClassTypeRef(tp, tpCls)

      case tp: AppliedType =>
        tp.tycon match
          case tycon @ TypeRef.OfClass(tyconCls) =>
            if tyconCls == this then Some(tp)
            else
              val baseTyconOpt = baseTypeOfClassTypeRef(tycon, tyconCls)
              baseTyconOpt.map { (baseTycon: BaseType) =>
                asBaseType(baseTycon.substClassTypeParams(tyconCls.typeParams, tp.args))
              }
          case tycon =>
            baseTypeOf(tp.superType)

      case tp: TypeProxy =>
        baseTypeOf(tp.superType)

      case tp: AndType =>
        // TODO? Opt when this.isStatic && tp.derivesFrom(this) && this.typeParams.isEmpty then this.typeRef
        baseTypeCombine(baseTypeOf(tp.first), baseTypeOf(tp.second), meet = true)

      case tp: OrType =>
        baseTypeCombine(baseTypeOf(tp.first), baseTypeOf(tp.second), meet = false)

      case _: NothingType | _: AnyKindType | _: TypeLambda =>
        None

      case _: CustomTransientGroundType =>
        None
    end baseTypeOf

    private def baseTypeCombine(baseType1: Option[BaseType], baseType2: Option[BaseType], meet: Boolean)(
      using Context
    ): Option[BaseType] =
      (baseType1, baseType2) match
        case (None, _) => if meet then baseType2 else None
        case (_, None) => if meet then baseType1 else None

        case (Some(tp1: TypeRef), Some(tp2: TypeRef)) =>
          if baseTypeCheckUnapplied(tp1, tp2) then baseType1
          else None

        case (Some(tp1: AppliedType), Some(tp2: AppliedType)) =>
          (tp1.tycon, tp2.tycon) match
            case (tycon1: TypeRef, tycon2: TypeRef) if baseTypeCheckUnapplied(tycon1, tycon2) =>
              baseTypeCombineArgs(tp1.args, tp2.args, typeParams, meet) match
                case Some(args) =>
                  if args eq tp1.args then baseType1
                  else Some(AppliedType(tycon1, args))
                case None =>
                  None
            case _ =>
              None

        case _ =>
          None
    end baseTypeCombine

    private def baseTypeCheckUnapplied(tp1: TypeRef, tp2: TypeRef)(using Context): Boolean =
      assert(tp1.optSymbol.contains(this) && tp2.optSymbol.contains(this))
      (tp1.prefix, tp2.prefix) match
        case (prefix1: Type, prefix2: Type) =>
          prefix1.isSameType(prefix2)
        case _ =>
          // Since both TypeRef's point to this class, NoSymbol's and PackageRef's must be the same by construction
          true
    end baseTypeCheckUnapplied

    private def baseTypeCombineArgs(
      args1: List[TypeOrWildcard],
      args2: List[TypeOrWildcard],
      tparams: List[ClassTypeParamSymbol],
      meet: Boolean
    )(using Context): Option[List[TypeOrWildcard]] =
      if tparams.isEmpty then Some(Nil)
      else
        val arg1 = args1.head
        val arg2 = args2.head
        val tparam = tparams.head
        val combinedArg = tparam.variance.sign match
          case 1 =>
            if meet then arg1.intersect(arg2)
            else arg1.union(arg2)
          case -1 =>
            if meet then arg1.union(arg2)
            else arg1.intersect(arg2)
          case 0 =>
            if arg1.isSameTypeOrWildcard(arg2) then arg1
            else return None
        val combinedTail = baseTypeCombineArgs(args1.tail, args2.tail, tparams.tail, meet) match
          case Some(combined) => combined
          case None           => return None
        val result =
          if (combinedArg eq arg1) && (combinedTail eq args1.tail) then args1
          else combinedArg :: combinedTail
        Some(result)
    end baseTypeCombineArgs

    private[tastyquery] final def findMember(pre: NonEmptyPrefix, name: Name)(using Context): Option[TermOrTypeSymbol] =
      def lookup(lin: List[ClassSymbol]): Option[TermOrTypeSymbol] = lin match
        case parentCls :: linRest =>
          parentCls.getDecl(name) match
            case Some(sym) if !sym.isPrivate =>
              Some(sym)
            case _ =>
              lookup(linRest)
        case Nil =>
          None
      end lookup

      def isOwnThis: Boolean = pre match
        case pre: ThisType if pre.cls == this => true
        case _                                => false

      getDecl(name) match
        case some @ Some(sym) if !sym.isPrivateThis || isOwnThis =>
          some
        case _ =>
          if name == nme.Constructor then None
          else lookup(linearization.tail)
    end findMember

    private[tastyquery] def resolveMember(name: Name, pre: NonEmptyPrefix)(using Context): ResolveMemberResult =
      findMember(pre, name) match
        case Some(sym: TermSymbol) =>
          ResolveMemberResult.TermMember(sym :: Nil, sym.declaredTypeAsSeenFrom(pre), sym.isStableMember)
        case Some(sym: ClassSymbol) =>
          ResolveMemberResult.ClassMember(sym)
        case Some(sym: TypeSymbolWithBounds) =>
          ResolveMemberResult.TypeMember(sym :: Nil, sym.boundsAsSeenFrom(pre))
        case None =>
          ResolveMemberResult.NotFound
    end resolveMember

    private[tastyquery] def resolveMatchingMember(
      name: SignedName,
      pre: NonEmptyPrefix,
      typePredicate: TypeOrMethodic => Boolean
    )(using Context): ResolveMemberResult =
      def lookup(lin: List[ClassSymbol]): ResolveMemberResult = lin match
        case parentCls :: linRest =>
          var overloadsRest = parentCls.getAllOverloadedDecls(name.underlying)
          while overloadsRest.nonEmpty do
            val decl = overloadsRest.head
            val matches =
              decl.isPublic
                && decl.needsSignature
                && name.sig.paramsCorrespond(decl.signature)
            if matches then
              val tpe = decl.declaredTypeAsSeenFrom(pre)
              if typePredicate(tpe) then return ResolveMemberResult.TermMember(decl :: Nil, tpe, decl.isStableMember)
            end if
            overloadsRest = overloadsRest.tail
          end while
          lookup(linRest)

        case Nil =>
          ResolveMemberResult.NotFound
      end lookup

      lookup(linearization)
    end resolveMatchingMember

    private var myLocalRef: TypeRef | Null = null

    /** A reference to this (unapplied) class type that is valid within its declaring scope. */
    private[tastyquery] final def localRef: TypeRef =
      val local = myLocalRef
      if local != null then local
      else
        val pre = owner match
          case owner: PackageSymbol => owner.packageRef
          case owner: ClassSymbol   => owner.thisType
          case _                    => NoPrefix
        val computed = TypeRef(pre, this)
        myLocalRef = computed
        computed
    end localRef

    private var myThisType: ThisType | Null = null

    /** The `ThisType` for this class, as visible from inside this class. */
    final def thisType: ThisType =
      val local = myThisType
      if local != null then local
      else
        val computed = ThisType(localRef)
        myThisType = computed
        computed
    end thisType

    /** Directly sets the sealed children of this class.
      *
      * This is only used by the Scala 2 unpickler.
      */
    private[tastyquery] def setScala2SealedChildren(children: List[Symbol | Scala2ExternalSymRef])(
      using Context
    ): Unit =
      if !flags.is(Scala2Defined) then
        throw IllegalArgumentException(s"Illegal $this.setScala2SealedChildren($children) for non-Scala 2 class")
      if myScala2SealedChildren.isDefined then
        throw IllegalStateException(s"Scala 2 sealed children were already set for $this")
      if mySealedChildren != null then throw IllegalStateException(s"Sealed children were already computed for $this")
      myScala2SealedChildren = Some(children)
    end setScala2SealedChildren

    /** The direct children of a sealed class (including enums).
      *
      * If `this.is(Sealed)` is false, this method returns `Nil`.
      *
      * Otherwise, each element of the list is either:
      *
      * - a non-module class that extends this class (including enum class cases), or
      * - a module value whose module class extends this class, or
      * - an enum val case for this enum class.
      *
      * The results are ordered by their declaration order in the source.
      */
    final def sealedChildren(using Context): List[ClassSymbol | TermSymbol] =
      val local = mySealedChildren
      if local != null then local
      else
        val computed: List[SealedChild] =
          if !flags.is(Sealed) then Nil
          else computeSealedChildren()
        mySealedChildren = computed
        computed
    end sealedChildren

    private def computeSealedChildren()(using Context): List[SealedChild] =
      myScala2SealedChildren match
        case Some(scala2Children) =>
          scala2Children.map(extractSealedChildFromScala2(_))
        case None =>
          defn.internalChildAnnotClass match
            case None =>
              Nil
            case Some(annotClass) =>
              getAnnotations(annotClass).map(extractSealedChildFromChildAnnot(_))
    end computeSealedChildren

    private def extractSealedChildFromScala2(scala2Child: Symbol | Scala2ExternalSymRef)(using Context): SealedChild =
      val sym = scala2Child match
        case sym: Symbol                    => sym
        case external: Scala2ExternalSymRef => NamedType.resolveScala2ExternalRef(external)

      sym match
        case sym: ClassSymbol                   => sym
        case sym: TermSymbol if sym.isModuleVal => sym
        case sym =>
          throw InvalidProgramStructureException(s"Unexpected symbol $sym for a sealed child of $this")
    end extractSealedChildFromScala2

    private def extractSealedChildFromChildAnnot(annot: Annotation)(using Context): SealedChild =
      annot.tree.tpe match
        case tpe: AppliedType =>
          tpe.args match
            case TypeRef.OfClass(childCls) :: Nil =>
              childCls
            case (childRef: TermRef) :: Nil if childRef.symbol.isModuleVal || childRef.symbol.isEnumCase =>
              childRef.symbol
            case _ =>
              throw InvalidProgramStructureException(s"Unexpected type $tpe for $annot")
        case tpe =>
          throw InvalidProgramStructureException(s"Unexpected type $tpe for $annot")
    end extractSealedChildFromChildAnnot
  }

  object ClassSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): ClassSymbol =
      owner.addDeclIfDeclaringSym(ClassSymbol(name, owner))

    private[tastyquery] def createNotDeclaration(name: TypeName, owner: Symbol): ClassSymbol =
      ClassSymbol(name, owner)

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol, flags: FlagSet, span: Span)(
      using Context
    ): ClassSymbol =
      // TODO Store the `span`
      createRefinedClassSymbol(owner, flags)

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol, flags: FlagSet)(using Context): ClassSymbol =
      val cls = ClassSymbol(tpnme.RefinedClassMagic, owner) // by-pass `owner.addDeclIfDeclaringSym`
      cls
        .withTypeParams(Nil)
        .withParentsDirect(defn.ObjectType :: Nil)
        .withGivenSelfType(None)
        .withFlags(flags, None)
        .setAnnotations(Nil)
      cls.checkCompleted()
      cls
  end ClassSymbol

  final class PackageSymbol private (val name: SimpleName, override val owner: PackageSymbol | Null)
      extends Symbol(owner)
      with DeclaringSymbol {
    type ThisNameType = SimpleName
    type DefiningTreeType = Nothing
    type DeclType = Symbol

    // DeclaringSymbol-related fields
    private var rootsInitialized: Boolean = false
    private val myDeclarations = mutable.HashMap[Name, Symbol]()

    // Cache fields
    val packageRef: PackageRef = new PackageRef(this)
    private var myAllPackageObjectDecls: List[ClassSymbol] | Null = null

    this.withFlags(EmptyFlagSet, None)
    this.setAnnotations(Nil)

    private[tastyquery] def getPackageDeclOrCreate(name: SimpleName): PackageSymbol =
      getPackageDecl(name).getOrElse {
        assert(name != nme.EmptyPackageName, s"Trying to create a subpackage $name of $this")
        val pkg = PackageSymbol(name, this)
        addDecl(pkg)
        pkg
      }
    end getPackageDeclOrCreate

    /** Is this the root package? */
    final def isRootPackage: Boolean = owner == null

    /** Gets the subpackage with the specified `name`, if it exists.
      *
      * If this package contains a subpackage with the name `name`, returns
      * `Some(subpackage)`. Otherwise, returns `None`.
      *
      * If there exists another kind of declaration with the given `name`, this
      * method returns `None` (instead of, for example, throwing).
      *
      * @note
      *   Performance guarantee: This method does not try to load non-package
      *   symbols from the classpath.
      */
    final def getPackageDecl(name: SimpleName): Option[PackageSymbol] =
      /* All subpackages are created eagerly when initializing contexts,
       * so we can directly access myDeclarations here.
       */
      myDeclarations.get(name).collect { case pkg: PackageSymbol =>
        pkg
      }
    end getPackageDecl

    private[Symbols] final def addDecl(decl: Symbol): Unit =
      assert(!myDeclarations.contains(decl.name), s"trying to add a second entry $decl for name ${decl.name} in $this")
      myDeclarations(decl.name) = decl

    @deprecated("use getDecl; members of packages are never overloaded", "0.4.0")
    final def getDecls(name: Name)(using Context): List[Symbol] =
      getDecl(name).toList

    private final def ensureRootsInitialized()(using Context): Unit =
      if !rootsInitialized then
        ctx.classloader.scanPackage(this)
        rootsInitialized = true

    final def getDecl(name: Name)(using Context): Option[Symbol] =
      myDeclarations.get(name).orElse {
        ensureRootsInitialized()
        if ctx.classloader.loadRoot(this, name) then myDeclarations.get(name)
        else None
      }
    end getDecl

    final def declarations(using Context): List[Symbol] =
      ensureRootsInitialized()
      ctx.classloader.loadAllRoots(this)
      myDeclarations.values.toList

    // See PackageRef.findMember
    private[tastyquery] def allPackageObjectDecls()(using Context): List[ClassSymbol] =
      val local = myAllPackageObjectDecls
      if local != null then local
      else
        val computed = computeAllPackageObjectDecls()
        myAllPackageObjectDecls = computed
        computed
    end allPackageObjectDecls

    private def computeAllPackageObjectDecls()(using Context): List[ClassSymbol] =
      ensureRootsInitialized()
      ctx.classloader.loadAllPackageObjectRoots(this)
      myDeclarations.valuesIterator.collect {
        case cls: ClassSymbol if cls.name.isPackageObjectClassName => cls
      }.toList
        .sortBy(_.name.toTermName.stripObjectSuffix.asSimpleName) // sort for determinism
    end computeAllPackageObjectDecls
  }

  object PackageSymbol:
    private[tastyquery] def createRoots(): (PackageSymbol, PackageSymbol) =
      val root = PackageSymbol(nme.RootName, null)
      root.rootsInitialized = true
      val empty = PackageSymbol(nme.EmptyPackageName, root)
      root.addDecl(empty)
      (root, empty)
  end PackageSymbol
}
