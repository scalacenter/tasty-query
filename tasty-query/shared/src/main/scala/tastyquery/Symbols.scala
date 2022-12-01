package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Spans.*
import tastyquery.Trees.*
import tastyquery.Types.*
import tastyquery.Variances.*

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
    private var myPrivateWithin: Option[Symbol] = None
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

    final def tree(using Context): Option[DefiningTreeType] =
      myTree

    private[tastyquery] final def withFlags(flags: FlagSet, privateWithin: Option[Symbol]): this.type =
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

    final def privateWithin: Option[Symbol] =
      if isFlagsInitialized then myPrivateWithin
      else throw IllegalStateException(s"flags of $this have not been initialized")

    final def flags: FlagSet =
      if isFlagsInitialized then myFlags
      else throw IllegalStateException(s"flags of $this have not been initialized")

    final def is(flag: Flag): Boolean =
      flags.is(flag)

    final def isAllOf(testFlags: FlagSet): Boolean =
      flags.isAllOf(testFlags)

    final def isAnyOf(testFlags: FlagSet): Boolean =
      flags.isAnyOf(testFlags)

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
      case cls: ClassSymbol => cls.is(Module) && cls.owner.isStaticOwner
      case _                => false

    private[Symbols] final def staticOwnerPrefix(using Context): Type = this match
      case pkg: PackageSymbol =>
        pkg.packageRef
      case cls: ClassSymbol if cls.is(Module) =>
        cls.owner.staticOwnerPrefix.select(cls.moduleValue.get)
      case _ =>
        throw AssertionError(s"Cannot construct static owner prefix for non-static-owner symbol $this")
    end staticOwnerPrefix

    private def nameWithPrefix(addPrefix: Symbol => Boolean): FullyQualifiedName =
      if isRoot then FullyQualifiedName.rootPackageName
      else
        val pre = owner
        if pre != null && addPrefix(pre) then pre.nameWithPrefix(addPrefix).mapLastOption(_.toTermName).select(name)
        else FullyQualifiedName(name :: Nil)

    final def fullName: FullyQualifiedName = nameWithPrefix(_.isStatic)
    private[tastyquery] final def erasedName: FullyQualifiedName = nameWithPrefix(_ => true)

    final def isType: Boolean = this.isInstanceOf[TypeSymbol]
    final def isTerm: Boolean = this.isInstanceOf[TermSymbol]

    final def isDeclaringSymbol: Boolean = this.isInstanceOf[DeclaringSymbol]
    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageSymbol]
    final def isRoot: Boolean = isPackage && owner == null

    final def asType: TypeSymbol = this.asInstanceOf[TypeSymbol]
    final def asTerm: TermSymbol = this.asInstanceOf[TermSymbol]
    final def asDeclaringSymbol: DeclaringSymbol = this.asInstanceOf[DeclaringSymbol]
    final def asClass: ClassSymbol = this.asInstanceOf[ClassSymbol]
    final def asPackage: PackageSymbol = this.asInstanceOf[PackageSymbol]

    private[tastyquery] final def memberIsOverloaded(name: SignedName): Boolean = this match
      case scope: ClassSymbol => scope.hasOverloads(name)
      case _                  => false

    override def toString: String = {
      val kind = this match
        case _: PackageSymbol => "package "
        case _: ClassSymbol   => if name.toTypeName.wrapsObjectName then "object class " else "class "
        case _                => if isFlagsInitialized && is(Module) then "object " else ""
      s"symbol[$kind$name]"
    }
    def toDebugString = toString
  }

  sealed abstract class TermOrTypeSymbol(override val owner: Symbol) extends Symbol(owner):
    // Overriding relationships

    /** The non-private symbol whose name and type matches the type of this symbol in the given class.
      *
      * @param inClass
      *   The class containing the result symbol's definition
      * @param siteClass
      *   The base class from which member types are computed
      */
    private final def matchingDecl(inClass: ClassSymbol, siteClass: ClassSymbol)(using Context): Option[Symbol] =
      this match
        case self: TypeSymbol =>
          inClass.getDecl(self.name).filterNot(_.is(Private))
        case self: TermSymbol =>
          val candidates = inClass.getAllOverloadedDecls(self.name).filterNot(_.is(Private))
          if candidates.isEmpty then None
          else
            val site = siteClass.thisType
            val targetType = self.declaredTypeAsSeenFrom(site)
            candidates.find { candidate =>
              // TODO Also check targetName here
              candidate.declaredTypeAsSeenFrom(site).matchesLoosely(targetType)
            }
    end matchingDecl

    /** If false, this symbol cannot possibly participate in an override, either as overrider or overridee. */
    private final def canMatchInheritedSymbols(using Context): Boolean =
      owner.isClass && memberCanMatchInheritedSymbols

    /** If false, this class member cannot possibly participate in an override, either as overrider or overridee. */
    private final def memberCanMatchInheritedSymbols(using Context): Boolean =
      !isConstructor && !is(Private)

    private final def isConstructor(using Context): Boolean =
      name == nme.Constructor

    /** The symbol, in class `inClass`, that is overridden by this symbol, if any. */
    final def overriddenSymbol(inClass: ClassSymbol)(using Context): Option[Symbol] =
      if inClass == owner then Some(this)
      else if canMatchInheritedSymbols then
        val ownerClass = owner.asClass
        if ownerClass.isSubclass(inClass) then matchingDecl(inClass, siteClass = ownerClass)
        else None
      else None

    /** All symbols overridden by this symbol. */
    final def allOverriddenSymbols(using Context): Iterator[Symbol] =
      if !canMatchInheritedSymbols then Iterator.empty
      else
        owner.asClass.linearization match
          case _ :: inherited => inherited.iterator.map(overriddenSymbol(_)).flatten
          case Nil            => Iterator.empty
    end allOverriddenSymbols

    /** The first symbol overridden by this symbol, if any. */
    final def nextOverriddenSymbol(using Context): Option[Symbol] =
      val overridden = allOverriddenSymbols
      if overridden.hasNext then Some(overridden.next())
      else None
    end nextOverriddenSymbol

    /** The symbol overriding this symbol in given subclass `inClass`, if any. */
    final def overridingSymbol(inClass: ClassSymbol)(using Context): Option[Symbol] =
      if inClass == owner then Some(this)
      else if canMatchInheritedSymbols && inClass.isSubclass(owner.asClass) then
        matchingDecl(inClass, siteClass = inClass)
      else None
  end TermOrTypeSymbol

  final class TermSymbol private (val name: TermName, owner: Symbol) extends TermOrTypeSymbol(owner):
    type ThisNameType = TermName
    type DefiningTreeType = ValOrDefDef | Bind

    // Reference fields (checked in doCheckCompleted)
    private var myDeclaredType: Type | Null = null

    // Cache fields
    private var mySignature: Option[Signature] | Null = null
    private var myParamRefss: List[Either[List[TermParamRef], List[TypeParamRef]]] | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myDeclaredType == null then failNotCompleted("declaredType was not initialized")

    private[tastyquery] final def withDeclaredType(tpe: Type): this.type =
      if myDeclaredType != null then throw new IllegalStateException(s"reassignment of declared type to $this")
      myDeclaredType = tpe
      this

    def declaredType(using Context): Type =
      val local = myDeclaredType
      if local != null then local
      else throw new IllegalStateException(s"$this was not assigned a declared type")

    /** Get the module class of this module value definition, if it exists:
      * - for `object val C` => `object class C[$]`
      */
    final def moduleClass(using Context): Option[ClassSymbol] =
      if is(Module) then declaredType.classSymbol
      else None

    final def staticRef(using Context): TermRef =
      require(isStatic, s"Cannot construct a staticRef for non-static symbol $this")
      TermRef(owner.staticOwnerPrefix, this)

    private[tastyquery] final def declaredTypeAsSeenFrom(prefix: Prefix)(using Context): Type =
      declaredType.asSeenFrom(prefix, owner)

    private def isConstructor: Boolean =
      owner.isClass && is(Method) && name == nme.Constructor

    private[tastyquery] final def needsSignature(using Context): Boolean =
      declaredType match
        case _: MethodType | _: PolyType => true
        case _                           => false
    end needsSignature

    private[tastyquery] final def signature(using Context): Option[Signature] =
      val local = mySignature
      if local != null then local
      else
        val sig = declaredType match
          case methodic: MethodicType =>
            Some(Signature.fromMethodic(methodic, Option.when(isConstructor)(owner.asClass)))
          case _ => None
        mySignature = sig
        sig

    /** If this symbol has a `MethodicType`, returns a `SignedName`, otherwise a `Name`. */
    final def signedName(using Context): Name =
      signature.fold(name) { sig =>
        val name = this.name.asSimpleName
        val targetName = name // TODO We may have to take `@targetName` into account here, one day
        SignedName(name, sig, targetName)
      }

    final def paramRefss(using Context): List[Either[List[TermParamRef], List[TypeParamRef]]] =
      def paramssOfType(tp: Type): List[Either[List[TermParamRef], List[TypeParamRef]]] = tp match
        case mt: PolyType   => Right(mt.paramRefs) :: paramssOfType(mt.resultType)
        case mt: MethodType => Left(mt.paramRefs) :: paramssOfType(mt.resultType)
        case _              => Nil
      val local = myParamRefss
      if local != null then local
      else
        val refs = paramssOfType(declaredType)
        myParamRefss = refs
        refs
  end TermSymbol

  object TermSymbol:
    private[tastyquery] def create(name: TermName, owner: Symbol): TermSymbol =
      owner.addDeclIfDeclaringSym(TermSymbol(name, owner))
  end TermSymbol

  sealed abstract class TypeSymbol protected (val name: TypeName, owner: Symbol) extends TermOrTypeSymbol(owner):
    type ThisNameType = TypeName
    type DefiningTreeType <: TypeDef | TypeTreeBind

    final def isTypeAlias(using Context): Boolean = this match
      case sym: TypeMemberSymbol => sym.typeDef.isInstanceOf[TypeMemberDefinition.TypeAlias]
      case _                     => false

    final def isOpaqueTypeAlias(using Context): Boolean = this match
      case sym: TypeMemberSymbol => sym.typeDef.isInstanceOf[TypeMemberDefinition.OpaqueTypeAlias]
      case _                     => false
  end TypeSymbol

  sealed abstract class TypeSymbolWithBounds protected (name: TypeName, owner: Symbol) extends TypeSymbol(name, owner):
    type DefiningTreeType <: TypeMember | TypeParam | TypeTreeBind

    def bounds(using Context): TypeBounds

    def lowerBound(using Context): Type

    def upperBound(using Context): Type
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

    final def bounds(using Context): TypeBounds =
      val local = myBounds
      if local == null then throw IllegalStateException(s"$this was not assigned type bounds")
      else local

    final def lowerBound(using Context): Type = bounds.low

    final def upperBound(using Context): Type = bounds.high
  end TypeParamSymbol

  final class ClassTypeParamSymbol private (name: TypeName, override val owner: ClassSymbol)
      extends TypeParamSymbol(name, owner)
      with TypeParamInfo:
    type DefiningTreeType = TypeParam

    private[tastyquery] def paramVariance(using Context): Variance =
      Variance.fromFlags(flags)

    final def typeRef(using Context): TypeRef = TypeRef(ThisType(owner.typeRef), this)
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

    final def typeDef(using Context): TypeMemberDefinition =
      val local = myDefinition
      if local == null then throw IllegalStateException("$this was not assigned a definition")
      else local

    final def aliasedType(using Context): Type =
      typeDef.asInstanceOf[TypeMemberDefinition.TypeAlias].alias

    private[tastyquery] def aliasedTypeAsSeenFrom(pre: Prefix)(using Context): Type =
      aliasedType.asSeenFrom(pre, owner)

    final def bounds(using Context): TypeBounds = typeDef match
      case TypeMemberDefinition.TypeAlias(alias)           => TypeAlias(alias)
      case TypeMemberDefinition.AbstractType(bounds)       => bounds
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, _) => bounds

    final def lowerBound(using Context): Type = typeDef match
      case TypeMemberDefinition.TypeAlias(alias)           => alias
      case TypeMemberDefinition.AbstractType(bounds)       => bounds.low
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, _) => bounds.low

    final def upperBound(using Context): Type = typeDef match
      case TypeMemberDefinition.TypeAlias(alias)           => alias
      case TypeMemberDefinition.AbstractType(bounds)       => bounds.high
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, _) => bounds.high
  end TypeMemberSymbol

  object TypeMemberSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): TypeMemberSymbol =
      owner.addDeclIfDeclaringSym(TypeMemberSymbol(name, owner))
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

    // Reference fields (checked in doCheckCompleted)
    private var myTypeParams: List[ClassTypeParamSymbol] | Null = null
    private var myParentsInit: (() => List[Type]) | Null = null
    private var myParents: List[Type] | Null = null

    // Optional reference fields
    private var mySpecialErasure: Option[() => ErasedTypeRef] = None

    // DeclaringSymbol-related fields
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[TermOrTypeSymbol]] =
      mutable.HashMap[Name, mutable.HashSet[TermOrTypeSymbol]]()

    // Cache fields
    private var myLinearization: List[ClassSymbol] | Null = null

    protected override def doCheckCompleted(): Unit =
      super.doCheckCompleted()
      if myTypeParams == null then failNotCompleted("typeParams not initialized")
      if myParents == null && myParentsInit == null then failNotCompleted("parents not initialized")

    private[tastyquery] def isValueClass(using Context): Boolean =
      parents.nonEmpty && parents.head.classSymbol.exists(_ == defn.AnyValClass)

    private[tastyquery] def isDerivedValueClass(using Context): Boolean =
      isValueClass && !defn.isPrimitiveValueClass(this)

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
      case scope: DeclaringSymbol if this.is(Module) => // `this` is a `ClassSymbol`
        scope.getDecl(this.name.sourceObjectName).collect { case sym: TermSymbol =>
          sym
        }
      case _ => None // not possible yet for local symbols

    private[tastyquery] final def withTypeParams(tparams: List[ClassTypeParamSymbol]): this.type =
      if myTypeParams != null then throw new IllegalStateException(s"reassignment of type parameters to $this")
      myTypeParams = tparams
      this

    final def typeParams(using Context): List[ClassTypeParamSymbol] =
      val local = myTypeParams
      if local == null then throw new IllegalStateException(s"type params not initialized for $this")
      else local

    private[tastyquery] final def withParentsDirect(parents: List[Type]): this.type =
      if myParentsInit != null || myParents != null then
        throw IllegalStateException(s"reassignment of parents of $this")
      myParents = parents
      this

    private[tastyquery] final def withParentsDelayed(parentsInit: () => List[Type]): this.type =
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

    final def isSubclass(that: ClassSymbol)(using Context): Boolean =
      linearization.contains(that)

    private[tastyquery] final def withSpecialErasure(specialErasure: () => ErasedTypeRef): this.type =
      if mySpecialErasure.isDefined then throw IllegalStateException(s"reassignment of the special erasure of $this")
      mySpecialErasure = Some(specialErasure)
      this

    private[tastyquery] final def specialErasure(using Context): Option[() => ErasedTypeRef] =
      mySpecialErasure

    // DeclaringSymbol implementation

    private[Symbols] final def addDecl(decl: TermOrTypeSymbol): Unit =
      val set = myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet)
      if decl.isType then assert(set.isEmpty, s"trying to add a second entry $decl for type name ${decl.name} in $this")
      set += decl

    private[Symbols] final def hasOverloads(name: SignedName): Boolean =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.sizeIs > 1
        case _           => false

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
            case decl: TermSymbol => decl.signature.exists(_ == overloaded.sig)
            case _                => false
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
      *   if the provided `name` is a [[SignedName]]
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
      *   if the provided `name` is a [[SignedName]]
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
      *   if the provided `name` is a [[SignedName]]
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
      *   if the provided `name` is a [[SignedName]]
      */
    final def findNonOverloadedDecl(name: TermName)(using Context): TermSymbol =
      getNonOverloadedDecl(name).getOrElse {
        throw MemberNotFoundException(this, name, s"Multiple overloads or no overload of '$name' in $this")
      }
    end findNonOverloadedDecl

    final def declarations(using Context): List[TermOrTypeSymbol] =
      myDeclarations.values.toList.flatten

    // Type-related things

    private[tastyquery] final def initParents: Boolean =
      myTypeParams != null

    /** Compute tp.baseType(this) */
    private[tastyquery] final def baseTypeOf(tp: Type)(using Context): Option[Type] =
      def recur(tp: Type): Option[Type] = tp match
        case tp: TypeRef =>
          def combineGlb(bt1: Option[Type], bt2: Option[Type]): Option[Type] =
            if bt1.isEmpty then bt2
            else if bt2.isEmpty then bt1
            else Some(bt1.get & bt2.get)

          def foldGlb(bt: Option[Type], ps: List[Type]): Option[Type] =
            ps.foldLeft(bt)((bt, p) => combineGlb(bt, recur(p)))

          tp.symbol match
            case tpSym: ClassSymbol =>
              def isOwnThis = tp.prefix match
                case prefix: ThisType   => prefix.cls == tpSym.owner
                case prefix: PackageRef => prefix.symbol == tpSym.owner
                case NoPrefix           => true
                case _                  => false

              if tpSym == this then Some(tp)
              else if isOwnThis then
                if tpSym.isSubclass(this) then
                  if this.isStatic && this.typeParams.isEmpty then Some(this.typeRef)
                  else foldGlb(None, tpSym.parents)
                else None
              else recur(tpSym.typeRef).map(_.asSeenFrom(tp.prefix, tpSym.owner.asDeclaringSymbol))
            case _: TypeSymbolWithBounds =>
              recur(tp.superType)
          end match

        case tp: AppliedType =>
          tp.tycon match
            case tycon: TypeRef if tycon.symbol == this =>
              Some(tp)
            case tycon =>
              // TODO Also handle TypeLambdas
              val typeParams = tycon.typeParams
              recur(tycon).map(_.substClassTypeParams(typeParams.asInstanceOf[List[ClassTypeParamSymbol]], tp.args))

        case tp: TypeProxy =>
          recur(tp.superType)

        case _ =>
          // TODO Handle AndType and OrType, and JavaArrayType
          None
      end recur

      recur(tp)
    end baseTypeOf

    private[tastyquery] final def findMember(pre: Type, name: Name)(using Context): Option[Symbol] =
      def lookup(lin: List[ClassSymbol]): Option[Symbol] = lin match
        case parentCls :: linRest =>
          parentCls.getDecl(name) match
            case Some(sym) if !sym.is(Private) =>
              Some(sym)
            case _ =>
              lookup(linRest)
        case Nil =>
          None
      end lookup

      getDecl(name).filter(!_.is(ParamAccessor)).orElse {
        if name == nme.Constructor then None
        else lookup(linearization.tail)
      }
    end findMember

    private var myTypeRef: TypeRef | Null = null

    private[tastyquery] final def typeRef(using Context): TypeRef =
      val local = myTypeRef
      if local != null then local
      else
        val pre = owner match
          case owner: PackageSymbol => owner.packageRef
          case owner: ClassSymbol   => owner.thisType
          case _                    => NoPrefix
        val typeRef = TypeRef(pre, this)
        myTypeRef = typeRef
        typeRef

    private var myThisType: ThisType | Null = null

    /** The `ThisType` for this class, as visible from inside this class. */
    private[tastyquery] final def thisType(using Context): ThisType =
      val local = myThisType
      if local != null then local
      else
        val computed = ThisType(typeRef)
        myThisType = computed
        computed
    end thisType
  }

  object ClassSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): ClassSymbol =
      owner.addDeclIfDeclaringSym(ClassSymbol(name, owner))

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol, span: Span)(using Context): ClassSymbol =
      // TODO Store the `span`
      createRefinedClassSymbol(owner)

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol)(using Context): ClassSymbol =
      val cls = ClassSymbol(tpnme.RefinedClassMagic, owner) // by-pass `owner.addDeclIfDeclaringSym`
      cls
        .withTypeParams(Nil)
        .withParentsDirect(defn.ObjectType :: Nil)
        .withFlags(EmptyFlagSet, None)
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
    val packageRef: PackageRef = PackageRef(this: @unchecked)

    this.withFlags(EmptyFlagSet, None)
    this.setAnnotations(Nil)

    private[tastyquery] def getPackageDeclOrCreate(name: SimpleName)(using Context): PackageSymbol =
      getPackageDecl(name).getOrElse {
        assert(name != nme.EmptyPackageName, s"Trying to create a subpackage $name of $this")
        val pkg = PackageSymbol(name, this)
        addDecl(pkg)
        pkg
      }
    end getPackageDeclOrCreate

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
    final def getPackageDecl(name: SimpleName)(using Context): Option[PackageSymbol] =
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
