package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

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
  *  +- NoSymbol                        singleton instance used when there is no symbol
  *  |
  *  +- PackageSymbol                   any package, including the root package, the empty package, and nested packages
  *  |
  *  +- TermSymbol                      any term definition:
  *  |                                  `val`, `var`, `def`, term param, term capture, `object` value
  *  |
  *  +- TypeSymbol                      any definition for a type
  *     +- ClassSymbol                  definition for a `class`, `trait`, or the module class of an `object`
  *     +- TypeSymbolWithBounds         any other kind of type: `type` definitions, type params, type captures
  *        +- TypeMemberSymbol          `type` definition, further refined through its `typeDef`
  *        +- TypeParamSymbol
  *           +- ClassTypeParamSymbol   type parameter of a class
  *           +- LocalTypeParamSymbol   any other type parameter
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
  * With the exception of `NoSymbol` and the root package symbol, all symbols
  * have an `owner` which is another `Symbol`.
  *
  * All symbols also have a `name`. It is a `TypeName` for `TypeSymbol`s, and a
  * `TermName` for `TermSymbol`s, `PackageSymbol`s and `NoSymbol`.
  */
object Symbols {

  sealed abstract class Symbol protected (val owner: Symbol | Null) {
    type ThisNameType <: Name

    val name: ThisNameType

    private var isFlagsInitialized = false
    private var myFlags: FlagSet = Flags.EmptyFlagSet
    private var myTree: Option[DefTree] = None
    private var myPrivateWithin: Option[Symbol] = None

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

    private[tastyquery] def withTree(t: DefTree): this.type =
      require(!isPackage, s"Multiple trees correspond to one package, a single tree cannot be assigned")
      myTree = Some(t)
      this

    final def tree(using Context): Option[DefTree] =
      myTree

    private[tastyquery] final def withFlags(flags: FlagSet): this.type =
      if isFlagsInitialized then throw IllegalStateException(s"reassignment of flags to $this")
      else
        isFlagsInitialized = true
        myFlags = flags
        this

    private[tastyquery] final def withPrivateWithin(privateWithin: Symbol): this.type =
      if myPrivateWithin.isDefined then throw new IllegalStateException(s"reassignment of privateWithin to $this")
      else
        myPrivateWithin = Some(privateWithin)
        this

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

    private[Symbols] final def addDeclIfDeclaringSym(decl: Symbol): decl.type =
      this match
        case declaring: DeclaringSymbol => declaring.addDecl(decl)
        case _                          => ()
      decl

    private[Symbols] def maybeOuter: Symbol = owner match {
      case owner: Symbol => owner
      case null          => NoSymbol
    }

    private[tastyquery] final def enclosingDecls: Iterator[DeclaringSymbol] =
      Iterator.iterate(enclosingDecl)(_.enclosingDecl).takeWhile(s => s.maybeOuter.exists)

    private[tastyquery] final def isStatic: Boolean =
      if owner == null then this != NoSymbol
      else owner.isStaticOwner

    @tailrec
    private def isStaticOwner: Boolean = this match
      case _: PackageSymbol => true
      case cls: ClassSymbol => cls.is(Module) && cls.owner.isStaticOwner
      case _                => false

    private def nameWithPrefix(addPrefix: Symbol => Boolean): FullyQualifiedName =
      if isRoot then FullyQualifiedName.rootPackageName
      else
        val pre = maybeOuter
        if addPrefix(pre) then pre.nameWithPrefix(addPrefix).mapLastOption(_.toTermName).select(name)
        else FullyQualifiedName(name :: Nil)

    final def fullName: FullyQualifiedName = nameWithPrefix(_.isStatic)
    private[tastyquery] final def erasedName: FullyQualifiedName = nameWithPrefix(_ => true)

    final def exists: Boolean = this ne NoSymbol

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

  object NoSymbol extends Symbol(null):
    type ThisNameType = SimpleName

    val name: SimpleName = nme.EmptySimpleName

    this.withFlags(EmptyFlagSet)

    override def toString: String = "NoSymbol"
  end NoSymbol

  final class TermSymbol private (val name: TermName, override val owner: Symbol) extends Symbol(owner):
    type ThisNameType = TermName

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

    private[tastyquery] final def declaredTypeAsSeenFrom(prefix: Type)(using Context): Type =
      declaredType.asSeenFrom(prefix, owner)

    private def isConstructor: Boolean =
      maybeOuter.isClass && is(Method) && name == nme.Constructor

    private[tastyquery] final def signature(using Context): Option[Signature] =
      val local = mySignature
      if local != null then local
      else
        val sig = declaredType match
          case methodic: MethodicType =>
            Some(Signature.fromMethodic(methodic, Option.when(isConstructor)(maybeOuter.asClass)))
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

  sealed abstract class TypeSymbol protected (val name: TypeName, override val owner: Symbol) extends Symbol(owner):
    type ThisNameType = TypeName

    final def isTypeAlias(using Context): Boolean = this match
      case sym: TypeMemberSymbol => sym.typeDef.isInstanceOf[TypeMemberDefinition.TypeAlias]
      case _                     => false

    final def isOpaqueTypeAlias(using Context): Boolean = this match
      case sym: TypeMemberSymbol => sym.typeDef.isInstanceOf[TypeMemberDefinition.OpaqueTypeAlias]
      case _                     => false
  end TypeSymbol

  sealed abstract class TypeSymbolWithBounds protected (name: TypeName, owner: Symbol) extends TypeSymbol(name, owner):
    def bounds(using Context): TypeBounds

    def lowerBound(using Context): Type

    def upperBound(using Context): Type
  end TypeSymbolWithBounds

  sealed abstract class TypeParamSymbol protected (name: TypeName, owner: Symbol)
      extends TypeSymbolWithBounds(name, owner):
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
    private[tastyquery] def paramVariance(using Context): Variance =
      Variance.fromFlags(flags)

    final def typeRef(using Context): TypeRef = TypeRef(ThisType(owner.typeRef), this)
  end ClassTypeParamSymbol

  object ClassTypeParamSymbol:
    private[tastyquery] def create(name: TypeName, owner: ClassSymbol): ClassTypeParamSymbol =
      ClassTypeParamSymbol(name, owner)
  end ClassTypeParamSymbol

  final class LocalTypeParamSymbol private (name: TypeName, owner: Symbol) extends TypeParamSymbol(name, owner)

  object LocalTypeParamSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): LocalTypeParamSymbol =
      LocalTypeParamSymbol(name, owner)
  end LocalTypeParamSymbol

  final class TypeMemberSymbol private (name: TypeName, owner: Symbol) extends TypeSymbolWithBounds(name, owner):
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

    private[tastyquery] def aliasedTypeAsSeenFrom(pre: Type)(using Context): Type =
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
    private[Symbols] def addDecl(decl: Symbol): Unit

    def getDecls(name: Name)(using Context): List[Symbol]

    def getDecl(name: Name)(using Context): Option[Symbol]

    /** Note: this will force all trees in a package */
    def declarations(using Context): List[Symbol]
  }

  final class ClassSymbol private (name: TypeName, owner: Symbol) extends TypeSymbol(name, owner) with DeclaringSymbol {
    // Reference fields (checked in doCheckCompleted)
    private var myTypeParams: List[ClassTypeParamSymbol] | Null = null
    private var myParentsInit: (() => List[Type]) | Null = null
    private var myParents: List[Type] | Null = null

    // Optional reference fields
    private var mySpecialErasure: Option[() => ErasedTypeRef] = None

    // DeclaringSymbol-related fields
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    // Cache fields
    private[tastyquery] val classInfo: ClassInfo = ClassInfo(this: @unchecked)
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
    final def companionClass(using Context): Option[ClassSymbol] = maybeOuter match
      case scope: PackageSymbol =>
        scope.getDecl(this.name.companionName).collect { case sym: ClassSymbol =>
          sym
        }
      case _ => None // not possible yet for local symbols

    /** Get the module value of this module class definition, if it exists:
      * - for `object class C[$]` => `object val C`
      */
    final def moduleValue(using Context): Option[TermSymbol] = maybeOuter match
      case scope: PackageSymbol if this.is(ModuleClass) =>
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
          myParentsInit = null
          val parents = localParentsInit()
          myParents = parents
          parents
        else throw IllegalStateException(s"$this was not assigned parents")
    end parents

    private def parentClasses(using Context): List[ClassSymbol] =
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

    private[Symbols] final def addDecl(decl: Symbol): Unit =
      val set = myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet)
      if decl.isType then assert(set.isEmpty, s"trying to add a second entry $decl for type name ${decl.name} in $this")
      set += decl

    private[Symbols] final def hasOverloads(name: SignedName): Boolean =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.sizeIs > 1
        case _           => false

    final def getDecls(name: Name)(using Context): List[Symbol] =
      name match
        case name: SignedName => getDecl(name).toList
        case _                => myDeclarations.get(name).fold(Nil)(_.toList)

    final def getDecl(name: Name)(using Context): Option[Symbol] =
      name match
        case overloaded: SignedName =>
          distinguishOverloaded(overloaded)
        case name =>
          myDeclarations.get(name) match
            case Some(decls) =>
              if decls.sizeIs == 1 then Some(decls.head)
              else if decls.sizeIs > 1 then
                throw MemberNotFoundException(this, name, s"unexpected overloads in $this: ${decls.mkString(", ")}")
              else None
            case _ => None
    end getDecl

    private final def distinguishOverloaded(overloaded: SignedName)(using Context): Option[Symbol] =
      myDeclarations.get(overloaded.underlying) match
        case Some(overloads) =>
          overloads.find {
            case decl: TermSymbol => decl.signature.exists(_ == overloaded.sig)
            case _                => false
          }
        case None => None
    end distinguishOverloaded

    final def declarations(using Context): List[Symbol] =
      myDeclarations.values.toList.flatten

    // Type-related things

    private[tastyquery] final def initParents: Boolean =
      myTypeParams != null

    /** Compute tp.baseType(this) */
    private[tastyquery] final def baseTypeOf(tp: Type)(using Context): Type =
      def recur(tp: Type): Type = tp match
        case tp: TypeRef =>
          def combineGlb(bt1: Type, bt2: Type): Type =
            if bt1 == NoType then bt2
            else if bt2 == NoType then bt1
            else bt1 & bt2

          def foldGlb(bt: Type, ps: List[Type]): Type =
            ps.foldLeft(bt)((bt, p) => combineGlb(bt, recur(p)))

          tp.symbol match
            case tpSym: ClassSymbol =>
              def isOwnThis = tp.prefix match
                case prefix: ThisType   => prefix.cls == tpSym.owner
                case prefix: PackageRef => prefix.symbol == tpSym.owner
                case NoPrefix           => true
                case _                  => false

              if tpSym == this then tp
              else if isOwnThis then
                if tpSym.isSubclass(this) then
                  if this.isStatic && this.typeParams.isEmpty then this.typeRef
                  else foldGlb(NoType, tpSym.parents)
                else NoType
              else recur(tpSym.typeRef).asSeenFrom(tp.prefix, tpSym.owner)
            case _: TypeSymbolWithBounds =>
              recur(tp.superType)
          end match

        case tp: AppliedType =>
          if tp.tycon.typeSymbol == this then tp
          else
            // TODO Also handle TypeLambdas
            val typeParams = tp.tycon.typeParams
            recur(tp.tycon).substClassTypeParams(typeParams.asInstanceOf[List[ClassTypeParamSymbol]], tp.args)

        case tp: TypeProxy =>
          recur(tp.superType)

        case _ =>
          // TODO Handle AndType and OrType, and JavaArrayType
          NoType
      end recur

      recur(tp)
    end baseTypeOf

    private[tastyquery] final def findMember(pre: Type, name: Name)(using Context): Option[Symbol] =
      def lookup(parents: List[Type]): Option[Symbol] = parents match
        case p :: ps =>
          p.classSymbol.flatMap { parentCls =>
            // val inherited = parentd.membersNamedNoShadowingBasedOnFlags(name, required, excluded | Private)
            // denots1.union(inherited.mapInherited(ownDenots, denots1, thisType))
            parentCls.findMember(pre, name) // lookup in parents of parent
          }.orElse(lookup(ps))
        case nil => None
      end lookup

      getDecl(name).orElse {
        if name == nme.Constructor then None
        else lookup(parents)
      }
    end findMember

    /** Get the self type of this class, as if viewed from an external package */
    private[tastyquery] final def accessibleThisType: Type =
      maybeOuter match
        case pre: PackageSymbol => TypeRef(pre.packageRef, this)
        case pre: ClassSymbol   => TypeRef(pre.accessibleThisType, this)
        case _                  => TypeRef(NoPrefix, this)

    private var myTypeRef: TypeRef | Null = null

    private[tastyquery] final def typeRef(using Context): TypeRef =
      val local = myTypeRef
      if local != null then local
      else
        val pre = owner match
          case owner: PackageSymbol => owner.packageRef
          case owner: ClassSymbol   => owner.accessibleThisType
          case _                    => NoPrefix
        val typeRef = TypeRef(pre, this)
        myTypeRef = typeRef
        typeRef
  }

  object ClassSymbol:
    private[tastyquery] def create(name: TypeName, owner: Symbol): ClassSymbol =
      owner.addDeclIfDeclaringSym(ClassSymbol(name, owner))

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol, span: Span)(using Context): ClassSymbol =
      val cls = create(tpnme.RefinedClassMagic, owner)
      cls
        .withTypeParams(Nil)
        .withParentsDirect(defn.ObjectType :: Nil)
        .withFlags(EmptyFlagSet)
      cls.checkCompleted()
      cls
  end ClassSymbol

  final class PackageSymbol private (val name: SimpleName, override val owner: PackageSymbol | Null)
      extends Symbol(owner)
      with DeclaringSymbol {
    type ThisNameType = SimpleName

    // DeclaringSymbol-related fields
    private var rootsInitialized: Boolean = false
    private val myDeclarations = mutable.HashMap[Name, Symbol]()

    // Cache fields
    val packageRef: PackageRef = PackageRef(this: @unchecked)

    this.withFlags(EmptyFlagSet)

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
