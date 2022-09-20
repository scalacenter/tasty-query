package tastyquery.ast

import scala.collection.mutable

import dotty.tools.tasty.TastyFormat.NameTags

import tastyquery.ast.Names.*
import tastyquery.ast.Trees.{DefTree, Tree, DefDef}
import tastyquery.ast.Flags.*
import tastyquery.ast.Spans.*
import tastyquery.ast.Types.*
import tastyquery.ast.Variances.*
import tastyquery.Contexts
import tastyquery.Contexts.{Context, ctx}

import tastyquery.util.syntax.chaining.given

import compiletime.codeOf
import tastyquery.reader.classfiles.Classpaths.Loader

object Symbols {

  class ExistingDefinitionException(val scope: Symbol, val name: Name, explanation: String = "")
      extends Exception(
        SymbolLookupException.addExplanation(s"$scope has already defined ${name.toDebugString}", explanation)
      )

  class SymbolLookupException(val name: Name, explanation: String = "")
      extends SymResolutionProblem(
        SymbolLookupException.addExplanation(s"Could not find symbol for name ${name.toDebugString}", explanation)
      )

  object SymbolLookupException {
    def unapply(e: SymbolLookupException): Option[Name] = Some(e.name)

    def addExplanation(msg: String, explanation: String): String =
      if (explanation.isEmpty) msg else s"$msg: $explanation"
  }

  val NoSymbol = new RegularSymbol(nme.EmptyTermName, null)

  sealed abstract class Symbol private[Symbols] (val name: Name, rawowner: Symbol | Null) extends ParamInfo {
    private var isFlagsInitialized = false
    private var myFlags: FlagSet = Flags.EmptyFlagSet
    private var myTree: Option[DefTree] = None
    private var myPrivateWithin: Option[Symbol] = None

    /** Forces the symbol to be initialized.
      *
      * This method should never be called from within the initialisation of
      * this symbol.
      *
      * For symbols that are not root symbols, this has no effect.
      */
    private[tastyquery] def ensureInitialised()(using Context): Unit

    def withTree(t: DefTree): this.type =
      require(!isPackage, s"Multiple trees correspond to one package, a single tree cannot be assigned")
      myTree = Some(t)
      this

    final def tree(using Context): Option[DefTree] =
      ensureInitialised()
      myTree

    /** Get the companion class for a definition, if it exists:
      * - for `class C` => `object class C[$]`
      * - for `object class C[$]` => `class C`
      * - for `object val C` => `class C`
      */
    final def companionClass(using Context): Option[ClassSymbol] = maybeOuter match
      case scope: PackageClassSymbol =>
        this match
          case _: PackageClassSymbol => None
          case cls: ClassSymbol =>
            scope.getDecl(cls.name.toTypeName.companionName).collect { case sym: ClassSymbol =>
              sym
            }
          case obj: RegularSymbol if obj.isTerm =>
            scope.getDecl(obj.name.toTypeName).collect { case sym: ClassSymbol =>
              sym
            }
          case _ => None
      case _ => None // not possible yet for local symbols

    private var myDeclaredType: Type | Null = null

    /** Hook called by a SymbolFactory for debugging purposes
      *  Example usage: throw an exception when some specific symbol is created.
      */
    private[Symbols] def postCreate(using Context): Unit = ()

    private[tastyquery] final def withDeclaredType(tpe: Type): this.type =
      val local = myDeclaredType
      if local != null then throw new IllegalStateException(s"reassignment of declared type to $this")
      else
        myDeclaredType = tpe
        this

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

    private[tastyquery] def signature(using Context): Option[Signature]

    /** If this symbol has a `MethodicType`, returns a `SignedName`, otherwise a `Name`. */
    final def signedName(using Context): Name =
      signature.fold(name) { sig =>
        val name = this.name.asSimpleName
        val targetName = name // TODO We may have to take `@targetName` into account here, one day
        SignedName(name, sig, targetName)
      }

    final def flags: FlagSet =
      if isFlagsInitialized then myFlags
      else throw IllegalStateException(s"flags of $this have not been initialized")

    final def is(flag: Flag): Boolean =
      flags.is(flag)

    final def isAllOf(testFlags: FlagSet): Boolean =
      flags.isAllOf(testFlags)

    final def isAnyOf(testFlags: FlagSet): Boolean =
      flags.isAnyOf(testFlags)

    def paramVariance(using Context): Variance =
      Variance.fromFlags(flags)

    def declaredType(using Context): Type =
      val local = myDeclaredType
      if local != null then local
      else throw new IllegalStateException(s"$this was not assigned a declared type")

    final def owner: Symbol = outer

    final def outer: Symbol = rawowner match {
      case owner: Symbol => owner
      case null          => assert(false, s"cannot access outer, ${this.name} was not declared within any scope")
    }

    final def enclosingDecl: DeclaringSymbol = rawowner match {
      case owner: DeclaringSymbol => owner
      case _: Symbol | null =>
        assert(false, s"cannot access owner, ${this.name} is local or not declared within any scope")
    }

    private[Symbols] def maybeOuter: Symbol = rawowner match {
      case owner: Symbol => owner
      case null          => NoSymbol
    }

    /** The type parameters of a class symbol, Nil for all other symbols. */
    def typeParams(using Context): List[Symbol] = Nil

    final def paramSymss(using Context): List[List[Symbol]] =
      tree match
        case Some(ddef: DefDef) =>
          ddef.paramLists.map {
            case Left(params)   => params.map(_.symbol)
            case Right(tparams) => tparams.map(_.symbol)
          }
        // TODO: java and scala 2 methods do not have trees
        case _ => Nil

    private[tastyquery] final def enclosingDecls: Iterator[DeclaringSymbol] =
      Iterator.iterate(enclosingDecl)(_.enclosingDecl).takeWhile(s => s.maybeOuter.exists)

    private[tastyquery] final def isStatic: Boolean =
      Iterator
        .iterate(this)(_.outer)
        .takeWhile(s => s.maybeOuter.exists)
        .forall(s => s.isPackage || s.isClass && s.name.toTypeName.wrapsObjectName)

    private def nameWithPrefix(addPrefix: Symbol => Boolean): FullyQualifiedName =
      if isRoot then FullyQualifiedName.rootPackageName
      else
        val pre = maybeOuter
        if addPrefix(pre) then pre.nameWithPrefix(addPrefix).mapLastOption(_.toTermName).select(name)
        else FullyQualifiedName(name :: Nil)

    final def fullName: FullyQualifiedName = nameWithPrefix(_.isStatic)
    private[tastyquery] final def erasedName: FullyQualifiedName = nameWithPrefix(_ => true)

    final def exists: Boolean = this ne NoSymbol

    final def isType: Boolean = name.isTypeName
    final def isTerm: Boolean = name.isTermName

    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageClassSymbol]
    final def isRoot: Boolean = isPackage && rawowner == null

    final def asClass: ClassSymbol = this.asInstanceOf[ClassSymbol]

    private[tastyquery] final def memberIsOverloaded(name: SignedName): Boolean = this match
      case scope: DeclaringSymbol => scope.hasOverloads(name)
      case _                      => false

    private[tastyquery] final def memberOverloads(name: SignedName): List[Symbol] = this match
      case scope: DeclaringSymbol => scope.allOverloads(name)
      case _                      => Nil

    /** Is this symbol a user-defined opaque type alias? */
    final def isOpaqueTypeAlias(using Context): Boolean = is(Opaque) && !isClass

    override def toString: String = {
      val kind = this match
        case _: PackageClassSymbol => "package "
        case _: ClassSymbol        => if name.toTypeName.wrapsObjectName then "object class " else "class "
        case _                     => if exists && outer.isPackage then "object " else "" // TODO: base this on flags
      s"symbol[$kind$name]"
    }
    def toDebugString = toString
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  final class RegularSymbol private[Symbols] (override val name: Name, rawowner: Symbol | Null)
      extends Symbol(name, rawowner) {
    private var mySignature: Option[Signature] | Null = null

    private[tastyquery] override final def ensureInitialised()(using Context): Unit =
      if owner.isPackage then // Top-level module value
        companionClass.foreach(_.ensureInitialised()) // init the root class
      else () // member symbol, should be initialised by owner

    private[tastyquery] override final def signature(using Context): Option[Signature] =
      val local = mySignature
      if local != null then local
      else
        val sig = declaredType match
          case methodic: MethodicType => Some(Signature.fromMethodic(methodic))
          case _                      => None
        mySignature = sig
        sig
  }

  sealed abstract class DeclaringSymbol private[Symbols] (override val name: Name, rawowner: Symbol | Null)
      extends Symbol(name, rawowner) {

    private[tastyquery] override final def signature(using Context): Option[Signature] = None

    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    private[tastyquery] final def addDecl(decl: Symbol): Unit =
      myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet) += decl

    /** direct lookup without requiring `Context`, can not resolve overloads */
    private[tastyquery] final def getDeclInternal(name: Name): Option[Symbol] = name match
      case overloaded: SignedName => None // need context to resolve overloads
      case name =>
        myDeclarations.get(name) match
          case Some(decls) =>
            if decls.sizeIs == 1 then Some(decls.head)
            else if decls.sizeIs > 1 then
              throw SymbolLookupException(name, s"unexpected overloads: ${decls.mkString(", ")}")
            else None // TODO: this should be an error
          case _ => None

    private[tastyquery] final def getModuleDeclInternal(name: Name): Option[Symbol] =
      myDeclarations.get(name) match
        case Some(decls) => decls.find(_.is(Module))
        case None        => None

    private[Symbols] final def hasOverloads(name: SignedName): Boolean =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.sizeIs > 1
        case _           => false

    private[Symbols] final def allOverloads(name: SignedName): List[Symbol] =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.toList
        case _           => Nil

    final def getDecls(name: Name)(using Context): List[Symbol] =
      this match
        case pkg: PackageClassSymbol => getDecl(name).toList
        case _ =>
          ensureInitialised()
          name match
            case name: SignedName => getDecl(name).toList
            case _                => myDeclarations.get(name).fold(Nil)(_.toList)

    final def getDecl(name: Name)(using Context): Option[Symbol] =
      ensureInitialised()
      name match
        case overloaded: SignedName =>
          distinguishOverloaded(overloaded)
        case name =>
          getDeclInternal(name) match
            case None =>
              this match
                case pkg: PackageClassSymbol => pkg.initialiseRootFor(name)
                case _                       => None
            case res => res

    private final def distinguishOverloaded(overloaded: SignedName)(using Context): Option[Symbol] =
      myDeclarations.get(overloaded.underlying) match
        case Some(overloads) =>
          if overloads.sizeIs == 1 then Some(overloads.head) // TODO: verify signature matches?
          else if overloads.sizeIs > 1 then overloads.find(s => s.signature.exists(_ == overloaded.sig))
          else None // TODO: this should be an error
        case None => None

    final def resolveOverloaded(name: SignedName)(using Context): Option[Symbol] =
      getDecl(name)

    /** Note: this will force all trees in a package */
    final def declarations(using Context): List[Symbol] =
      ensureInitialised()
      this match
        case pkg: PackageClassSymbol => pkg.initialiseAllRoots()
        case _                       => ()
      declarationsInternal

    private[tastyquery] final def declarationsInternal: List[Symbol] =
      myDeclarations.values.toList.flatten

    override def declaredType(using Context): Type =
      ensureInitialised()
      super.declaredType

    final override def toDebugString: String =
      s"${super.toString} with declarations [${myDeclarations.keys.map(_.toDebugString).mkString(", ")}]"
  }

  class ClassSymbol private[Symbols] (override val name: Name, rawowner: Symbol | Null)
      extends DeclaringSymbol(name, rawowner) {
    private[tastyquery] var initialised: Boolean = false

    // TODO: how do we associate some Symbols with TypeBounds, and some with Type?
    private var myTypeParams: List[(Symbol, TypeBounds)] | Null = null

    /** Get the companion object of class definition, if it exists:
      * - for `class C` => `object val C`
      * - for `object class C[$]` => `object val C`
      */
    final def companionObject(using Context): Option[RegularSymbol] = maybeOuter match
      case scope: PackageClassSymbol =>
        this match
          case _: PackageClassSymbol => None
          case cls: ClassSymbol =>
            scope.getDecl(cls.name.toTypeName.sourceObjectName).collect { case sym: RegularSymbol =>
              sym
            }
      case _ => None // not possible yet for local symbols

    private[tastyquery] final def withTypeParams(tparams: List[Symbol], bounds: List[TypeBounds]): this.type =
      val local = myTypeParams
      if local != null then throw new IllegalStateException(s"reassignment of type parameters to $this")
      else
        myTypeParams = tparams.zip(bounds)
        this

    private def typeParamsInternal(using Context): List[(Symbol, TypeBounds)] =
      ensureInitialised()
      typeParamsInternalNoInitialize

    private def typeParamsInternalNoInitialize(using Context): List[(Symbol, TypeBounds)] =
      val local = myTypeParams
      if local == null then throw new IllegalStateException(s"expected type params for $this")
      else local

    private[tastyquery] final def typeParamSymsNoInitialize(using Context): List[Symbol] =
      typeParamsInternalNoInitialize.map(_(0))

    private[tastyquery] override final def ensureInitialised()(using Context): Unit =
      def initialiseMembers(): Unit = this match
        case pkg: PackageClassSymbol =>
          ctx.classloader.scanPackage(pkg)
          assert(initialised, s"could not initialize package $fullName")
        case cls =>
          assert(false, s"class ${cls.fullName} was never initialised")

      if !initialised then
        // TODO: maybe add flag and check against if we are currently initialising this symbol?
        initialiseMembers()

    private[tastyquery] final def initParents: Boolean =
      myTypeParams != null

    final def derivesFrom(base: Symbol)(using Context): Boolean =
      base.isClass &&
        ((this eq base)
        //|| (baseClassSet contains base)
        )

    /** Compute tp.baseType(this) */
    final def baseTypeOf(tp: Type)(using Context): Type =
      // TODO
      tp.widen

    // private[tastyquery] final def hasTypeParams: List[Symbol] = typeParamsInternal.map(_(0))
    private[tastyquery] final def typeParamSyms(using Context): List[Symbol] =
      typeParamsInternal.map(_(0))

    override def typeParams(using Context): List[Symbol] =
      typeParamSyms

    /** Get the self type of this class, as if viewed from an external package */
    private[tastyquery] final def accessibleThisType: Type = this match
      case pkg: PackageClassSymbol => PackageRef(pkg) // TODO: maybe we need this-type of package for package-private
      case cls =>
        maybeOuter match
          case pre: ClassSymbol => TypeRef(pre.accessibleThisType, cls)
          case _                => TypeRef(NoPrefix, cls)

    private var myTypeRef: TypeRef | Null = null

    private[tastyquery] final def typeRef(using Context): TypeRef =
      val local = myTypeRef
      if local != null then local
      else
        val pre = owner match
          case owner: ClassSymbol => owner.accessibleThisType
          case _                  => NoPrefix
        val typeRef = TypeRef(pre, this)
        myTypeRef = typeRef
        typeRef
  }

  // TODO: typename or term name?
  class PackageClassSymbol private[Symbols] (override val name: Name, rawowner: PackageClassSymbol | Null)
      extends ClassSymbol(name, rawowner) {
    if (rawowner != null) {
      // A package symbol is always a declaration in its owner package
      rawowner.addDecl(this)
    } else {
      // Root package is the only symbol that is allowed to not have an owner
      assert(name == nme.RootName)
    }

    this.withDeclaredType(PackageRef(this))

    private[tastyquery] def possibleRoot(rootName: SimpleName)(using Context): Option[Loader.Root] =
      ensureInitialised()
      ctx.classloader.findRoot(this, rootName)

    /** When no symbol exists, try to enter root symbols for the given Name, will shortcut if no root
      * exists for the given name.
      */
    private[tastyquery] def initialiseRootFor(name: Name)(using Context): Option[Symbol] =
      ctx.classloader.enterRoots(this, name)

    private[tastyquery] def initialiseAllRoots()(using Context): Unit =
      ctx.classloader.forceRoots(this)

    final def getPackageDecl(name: SimpleName)(using Context): Option[PackageClassSymbol] =
      // wrapper that ensures the Context is available, just in case we need it
      // to be side-effecting in the future.
      getPackageDeclInternal(name)

    private[tastyquery] def getPackageDeclInternal(packageName: SimpleName): Option[PackageClassSymbol] =
      /* All subpackages are created eagerly when initializing contexts,
       * so we can use getDeclInternal here.
       */
      getDeclInternal(packageName).collect { case pkg: PackageClassSymbol =>
        pkg
      }
  }

  sealed abstract class SymbolFactory[T <: Symbol] {
    type OwnerSym <: Symbol

    final def createSymbol(name: Name, owner: OwnerSym)(using Context): T =
      factory(name, owner).useWith(_.postCreate)

    protected def factory(name: Name, owner: OwnerSym): T

    def castSymbol(symbol: Symbol): T
  }

  /** A factory for symbols without open scopes, i.e. not a package */
  sealed abstract class ClosedSymbolFactory[T <: Symbol] extends SymbolFactory[T]:
    final type OwnerSym = Symbol

  object RegularSymbolFactory extends ClosedSymbolFactory[RegularSymbol] {
    override protected def factory(name: Name, owner: OwnerSym): RegularSymbol =
      RegularSymbol(name, owner)

    override def castSymbol(symbol: Symbol): RegularSymbol = symbol.asInstanceOf[RegularSymbol]
  }

  object ClassSymbolFactory extends ClosedSymbolFactory[ClassSymbol] {
    override protected def factory(name: Name, owner: OwnerSym): ClassSymbol =
      ClassSymbol(name, owner)

    override def castSymbol(symbol: Symbol): ClassSymbol = symbol.asInstanceOf[ClassSymbol]

    def createRefinedClassSymbol(owner: OwnerSym, span: Span)(using Context): ClassSymbol =
      val cls = createSymbol(tpnme.RefinedClassMagic, owner)
      cls
        .withDeclaredType(ClassType(cls, ObjectType))
        .withFlags(EmptyFlagSet)
      cls.initialised = true
      cls
  }

  object PackageClassSymbolFactory extends SymbolFactory[PackageClassSymbol] {
    type OwnerSym = PackageClassSymbol // can only be created when the owner is a PackageClassSymbol
    override protected def factory(name: Name, owner: OwnerSym): PackageClassSymbol =
      if owner.getPackageDeclInternal(name.asSimpleName).isDefined then
        throw IllegalStateException(s"Trying to recreate package $name in $owner")
      PackageClassSymbol(name, owner)

    def createRoots: (PackageClassSymbol, PackageClassSymbol) =
      val root = PackageClassSymbol(nme.RootName, null)
      val empty = PackageClassSymbol(nme.EmptyPackageName, root)
      root.initialised = true // should not be any class files for the root package
      (root, empty)

    override def castSymbol(symbol: Symbol): PackageClassSymbol = symbol.asInstanceOf[PackageClassSymbol]
  }
}
