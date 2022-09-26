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
import tastyquery.Contexts.{Context, ctx, defn}

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

  val NoSymbol = RegularSymbol.createNoSymbol()

  sealed abstract class Symbol private[Symbols] (val name: Name, rawowner: Symbol | Null) extends ParamInfo {
    private var isFlagsInitialized = false
    private var myFlags: FlagSet = Flags.EmptyFlagSet
    private var myTree: Option[DefTree] = None
    private var myPrivateWithin: Option[Symbol] = None

    def withTree(t: DefTree): this.type =
      require(!isPackage, s"Multiple trees correspond to one package, a single tree cannot be assigned")
      myTree = Some(t)
      this

    final def tree(using Context): Option[DefTree] =
      myTree

    /** Get the companion class for a definition, if it exists:
      * - for `class C` => `object class C[$]`
      * - for `object class C[$]` => `class C`
      * - for `object val C` => `class C`
      */
    final def companionClass(using Context): Option[ClassSymbol] = maybeOuter match
      case scope: PackageSymbol =>
        this match
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

    def ref(using Context): Type = this match
      case pkg: PackageSymbol => pkg.packageRef
      case cls: ClassSymbol   => cls.typeRef
      case sym: RegularSymbol => // TODO: should we cache in RegularSymbol?
        val pre = sym.maybeOuter match
          case pre: ClassSymbol => pre.ref
          case _                => NoPrefix
        NamedType(pre, sym)

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
    final def isTerm: Boolean = name.isTermName && !isPackage

    final def isDeclaringSymbol: Boolean = this.isInstanceOf[DeclaringSymbol]
    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageSymbol]
    final def isRoot: Boolean = isPackage && rawowner == null

    final def asDeclaringSymbol: DeclaringSymbol = this.asInstanceOf[DeclaringSymbol]
    final def asClass: ClassSymbol = this.asInstanceOf[ClassSymbol]
    final def asPackage: PackageSymbol = this.asInstanceOf[PackageSymbol]

    private[tastyquery] final def memberIsOverloaded(name: SignedName): Boolean = this match
      case scope: DeclaringSymbol => scope.hasOverloads(name)
      case _                      => false

    private[tastyquery] final def memberPossiblyOverloaded(name: SignedName): Boolean = this match
      case scope: DeclaringSymbol => scope.hasPossibleOverloads(name)
      case _                      => false

    private[tastyquery] final def memberOverloads(name: SignedName): List[Symbol] = this match
      case scope: DeclaringSymbol => scope.allOverloads(name)
      case _                      => Nil

    /** Is this symbol a user-defined opaque type alias? */
    final def isOpaqueTypeAlias(using Context): Boolean = is(Opaque) && !isClass

    override def toString: String = {
      val kind = this match
        case _: PackageSymbol => "package "
        case _: ClassSymbol   => if name.toTypeName.wrapsObjectName then "object class " else "class "
        case _                => if isFlagsInitialized && is(Module) then "object " else ""
      s"symbol[$kind$name]"
    }
    def toDebugString = toString
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  final class RegularSymbol private (override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner) {
    private var mySignature: Option[Signature] | Null = null

    private def isConstructor: Boolean =
      maybeOuter.isClass && is(Method) && name == nme.Constructor

    private[tastyquery] override final def signature(using Context): Option[Signature] =
      val local = mySignature
      if local != null then local
      else
        val sig = declaredType match
          case methodic: MethodicType =>
            Some(Signature.fromMethodic(methodic, Option.when(isConstructor)(maybeOuter.asClass)))
          case _ => None
        mySignature = sig
        sig
  }

  object RegularSymbol:
    private[tastyquery] def create(name: Name, owner: Symbol): RegularSymbol =
      RegularSymbol(name, owner)

    private[Symbols] def createNoSymbol(): RegularSymbol =
      RegularSymbol(nme.EmptyTermName, null)
  end RegularSymbol

  sealed trait DeclaringSymbol extends Symbol {
    private[tastyquery] override final def signature(using Context): Option[Signature] = None

    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    /** Ensures that the declarations of this symbol are initialized. */
    protected[this] def ensureDeclsInitialized()(using Context): Unit

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

    private[Symbols] final def hasPossibleOverloads(name: SignedName): Boolean =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.sizeIs >= 1
        case _           => false

    private[Symbols] final def allOverloads(name: SignedName): List[Symbol] =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.toList
        case _           => Nil

    final def getDecls(name: Name)(using Context): List[Symbol] =
      this match
        case pkg: PackageSymbol => getDecl(name).toList
        case _ =>
          ensureDeclsInitialized()
          name match
            case name: SignedName => getDecl(name).toList
            case _                => myDeclarations.get(name).fold(Nil)(_.toList)

    final def getDecl(name: Name)(using Context): Option[Symbol] =
      ensureDeclsInitialized()
      name match
        case overloaded: SignedName =>
          distinguishOverloaded(overloaded)
        case name =>
          getDeclInternal(name) match
            case None =>
              this match
                case pkg: PackageSymbol => pkg.initialiseRootFor(name)
                case _                  => None
            case res => res

    private final def distinguishOverloaded(overloaded: SignedName)(using Context): Option[Symbol] =
      myDeclarations.get(overloaded.underlying) match
        case Some(overloads) => overloads.find(_.signature.exists(_ == overloaded.sig))
        case None            => None

    final def resolveOverloaded(name: SignedName)(using Context): Option[Symbol] =
      getDecl(name)

    /** Note: this will force all trees in a package */
    final def declarations(using Context): List[Symbol] =
      ensureDeclsInitialized()
      this match
        case pkg: PackageSymbol => pkg.initialiseAllRoots()
        case _                  => ()
      declarationsInternal

    private[tastyquery] final def declarationsInternal: List[Symbol] =
      myDeclarations.values.toList.flatten

    final override def toDebugString: String =
      s"${super.toString} with declarations [${myDeclarations.keys.map(_.toDebugString).mkString(", ")}]"
  }

  final class ClassSymbol protected (override val name: Name, rawowner: Symbol | Null)
      extends Symbol(name, rawowner)
      with DeclaringSymbol {
    // TODO: how do we associate some Symbols with TypeBounds, and some with Type?
    private var myTypeParams: List[(Symbol, TypeBounds)] | Null = null

    private[tastyquery] def isDerivedValueClass(using Context): Boolean =
      def isValueClass: Boolean =
        tree.isDefined && // TODO: Remove when Scala 2 classes have a ClassInfo
          declaredType.asInstanceOf[ClassInfo].rawParents.head.classSymbol.exists(_ == defn.AnyValClass)
      isValueClass && !defn.isPrimitiveValueClass(this)

    /** Get the companion object of class definition, if it exists:
      * - for `class C` => `object val C`
      * - for `object class C[$]` => `object val C`
      */
    final def companionObject(using Context): Option[RegularSymbol] = maybeOuter match
      case scope: PackageSymbol =>
        scope.getDecl(this.name.toTypeName.sourceObjectName).collect { case sym: RegularSymbol =>
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
      val local = myTypeParams
      if local == null then throw new IllegalStateException(s"expected type params for $this")
      else local

    private[tastyquery] final def typeParamSymsNoInitialize(using Context): List[Symbol] =
      typeParamsInternal.map(_(0))

    protected[this] final def ensureDeclsInitialized()(using Context): Unit =
      // ClassSymbols are always initialized when created
      ()

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
        else lookup(declaredType.asInstanceOf[ClassInfo].rawParents)
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
      ClassSymbol(name, owner)

    private[tastyquery] def createRefinedClassSymbol(owner: Symbol, span: Span)(using Context): ClassSymbol =
      val cls = create(tpnme.RefinedClassMagic, owner)
      cls
        .withDeclaredType(ClassInfo.direct(cls, ObjectType :: Nil))
        .withFlags(EmptyFlagSet)
      cls
  end ClassSymbol

  final class PackageSymbol private (override val name: Name, rawowner: PackageSymbol | Null)
      extends Symbol(name, rawowner)
      with DeclaringSymbol {

    val packageRef: PackageRef = PackageRef(this: @unchecked)
    (this: @unchecked).withDeclaredType(packageRef)

    private var rootsInitialized: Boolean = false

    protected[this] final def ensureDeclsInitialized()(using Context): Unit =
      if !rootsInitialized then
        ctx.classloader.scanPackage(this)
        rootsInitialized = true

    private[tastyquery] def possibleRoot(rootName: SimpleName)(using Context): Option[Loader.Root] =
      ensureDeclsInitialized()
      ctx.classloader.findRoot(this, rootName)

    /** When no symbol exists, try to enter root symbols for the given Name, will shortcut if no root
      * exists for the given name.
      */
    private[tastyquery] def initialiseRootFor(name: Name)(using Context): Option[Symbol] =
      ctx.classloader.enterRoots(this, name)

    private[tastyquery] def initialiseAllRoots()(using Context): Unit =
      ctx.classloader.forceRoots(this)

    final def getPackageDecl(name: SimpleName)(using Context): Option[PackageSymbol] =
      // wrapper that ensures the Context is available, just in case we need it
      // to be side-effecting in the future.
      getPackageDeclInternal(name)

    private[tastyquery] def getPackageDeclInternal(packageName: SimpleName): Option[PackageSymbol] =
      /* All subpackages are created eagerly when initializing contexts,
       * so we can use getDeclInternal here.
       */
      getDeclInternal(packageName).collect { case pkg: PackageSymbol =>
        pkg
      }
  }

  object PackageSymbol:
    private[tastyquery] def create(name: SimpleName, owner: PackageSymbol): PackageSymbol =
      if owner.getPackageDeclInternal(name).isDefined then
        throw IllegalStateException(s"Trying to recreate package $name in $owner")
      val pkg = PackageSymbol(name, owner)
      owner.addDecl(pkg)
      pkg

    private[tastyquery] def createRoots(): (PackageSymbol, PackageSymbol) =
      val root = PackageSymbol(nme.RootName, null)
      root.rootsInitialized = true
      val empty = PackageSymbol(nme.EmptyPackageName, root)
      root.addDecl(empty)
      (root, empty)
  end PackageSymbol
}
