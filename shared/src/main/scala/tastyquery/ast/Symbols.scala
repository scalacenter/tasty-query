package tastyquery.ast

import scala.collection.mutable
import tastyquery.ast.Names.{Name, TermName, SignedName, SimpleName, QualifiedName, TypeName, SuffixedName, nme}
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Trees.{DefTree, Tree, DefDef}
import tastyquery.ast.Flags, Flags.FlagSet
import tastyquery.ast.Types.*
import tastyquery.Contexts.{BaseContext, baseCtx}

import compiletime.codeOf

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

  abstract class Symbol private[Symbols] (val name: Name, rawowner: Symbol | Null) {
    private var isFlagsInitialized = false
    private var myFlags: FlagSet = Flags.EmptyFlagSet
    private var myTree: Option[DefTree] = None
    // overridden in package symbol
    def withTree(t: DefTree): this.type = {
      myTree = Some(t)
      this
    }
    final def tree: Option[DefTree] = myTree

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

    private[tastyquery] def signature(using BaseContext): Option[Signature]

    final def flags: FlagSet =
      if isFlagsInitialized then myFlags
      else throw IllegalStateException(s"flags of $this have not been initialized")

    def declaredType(using BaseContext): Type =
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

    final def paramSymss: List[List[Symbol]] =
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

    private def nameWithPrefix(addPrefix: Symbol => Boolean): Name =
      if isPackage then name
      else
        val pre = maybeOuter
        if pre.exists && addPrefix(pre) then
          val withPrefix = name match
            case TypeName(SuffixedName(NameTags.OBJECTCLASS, module)) =>
              pre.nameWithPrefix(addPrefix).toTermName.select(module.asSimpleName).withObjectSuffix
            case _ => pre.nameWithPrefix(addPrefix).toTermName.select(name.asSimpleName)
          if name.isTypeName then withPrefix.toTypeName
          else withPrefix
        else name

    final def fullName: Name = nameWithPrefix(_.isStatic)
    private[tastyquery] final def erasedName: Name = nameWithPrefix(_ => true)

    final def exists: Boolean = this ne NoSymbol

    final def isType: Boolean = name.isTypeName
    final def isTerm: Boolean = name.isTermName

    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageClassSymbol]

    final def asClass: ClassSymbol = this.asInstanceOf[ClassSymbol]

    private[tastyquery] final def memberIsOverloaded(name: SignedName): Boolean = this match
      case scope: DeclaringSymbol => scope.hasOverloads(name)
      case _                      => false

    private[tastyquery] final def memberOverloads(name: SignedName): List[Symbol] = this match
      case scope: DeclaringSymbol => scope.allOverloads(name)
      case _                      => Nil

    def lookup(name: Name)(using BaseContext): Option[Symbol] = this match
      case scope: DeclaringSymbol => scope.getDecl(name)
      case _                      => None

    override def toString: String = {
      val kind = this match
        case _: PackageClassSymbol => "package "
        case _: ClassSymbol        => if name.toTypeName.wrapsObjectName then "object class " else "class "
        case _                     => if exists && outer.isPackage then "object " else ""
      s"symbol[$kind$name]"
    }
    def toDebugString = toString
  }

  object Symbol {
    def unapply(s: Symbol): Option[Name] = Some(s.name)
  }

  final class RegularSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner) {
    private var mySignature: Option[Signature] | Null = null

    private[tastyquery] override final def signature(using BaseContext): Option[Signature] =
      val local = mySignature
      if local != null then local
      else
        val sig = declaredType match
          case methodOrPoly: (MethodType | PolyType) => Some(Signature.fromMethodOrPoly(methodOrPoly))
          case _                                     => None
        mySignature = sig
        sig
  }

  abstract class DeclaringSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner) {

    private[tastyquery] override final def signature(using BaseContext): Option[Signature] = None

    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    private[tastyquery] final def addDecl(decl: Symbol): Unit =
      myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet) += decl

    private[tastyquery] final def getDeclInternal(name: Name): Option[Symbol] = name match {
      case overloaded: SignedName =>
        None // need context to resolve overloads
      case name =>
        myDeclarations.get(name) match
          case Some(decls) =>
            if decls.sizeIs == 1 then Some(decls.head)
            else if decls.sizeIs > 1 then
              throw SymbolLookupException(name, s"unexpected overloads: ${decls.mkString(", ")}")
            else None // TODO: this should be an error
          case _ => None
    }

    private[Symbols] final def getDeclBase(name: Name)(using BaseContext): Option[Symbol] = name match
      case overloaded: SignedName =>
        distinguishOverloaded(overloaded)
      case name =>
        getDeclInternal(name)

    private[Symbols] final def hasOverloads(name: SignedName): Boolean =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.sizeIs > 1
        case _           => false

    private[Symbols] final def allOverloads(name: SignedName): List[Symbol] =
      myDeclarations.get(name.underlying) match
        case Some(decls) => decls.toList
        case _           => Nil

    def getDecl(name: Name)(using BaseContext): Option[Symbol] =
      getDeclBase(name)

    private final def distinguishOverloaded(overloaded: SignedName)(using BaseContext): Option[Symbol] =
      myDeclarations.get(overloaded.underlying) match
        case Some(overloads) =>
          if overloads.sizeIs == 1 then Some(overloads.head) // TODO: verify signature matches?
          else if overloads.sizeIs > 1 then overloads.find(s => s.signature.exists(_ == overloaded.sig))
          else None // TODO: this should be an error
        case None => None

    final def resolveOverloaded(name: SignedName)(using BaseContext): Option[Symbol] =
      getDecl(name)

    final def declarations: List[Symbol] = myDeclarations.values.toList.flatten

    final override def toDebugString: String =
      s"${super.toString} with declarations [${myDeclarations.keys.map(_.toDebugString).mkString(", ")}]"
  }

  class ClassSymbol(override val name: Name, rawowner: Symbol | Null) extends DeclaringSymbol(name, rawowner) {
    private[tastyquery] var initialised: Boolean = false

    // TODO: how do we associate some Symbols with TypeBounds, and some with Type?
    private var myTypeParams: List[(Symbol, TypeBounds)] | Null = null

    private[tastyquery] final def withTypeParams(tparams: List[Symbol], bounds: List[TypeBounds]): this.type =
      val local = myTypeParams
      if local != null then throw new IllegalStateException(s"reassignment of type parameters to $this")
      else
        myTypeParams = tparams.zip(bounds)
        this

    private def typeParamsInternal: List[(Symbol, TypeBounds)] =
      val local = myTypeParams
      if local == null then throw new IllegalStateException(s"expected type params for $this")
      else local

    /** Forces the class or package to be initialised, should never be called from within the initialisation
      * of this class or package.
      */
    private[tastyquery] final def ensureInitialised()(using BaseContext): Unit =
      def initialiseMembers(): Unit = this match
        case pkg: PackageClassSymbol => baseCtx.classloader.scanPackage(pkg)
        case cls                     => baseCtx.classloader.scanClass(cls)
      if !initialised then
        // TODO: maybe add flag and check against if we are currently initialising this symbol?
        initialiseMembers()
        assert(initialised)

    private[tastyquery] final def initParents: Boolean =
      myTypeParams != null

    // private[tastyquery] final def hasTypeParams: List[Symbol] = typeParamsInternal.map(_(0))
    private[tastyquery] final def typeParamSyms: List[Symbol] =
      typeParamsInternal.map(_(0))

    /** Get the self type of this class, as if viewed from an external package */
    private[tastyquery] final def accessibleThisType: Type = this match
      case pkg: PackageClassSymbol => PackageRef(pkg) // TODO: maybe we need this-type of package for package-private
      case cls =>
        maybeOuter match
          case pre: ClassSymbol => TypeRef(pre.accessibleThisType, cls)
          case _                => TypeRef(NoPrefix, cls)

    override def declaredType(using BaseContext): Type =
      ensureInitialised()
      super.declaredType

    override final def getDecl(name: Name)(using BaseContext): Option[Symbol] =
      ensureInitialised()
      getDeclBase(name)
  }

  // TODO: typename or term name?
  class PackageClassSymbol(override val name: Name, rawowner: PackageClassSymbol | Null)
      extends ClassSymbol(name, rawowner) {
    if (rawowner != null) {
      // A package symbol is always a declaration in its owner package
      rawowner.addDecl(this)
    } else {
      // Root package is the only symbol that is allowed to not have an owner
      assert(name == nme.RootName)
    }

    this.withDeclaredType(PackageRef(this))

    def findPackageSymbol(packageName: TermName): Option[PackageClassSymbol] = packageName match {
      case _: SimpleName => getPackageDecl(packageName)
      case QualifiedName(NameTags.QUALIFIED, prefix, suffix) =>
        if (prefix == name)
          getPackageDecl(packageName)
        else
          // recurse
          findPackageSymbol(prefix).flatMap(_.findPackageSymbol(packageName))
      case _ => throw IllegalArgumentException(s"Unexpected package name: $name")
    }

    override def lookup(name: Name)(using BaseContext): Option[Symbol] =
      val sel = name match {
        case name: SimpleName if this.name != nme.RootName => this.name.toTermName.select(name)
        case _                                             => name
      }
      getDecl(sel)

    private def getPackageDecl(packageName: TermName): Option[PackageClassSymbol] =
      /* All subpackages are created eagerly when initializing contexts,
       * so we can use getDeclInternal here.
       */
      getDeclInternal(packageName).map(_.asInstanceOf[PackageClassSymbol])

    override def withTree(t: DefTree): PackageClassSymbol.this.type = throw new UnsupportedOperationException(
      s"Multiple trees correspond to one package, a single tree cannot be assigned"
    )
  }

  abstract class SymbolFactory[T <: Symbol] {
    def createSymbol(name: Name, owner: Symbol): T
    def castSymbol(symbol: Symbol): T
  }

  object RegularSymbolFactory extends SymbolFactory[RegularSymbol] {
    override def createSymbol(name: Name, owner: Symbol): RegularSymbol = new RegularSymbol(name, owner)

    override def castSymbol(symbol: Symbol): RegularSymbol = symbol.asInstanceOf[RegularSymbol]
  }

  object ClassSymbolFactory extends SymbolFactory[ClassSymbol] {
    override def createSymbol(name: Name, owner: Symbol): ClassSymbol = new ClassSymbol(name, owner)

    override def castSymbol(symbol: Symbol): ClassSymbol = symbol.asInstanceOf[ClassSymbol]
  }

  object PackageClassSymbolFactory extends SymbolFactory[PackageClassSymbol] {
    override def createSymbol(name: Name, owner: Symbol): PackageClassSymbol =
      new PackageClassSymbol(name, owner.asInstanceOf[PackageClassSymbol])

    override def castSymbol(symbol: Symbol): PackageClassSymbol = symbol.asInstanceOf[PackageClassSymbol]
  }
}
