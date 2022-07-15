package tastyquery

import scala.annotation.tailrec

import dotty.tools.tasty.TastyBuffer.Addr
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.{Type, Symbolic, Binders, PackageRef, TypeRef, SymResolutionProblem}

import scala.collection.mutable
import scala.collection.mutable.HashMap
import tastyquery.reader.classfiles.Classpaths
import tastyquery.reader.classfiles.Classpaths.Classpath
import scala.util.Try
import scala.util.control.NonFatal

object Contexts {

  /** The current context */
  inline def fileCtx(using ctx: FileContext): FileContext = ctx
  transparent inline def ctx(using ctx: Context): Context = ctx
  transparent inline def clsCtx(using clsCtx: ClassContext): ClassContext = clsCtx
  transparent inline def defn(using ctx: Context): ctx.defn.type = ctx.defn

  def init(classpath: Classpath): Context =
    val ctx = classpath.loader { classloader =>
      val ctx = Context(Definitions(), classloader)
      ctx.classloader.initPackages()(using ctx)
      ctx
    }
    ctx.initializeFundamentalClasses()
    ctx

  private[Contexts] def moduleClassRoot(classRoot: ClassSymbol)(using Context): ClassSymbol = {
    val pkg = classRoot.enclosingDecl
    ClassSymbolFactory.castSymbol(pkg.getDecl(classRoot.name.toTypeName.toObjectName).get)
  }

  private[Contexts] def moduleRoot(classRoot: ClassSymbol)(using Context): RegularSymbol = {
    val pkg = classRoot.enclosingDecl
    RegularSymbolFactory.castSymbol(pkg.getDecl(classRoot.name.toTermName).get)
  }

  private[tastyquery] def initialisedRoot(classRoot: ClassSymbol)(using Context): Boolean =
    classRoot.initialised || moduleClassRoot(classRoot).initialised

  /** Context is used throughout unpickling an entire project. */
  class Context private[Contexts] (val defn: Definitions, val classloader: Classpaths.Loader) {
    private given Context = this

    def withFile(root: ClassSymbol, filename: String)(using Classpaths.permissions.LoadRoot): FileContext =
      new FileContext(defn, root, filename, classloader)

    def withRoot(root: ClassSymbol)(using Classpaths.permissions.LoadRoot): ClassContext =
      new ClassContext(defn, classloader, root)

    def getClassIfDefined(fullClassName: String): Either[SymResolutionProblem, ClassSymbol] =
      def packageAndClass(fullClassName: String): TypeRef = {
        val lastSep = fullClassName.lastIndexOf('.')
        if (lastSep == -1) TypeRef(PackageRef(nme.EmptyPackageName), typeName(fullClassName))
        else {
          import scala.language.unsafeNulls
          val packageName = fullClassName.substring(0, lastSep)
          val className = typeName(fullClassName.substring(lastSep + 1))
          TypeRef(PackageRef(classloader.toPackageName(packageName)), className)
        }
      }
      val symEither =
        try Right(packageAndClass(fullClassName).resolveToSymbol(using this))
        catch
          case e: SymResolutionProblem =>
            Left(e)
      (symEither: @unchecked) match
        case Right(cls: ClassSymbol) => Right(cls)
        case Left(err)               => Left(err) // let Right of non-class throw - it should not occur

    def findSymbolFromRoot(path: List[Name]): Symbol =
      @tailrec
      def rec(owner: Symbol, path: List[Name]): Symbol =
        path match
          case Nil =>
            owner
          case name :: pathRest =>
            val sym = owner.lookup(name).getOrElse {
              throw new IllegalArgumentException(s"cannot find member ${name.toDebugString} in $owner")
            }
            rec(sym, pathRest)

      rec(defn.RootPackage, path)
    end findSymbolFromRoot

    def createClassSymbol(name: Name, owner: DeclaringSymbol): ClassSymbol =
      owner.getDeclInternal(name) match
        case None =>
          val cls = ClassSymbolFactory.createSymbol(name, owner)
          owner.addDecl(cls)
          cls
        case some =>
          throw ExistingDefinitionException(owner, name)

    def createSymbol(name: Name, owner: DeclaringSymbol): RegularSymbol =
      owner.getDeclInternal(name) match
        case None =>
          val sym = RegularSymbolFactory.createSymbol(name, owner)
          owner.addDecl(sym)
          sym
        case some =>
          throw ExistingDefinitionException(owner, name)

    def createPackageSymbolIfNew(name: TermName, owner: PackageClassSymbol): PackageClassSymbol = {
      def create(): PackageClassSymbol = {
        val trueOwner = if (owner == defn.EmptyPackage) defn.RootPackage else owner
        val sym = PackageClassSymbolFactory.createSymbol(name, trueOwner)
        sym
      }

      defn.RootPackage.findPackageSymbol(name) match {
        case Some(pkg) => pkg
        case None =>
          name match {
            case _: SimpleName => create()
            case QualifiedName(NameTags.QUALIFIED, prefix, _) =>
              if (prefix == owner.name) {
                create()
              } else {
                // create intermediate packages
                val newOwner = createPackageSymbolIfNew(prefix, owner)
                createPackageSymbolIfNew(name, newOwner)
              }
            case _ =>
              throw IllegalArgumentException(s"Unexpected package name: $name")
          }
      }
    }

    def getPackageSymbol(name: TermName): PackageClassSymbol = defn.RootPackage.findPackageSymbol(name).get

    private[Contexts] def initializeFundamentalClasses(): Unit = {
      val scalaPackage = createPackageSymbolIfNew(nme.scalaPackageName, defn.RootPackage)
      val javaLangPackage = createPackageSymbolIfNew(nme.javalangPackageName, defn.RootPackage)

      // TODO Assign superclasses and create members

      def initialise(cls: ClassSymbol): Unit =
        cls.withTypeParams(Nil, Nil)
        cls.initialised = true

      val anyClass = createClassSymbol(typeName("Any"), scalaPackage)
      initialise(anyClass)

      val nullClass = createClassSymbol(typeName("Null"), scalaPackage)
      initialise(nullClass)

      val nothingClass = createClassSymbol(typeName("Nothing"), scalaPackage)
      initialise(nothingClass)

      def fakeJavaLangClassIfNotFound(name: String): ClassSymbol =
        // TODO: add java.lang package in tests
        val tname = typeName(name)
        javaLangPackage.getDeclInternal(tname) match
          case Some(sym: ClassSymbol) =>
            sym
          case _ =>
            val sym = createClassSymbol(tname, javaLangPackage)
            initialise(sym)
            sym

      fakeJavaLangClassIfNotFound("Object")
      fakeJavaLangClassIfNotFound("Comparable")
      fakeJavaLangClassIfNotFound("Serializable")
      fakeJavaLangClassIfNotFound("String")
      fakeJavaLangClassIfNotFound("Throwable")
      fakeJavaLangClassIfNotFound("Error")
      fakeJavaLangClassIfNotFound("Exception")
    }
  }

  class ClassContext private[Contexts] (
    override val defn: Definitions,
    override val classloader: Classpaths.Loader,
    val owner: ClassSymbol
  ) extends Context(defn, classloader) {

    def classRoot: ClassSymbol = owner

    def moduleClassRoot: ClassSymbol = Contexts.moduleClassRoot(classRoot)(using this)

    def moduleRoot: RegularSymbol = Contexts.moduleRoot(classRoot)(using this)

    /*def createSymbol[T <: Symbol](name: Name, factory: SymbolFactory[T], addToDecls: Boolean): T =
      val sym = factory.createSymbol(name, owner)
      if (addToDecls) owner.addDecl(sym)
      sym*/

  }

  /** FileLocalInfo maintains file-local information, used during unpickling:
    * @param filename -- the .tasty file being unpickled, used for error reporting
    * @param localSymbols -- map of the symbols, created when unpickling the current file.
    *                     A symbol can be referred to from anywhere in the file, therefore once the symbol is added
    *                     to the file info, it is kept in the context and its subcontexts.
    *  @param enclosingBinders -- map of the type binders which have the current address in scope.
    *                          A type binder can only be referred to if it encloses the referring address.
    *                          A new FileLocalInfo (hence a new FileContext) is created when an enclosing is added
    *                          to mimic the scoping.
    */
  class FileLocalInfo(
    val filename: String,
    val localSymbols: mutable.HashMap[Addr, Symbol] = mutable.HashMap.empty,
    val enclosingBinders: Map[Addr, Binders] = Map.empty
  ) {
    def addEnclosingBinders(addr: Addr, b: Binders): FileLocalInfo =
      new FileLocalInfo(filename, localSymbols, enclosingBinders.updated(addr, b))
  }

  /** FileContext is used when unpickling a given .tasty file.
    * It extends the Context with the information,local to the file, and keeps track of the current owner.
    */
  class FileContext private[Contexts] (
    override val defn: Definitions,
    val classRoot: ClassSymbol,
    val owner: Symbol,
    private val fileLocalInfo: FileLocalInfo,
    override val classloader: Classpaths.Loader
  ) extends Context(defn, classloader) { base =>

    private[Contexts] def this(
      defn: Definitions,
      classRoot: ClassSymbol,
      filename: String,
      classloader: Classpaths.Loader
    ) = this(defn, classRoot, defn.RootPackage, new FileLocalInfo(filename), classloader)

    def withEnclosingBinders(addr: Addr, b: Binders): FileContext =
      new FileContext(defn, classRoot, owner, fileLocalInfo.addEnclosingBinders(addr, b), classloader)

    def withOwner(newOwner: Symbol): FileContext =
      if (newOwner == owner) this
      else new FileContext(defn, classRoot, newOwner, fileLocalInfo, classloader)

    def getFile: String = fileLocalInfo.filename

    def getEnclosingBinders(addr: Addr): Binders = fileLocalInfo.enclosingBinders(addr)

    def hasSymbolAt(addr: Addr): Boolean = fileLocalInfo.localSymbols.contains(addr)

    private def registerSym[T <: Symbol](addr: Addr, sym: T, addToDecls: Boolean): T =
      fileLocalInfo.localSymbols(addr) = sym
      if addToDecls then
        owner match
          case owner: DeclaringSymbol => owner.addDecl(sym)
          case _ => throw IllegalArgumentException(s"can not add $sym to decls of non-declaring symbol $owner")
      sym

    /** Creates a new symbol at @addr with @name. If `addToDecls` is true, the symbol is added to the owner's
      * declarations: this requires that the owner is a `DeclaringSymbol`, or else throws.
      *
      * @note `addToDecls` should be `true` for ValDef and DefDef, `false` for parameters and type parameters.
      * @note A method is added to the declarations of its class, but a nested method should not added
      *    to declarations of the outer method.
      */
    def createSymbol[T <: Symbol](addr: Addr, name: Name, factory: SymbolFactory[T], addToDecls: Boolean): T =

      extension (s: ClassSymbol)
        def isModuleClassRoot: Boolean = s.name.toTermName match
          case SuffixedName(NameTags.OBJECTCLASS, module) => module == classRoot.name.toTermName
          case _                                          => false

      extension (s: RegularSymbol)
        def isModuleRoot: Boolean =
          s.name == classRoot.name.toTermName

      def mkSymbol(name: Name, owner: Symbol): T =
        if owner == classRoot.enclosingDecl then
          val existing = owner match
            case owner: DeclaringSymbol => owner.getDeclInternal(name)
            case _                      => None
          existing match
            case Some(sym) =>
              (factory, sym) match
                case (ClassSymbolFactory, `classRoot`)                               => classRoot
                case (ClassSymbolFactory, sym: ClassSymbol) if sym.isModuleClassRoot => sym
                case (RegularSymbolFactory, sym: RegularSymbol) if sym.isModuleRoot  => sym
                case _ => throw ExistingDefinitionException(owner, name, explanation = s"existing symbol: $sym")
            case _ => factory.createSymbol(name, owner)
        else factory.createSymbol(name, owner)

      if !hasSymbolAt(addr) then registerSym(addr, mkSymbol(name, owner), addToDecls)
      else throw ExistingDefinitionException(owner, name)

    def createPackageSymbolIfNew(name: TermName): PackageClassSymbol = owner match {
      case owner: PackageClassSymbol => base.createPackageSymbolIfNew(name, owner)
      case owner                     => assert(false, s"Unexpected non-package owner: $owner")
    }

    def getSymbol(addr: Addr): Symbol =
      fileLocalInfo.localSymbols(addr)
    def getSymbol[T <: Symbol](addr: Addr, symbolFactory: SymbolFactory[T]): T =
      symbolFactory.castSymbol(fileLocalInfo.localSymbols(addr))
  }
}
