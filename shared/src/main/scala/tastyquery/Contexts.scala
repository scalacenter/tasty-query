package tastyquery

import dotty.tools.tasty.TastyBuffer.Addr
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.{Type, Symbolic, Binders, PackageRef, TypeRef}

import scala.collection.mutable
import scala.collection.mutable.HashMap
import tastyquery.reader.classfiles.Classpaths
import tastyquery.reader.classfiles.Classpaths.Classpath
import scala.util.Try
import scala.util.control.NonFatal

object Contexts {

  /** The current context */
  inline def ctx(using ctx: FileContext): FileContext = ctx
  transparent inline def baseCtx(using baseCtx: BaseContext): BaseContext = baseCtx
  transparent inline def clsCtx(using clsCtx: ClassContext): ClassContext = clsCtx
  transparent inline def defn(using baseCtx: BaseContext): baseCtx.defn.type = baseCtx.defn

  def init(classpath: Classpath): BaseContext =
    val baseCtx = classpath.loader { classloader =>
      val baseCtx = BaseContext(Definitions(), classloader)
      baseCtx.classloader.initPackages()(using baseCtx)
      baseCtx
    }
    baseCtx.initializeFundamentalClasses()
    baseCtx

  private[Contexts] def moduleClassRoot(classRoot: ClassSymbol): ClassSymbol = {
    val pkg = classRoot.enclosingDecl
    ClassSymbolFactory.castSymbol(pkg.getDecl(classRoot.name.toTypeName.toObjectName).get)
  }

  private[Contexts] def moduleRoot(classRoot: ClassSymbol): RegularSymbol = {
    val pkg = classRoot.enclosingDecl
    RegularSymbolFactory.castSymbol(pkg.getDecl(classRoot.name.toTermName).get)
  }

  private[tastyquery] def initialisedRoot(classRoot: ClassSymbol): Boolean =
    classRoot.initialised || moduleClassRoot(classRoot).initialised

  /** BaseContext is used throughout unpickling an entire project. */
  class BaseContext private[Contexts] (val defn: Definitions, val classloader: Classpaths.Loader) {

    def withFile(root: ClassSymbol, filename: String)(using Classpaths.permissions.LoadRoot): FileContext =
      new FileContext(defn, root, filename, classloader)

    def withRoot(root: ClassSymbol)(using Classpaths.permissions.LoadRoot): ClassContext =
      new ClassContext(defn, classloader, root)

    def getClassIfDefined(fullClassName: String): Option[ClassSymbol] =
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
      val symOpt =
        try Some(packageAndClass(fullClassName).resolveToSymbol(using this))
        catch
          case NonFatal(e) =>
            println(s"[error] Cannot resolve class $fullClassName: $e")
            None
      symOpt match
        case Some(cls: ClassSymbol) => Some(cls)
        case _                      => None

    def createClassSymbol(name: Name, owner: DeclaringSymbol): ClassSymbol =
      owner.getDecl(name) match
        case None =>
          val cls = ClassSymbolFactory.createSymbol(name, owner)
          owner.addDecl(cls)
          cls
        case some =>
          throw ExistingDefinitionException(owner, name)

    def createSymbol(name: Name, owner: DeclaringSymbol): RegularSymbol =
      owner.getDecl(name) match
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

      // TODO Assign superclasses and create members

      val anyClass = createClassSymbol(typeName("Any"), scalaPackage)
      anyClass.initialised = true

      val nullClass = createClassSymbol(typeName("Null"), scalaPackage)
      nullClass.initialised = true

      val nothingClass = createClassSymbol(typeName("Nothing"), scalaPackage)
      nothingClass.initialised = true
    }
  }

  class ClassContext private[Contexts] (
    override val defn: Definitions,
    override val classloader: Classpaths.Loader,
    val owner: ClassSymbol
  ) extends BaseContext(defn, classloader) {

    def classRoot: ClassSymbol = owner

    def moduleClassRoot: ClassSymbol = Contexts.moduleClassRoot(classRoot)

    def moduleRoot: RegularSymbol = Contexts.moduleRoot(classRoot)

    def createSymbol[T <: Symbol](name: Name, factory: SymbolFactory[T], addToDecls: Boolean = false): T =
      owner.getDecl(name) match
        case None =>
          val sym = factory.createSymbol(name, owner)
          if (addToDecls) owner.addDecl(sym)
          sym
        case some =>
          throw ExistingDefinitionException(owner, name)

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
    * It extends the BaseContext with the information,local to the file, and keeps track of the current owner.
    */
  class FileContext private[Contexts] (
    override val defn: Definitions,
    val classRoot: ClassSymbol,
    val owner: Symbol,
    private val fileLocalInfo: FileLocalInfo,
    override val classloader: Classpaths.Loader
  ) extends BaseContext(defn, classloader) { base =>

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
          owner.lookup(name) match
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
