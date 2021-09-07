package tastyquery

import dotty.tools.tasty.TastyBuffer.Addr
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.TypeLambda

import scala.collection.mutable
import scala.collection.mutable.HashMap

object Contexts {

  /** The current context */
  inline def ctx(using ctx: FileContext): FileContext = ctx

  def empty: BaseContext =
    new BaseContext(new Definitions())

  def empty(filename: String): FileContext = {
    val defn = new Definitions()
    new FileContext(defn, defn.RootPackage, filename)
  }

  /** BaseContext is used throughout unpickling an entire project. */
  class BaseContext private[Contexts](val defn: Definitions) {
    def withFile(filename: String): FileContext =
      new FileContext(defn, defn.RootPackage, filename)

    def createPackageSymbolIfNew(name: TermName, owner: Symbol): PackageClassSymbol = {
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
  }

  /** FileLocalInfo maintains file-local information, used during unpickling:
    * @param filename -- the .tasty file being unpickled, used for error reporting
    * @param localSymbols -- map of the symbols, created when unpickling the current file.
    *                     A symbol can be referred to from anywhere in the file, therefore once the symbol is added
    *                     to the file info, it is kept in the context and its subcontexts.
    *  @param enclosingLambdas -- map of the type lambdas which have the current address in scope.
    *                          A type lambda can only be referred to if it encloses the referring address.
    *                          A new FileLocalInfo (hence a new FileContext) is created when an enclosing is added
    *                          to mimic the scoping.
    */
  class FileLocalInfo(
    val filename: String,
    val localSymbols: mutable.HashMap[Addr, Symbol] = mutable.HashMap.empty,
    val enclosingLambdas: Map[Addr, TypeLambda] = Map.empty
  ) {
    def addEnclosingLambda(addr: Addr, tl: TypeLambda): FileLocalInfo =
      new FileLocalInfo(filename, localSymbols, enclosingLambdas.updated(addr, tl))
  }

  /** FileContext is used when unpickling a given .tasty file.
    * It extends the BaseContext with the information,local to the file, and keeps track of the current owner.
    */
  class FileContext private[Contexts] (
    override val defn: Definitions,
    val owner: Symbol,
    private val fileLocalInfo: FileLocalInfo
  ) extends BaseContext(defn) {
    def this(defn: Definitions, owner: Symbol, filename: String) = this(defn, owner, new FileLocalInfo(filename))

    def withEnclosingLambda(addr: Addr, tl: TypeLambda): FileContext =
      new FileContext(defn, owner, fileLocalInfo.addEnclosingLambda(addr, tl))

    def withOwner(newOwner: Symbol): FileContext =
      if (newOwner == owner) this
      else new FileContext(defn, newOwner, fileLocalInfo)

    def getFile: String = fileLocalInfo.filename

    def getEnclosingLambda(addr: Addr): TypeLambda = fileLocalInfo.enclosingLambdas(addr)

    def hasSymbolAt(addr: Addr): Boolean = fileLocalInfo.localSymbols.contains(addr)

    private def registerSym(addr: Addr, sym: Symbol, addToDecls: Boolean): Unit = {
      fileLocalInfo.localSymbols(addr) = sym
      if (addToDecls && owner.isInstanceOf[DeclaringSymbol])
        owner.asInstanceOf[DeclaringSymbol].addDecl(sym)
    }

    /** Creates a new symbol at @addr with @name. The symbol is added to the owner's declarations if both
      * 1) @addToDecls is true.
      *    Example: true for valdef and defdef, false for parameters and type parameters
      * 2) the owner is a declaring symbol.
      *    Example: a method is added to the declarations of its class, but a nested method is not added
      *    to declarations of its owner method.
      */
    def createSymbolIfNew[T <: Symbol](
      addr: Addr,
      name: Name,
      factory: SymbolFactory[T],
      addToDecls: Boolean = false
    ): T = {
      if (!hasSymbolAt(addr)) {
        registerSym(addr, factory.createSymbol(name, owner), addToDecls)
      }
      fileLocalInfo.localSymbols(addr).asInstanceOf[T]
    }

    def createPackageSymbolIfNew(name: TermName): PackageClassSymbol = super.createPackageSymbolIfNew(name, owner)

    def getSymbol(addr: Addr): Symbol =
      fileLocalInfo.localSymbols(addr)
    def getSymbol[T <: Symbol](addr: Addr, symbolFactory: SymbolFactory[T]): T =
      symbolFactory.castSymbol(fileLocalInfo.localSymbols(addr))
  }
}
