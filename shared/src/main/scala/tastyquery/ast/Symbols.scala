package tastyquery.ast

import scala.collection.mutable
import tastyquery.ast.Names.{Name, TermName, SignedName, SimpleName, QualifiedName, TypeName, SuffixedName, nme}
import dotty.tools.tasty.TastyFormat.NameTags
import tastyquery.ast.Trees.{DefTree, Tree}
import tastyquery.ast.Types.*
import tastyquery.Contexts.BaseContext

object Symbols {

  class ExistingDefinitionException(val scope: Symbol, val name: Name, explanation: String = "")
      extends Exception(
        SymbolLookupException.addExplanation(s"$scope has already defined ${name.toDebugString}", explanation)
      )

  class SymbolLookupException(val name: Name, explanation: String = "")
      extends RuntimeException(
        SymbolLookupException.addExplanation(s"Could not find symbol for name ${name.toDebugString}", explanation)
      )

  object SymbolLookupException {
    def unapply(e: SymbolLookupException): Option[Name] = Some(e.name)

    def addExplanation(msg: String, explanation: String): String =
      if (explanation.isEmpty) msg else s"$msg: $explanation"
  }

  val NoSymbol = new RegularSymbol(nme.EmptyTermName, null)

  abstract class Symbol private[Symbols] (val name: Name, rawowner: Symbol | Null) {
    protected var myTree: Option[DefTree] = None
    // overridden in package symbol
    def withTree(t: DefTree): this.type = {
      myTree = Some(t)
      this
    }
    final def tree: Option[DefTree] = myTree

    private var myDeclaredType: Type | Null = null

    private[tastyquery] def withDeclaredType(tpe: Type): this.type =
      myDeclaredType = tpe
      this

    def declaredType: Type =
      val local = myDeclaredType
      if local != null then local
      else throw new IllegalStateException(s"$this was not assigned a declared type")

    final def outer: Symbol = rawowner match {
      case owner: Symbol => owner
      case null          => assert(false, s"cannot access outer, ${this.name} was not declared within any scope")
    }

    final def enclosingDecl: DeclaringSymbol = rawowner match {
      case owner: DeclaringSymbol => owner
      case _: Symbol | null =>
        assert(false, s"cannot access owner, ${this.name} is local or not declared within any scope")
    }

    private[Symbol] def maybeOuter: Symbol = rawowner match {
      case owner: Symbol => owner
      case null          => NoSymbol
    }

    private[tastyquery] final def enclosingDecls: Iterator[DeclaringSymbol] =
      Iterator.iterate(enclosingDecl)(_.enclosingDecl).takeWhile(s => s.maybeOuter.exists)

    private[tastyquery] final def isStatic: Boolean =
      Iterator
        .iterate(this)(_.outer)
        .takeWhile(s => s.maybeOuter.exists)
        .forall(s => s.isPackage || s.isClass && s.name.toTypeName.wrapsObjectName)

    final def fullName: Name =
      if isPackage then name
      else
        val pre = maybeOuter
        if pre.exists && pre.isStatic then
          val withPrefix = name match
            case TypeName(SuffixedName(NameTags.OBJECTCLASS, module)) =>
              pre.fullName.toTermName.select(module.asSimpleName).withObjectSuffix
            case _ => pre.fullName.toTermName.select(name.asSimpleName)
          if name.isTypeName then withPrefix.toTypeName
          else withPrefix
        else name

    final def exists: Boolean = this ne NoSymbol

    final def isClass: Boolean = this.isInstanceOf[ClassSymbol]
    final def isPackage: Boolean = this.isInstanceOf[PackageClassSymbol]

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

  final class RegularSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner)

  abstract class DeclaringSymbol(override val name: Name, rawowner: Symbol | Null) extends Symbol(name, rawowner) {
    /* A map from the name of a declaration directly inside this symbol to the corresponding symbol
     * The qualifiers on the name are not dropped. For instance, the package names are always fully qualified. */
    private val myDeclarations: mutable.HashMap[Name, mutable.HashSet[Symbol]] =
      mutable.HashMap[Name, mutable.HashSet[Symbol]]()

    private[tastyquery] final def addDecl(decl: Symbol): Unit =
      myDeclarations.getOrElseUpdate(decl.name, new mutable.HashSet) += decl

    private[tastyquery] final def getDeclInternal(name: Name): Option[Symbol] = name match {
      case overloaded: SignedName =>
        getDeclInternal(overloaded.underlying) // TODO: look at signature to filter overloads
      case name =>
        myDeclarations.get(name) match
          case Some(decls) =>
            if decls.sizeIs == 1 then Some(decls.head)
            else if decls.sizeIs > 1 then
              throw SymbolLookupException(name, s"unexpected overloads: ${decls.mkString(", ")}")
            else None
          case _ => None
    }

    def getDecl(name: Name)(using BaseContext): Option[Symbol] =
      getDeclInternal(name)

    final def resolveOverloaded(name: SignedName)(using BaseContext): Option[Symbol] =
      getDecl(name)

    final def declarations: List[Symbol] = myDeclarations.values.toList.flatten

    final override def toDebugString: String =
      s"${super.toString} with declarations [${myDeclarations.keys.map(_.toDebugString).mkString(", ")}]"
  }

  class ClassSymbol(override val name: Name, rawowner: Symbol | Null) extends DeclaringSymbol(name, rawowner) {
    private[tastyquery] var initialised: Boolean = false

    override def getDecl(name: Name)(using BaseContext): Option[Symbol] =
      getDeclInternal(name).orElse {
        summon[BaseContext].classloader.scanClass(this)
        getDeclInternal(name)
      }
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

    override def getDecl(name: Name)(using BaseContext): Option[Symbol] =
      getDeclInternal(name).orElse {
        summon[BaseContext].classloader.scanPackage(this)
        getDeclInternal(name)
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
