package tastyquery

import scala.annotation.tailrec

import dotty.tools.tasty.TastyBuffer.Addr
import dotty.tools.tasty.TastyFormat.NameTags

import tastyquery.ast.Flags.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.*

import tastyquery.reader.classfiles.Classpaths.{Classpath, Loader}

import tastyquery.util.syntax.chaining.given

object Contexts {

  /** The current context */
  transparent inline def ctx(using ctx: Context): Context = ctx
  transparent inline def defn(using ctx: Context): ctx.defn.type = ctx.defn

  def init(classpath: Classpath): Context =
    val ctx = classpath.loader { classloader =>
      val ctx = new Context(classloader)
      ctx.classloader.initPackages()(using ctx)
      ctx
    }
    ctx.initializeFundamentalClasses()
    ctx

  /** Has the root been initialised already? Does not force, but returns true if at least one root was entered */
  private[tastyquery] def initialisedRoot(root: Loader.Root): Boolean =
    root.pkg.getDeclInternal(root.rootName).isDefined // module value
      || root.pkg.getDeclInternal(root.rootName.toTypeName).isDefined // class value

  /** Context is used throughout unpickling an entire project. */
  final class Context private[Contexts] (val classloader: Loader) {
    private given Context = this

    private val (RootPackage @ _, EmptyPackage @ _) = PackageClassSymbol.createRoots()

    val defn: Definitions = Definitions(this: @unchecked, RootPackage, EmptyPackage)

    /** basically an internal method for loading Java classes embedded in Java descriptors */
    private[tastyquery] def getClassFromBinaryName(binaryName: String): Either[SymResolutionProblem, ClassSymbol] =
      getRootIfDefined(binaryName).flatMap { root =>
        root.pkg
          .getDecl(root.rootName.toTypeName)
          .collect { case cls: ClassSymbol => cls }
          .toRight(SymbolLookupException(root.rootName, s"in ${root.pkg.fullName}; perhaps it is not on the classpath"))
      }

    /** Does there possibly exist a root for the given binary name. Does not force any classes covered by the name */
    private[tastyquery] def existsRoot(binaryName: String): Boolean =
      getRootIfDefined(binaryName).isRight

    /** Force a root to discover any top level symbols covered by the root. */
    private[tastyquery] def rootSymbolsIfDefined(binaryName: String): List[Symbol] =
      getRootIfDefined(binaryName) match
        case Right(root) =>
          root.pkg.getDecl(root.rootName.toTypeName).toList // class value
            ++ root.pkg.getDecl(root.rootName).toList // module value
            ++ root.pkg.getDecl(root.rootName.withObjectSuffix.toTypeName).toList // module class value
        case Left(_) => Nil

    /** Returns a root if there exists one on the classpath, does not force the underlying root symbols */
    private def getRootIfDefined(binaryName: String): Either[SymResolutionProblem, Loader.Root] =
      val (packageName, rootName) =
        val lastSep = binaryName.lastIndexOf('.')
        if lastSep == -1 then
          val rootName = termName(binaryName)
          (FullyQualifiedName(nme.EmptyPackageName :: Nil), rootName)
        else
          import scala.language.unsafeNulls
          val packageName = binaryName.substring(0, lastSep)
          val rootName = termName(binaryName.substring(lastSep + 1))
          (classloader.toPackageName(packageName), rootName)
      try
        val pkg = PackageRef(packageName).resolveToSymbol
        pkg
          .possibleRoot(rootName)
          .toRight(SymbolLookupException(rootName, s"no root $rootName exists in package $packageName"))
      catch
        case e: SymResolutionProblem =>
          Left(SymbolLookupException(rootName, s"unknown package $packageName"))

    def findPackageFromRoot(fullyQualifiedName: FullyQualifiedName): PackageClassSymbol =
      @tailrec
      def rec(owner: PackageClassSymbol, path: List[Name]): PackageClassSymbol =
        path match
          case Nil =>
            owner
          case (name: SimpleName) :: pathRest =>
            val next = owner.getPackageDecl(name).getOrElse {
              throw SymbolLookupException(name, s"cannot find package member $name of $owner")
            }
            rec(next, pathRest)
          case name :: pathRest =>
            throw SymbolLookupException(name, s"cannot find package member $name of $owner")
      rec(RootPackage, fullyQualifiedName.path)
    end findPackageFromRoot

    def findSymbolFromRoot(path: List[Name]): Symbol =
      @tailrec
      def rec(symbol: Symbol, path: List[Name]): Symbol =
        path match
          case Nil =>
            symbol
          case name :: pathRest =>
            val owner = symbol match
              case owner: DeclaringSymbol => owner
              case _ =>
                throw IllegalArgumentException(
                  s"$symbol does not declare a scope, cannot find member ${name.toDebugString}"
                )
            val next = owner.getDecl(name).getOrElse {
              throw IllegalArgumentException(s"cannot find member ${name.toDebugString} in $symbol")
            }
            rec(next, pathRest)
      rec(RootPackage, path)
    end findSymbolFromRoot

    def createClassSymbol(name: TypeName, owner: DeclaringSymbol): ClassSymbol =
      owner.getDeclInternal(name) match
        case None =>
          val cls = ClassSymbol.create(name, owner)
          owner.addDecl(cls)
          cls
        case some =>
          throw ExistingDefinitionException(owner, name)

    def createSymbol(name: Name, owner: DeclaringSymbol): RegularSymbol =
      owner.getDeclInternal(name) match
        case None =>
          val sym = RegularSymbol.create(name, owner)
          owner.addDecl(sym)
          sym
        case some =>
          throw ExistingDefinitionException(owner, name)

    def createPackageSymbolIfNew(name: SimpleName, owner: PackageClassSymbol): PackageClassSymbol =
      assert(owner != EmptyPackage, s"Trying to create a subpackage $name of $owner")
      owner.getPackageDeclInternal(name) match {
        case Some(pkg) => pkg
        case None      => PackageClassSymbol.create(name, owner)
      }

    def createPackageSymbolIfNew(fullyQualifiedName: FullyQualifiedName): PackageClassSymbol =
      fullyQualifiedName.path.foldLeft(RootPackage) { (owner, name) =>
        createPackageSymbolIfNew(name.asSimpleName, owner)
      }

    private[Contexts] def initializeFundamentalClasses(): Unit = {
      // TODO Assign superclasses and create members

      def fakeJavaLangClassIfNotFound(name: String): ClassSymbol =
        val tname = typeName(name)
        defn.javaLangPackage.getDecl(tname) match
          case Some(sym: ClassSymbol) =>
            sym
          case _ =>
            val sym = createClassSymbol(tname, defn.javaLangPackage)
            sym.initialised = true
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
}
