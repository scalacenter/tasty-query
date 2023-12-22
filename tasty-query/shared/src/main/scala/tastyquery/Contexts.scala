package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Classpaths.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

import tastyquery.reader.Loaders.Loader

/** Container for top-level definitions related to contexts.
  *
  * See [[Contexts.Context]] for more details.
  */
object Contexts {

  /** The implicitly available context. */
  inline def ctx(using ctx: Context): Context = ctx

  /** Standard definitions of symbols and types. */
  inline def defn(using ctx: Context): ctx.defn.type = ctx.defn

  /** Factory methods for [[Context]]. */
  object Context:
    /** Creates a new [[Context]] for the given [[Classpaths.Classpath]].
      *
      * If all the [[Classpaths.ClasspathEntry ClasspathEntries]] in the classpath
      * are thread-safe, then the resulting [[Context]] is thread-safe.
      */
    def initialize(classpath: Classpath): Context =
      val classloader = Loader(classpath)
      val ctx = new Context(classloader)
      classloader.initPackages()(using ctx)

      /* Exploit the portable releaseFence() call inside the `::` constructor,
       * in order to publish all the mutations that were done during the
       * above initialization to other threads.
       */
      new ::(Nil, Nil)

      ctx
    end initialize
  end Context

  /** A semantic universe for a given [[Classpaths.Classpath]].
    *
    * A [[Context]] gathers all the semantic information about symbols, types
    * and trees that can be found in a given classpath. It represents a
    * "universe" in which all definitions are related to each other.
    *
    * It is common practice to carry a `(using Context)` in every method that
    * manipulates a given universe. Virtually all methods of the tasty-query
    * API require a given `Context`. The current given `Context` can be
    * accessed with [[ctx]].
    *
    * The main entry point is the method [[findSymbolFromRoot]], which gives
    * access to a top-level symbol from its fully-qualified name path.
    *
    * Another likely entry point is to use [[Definitions.RootPackage defn.RootPackage]] to obtain the
    * root package package symbol, and explore everything from there using
    * [[Symbols.DeclaringSymbol.getDecl]] and/or
    * [[Symbols.DeclaringSymbol.declarations]].
    *
    * The same instance of [[Classpaths.Classpath]] can be reused to create
    * several [[Context]]s, if necessary.
    */
  final class Context private[Contexts] (classloader: Loader) {
    private given Context = this

    private val sourceFiles = mutable.HashMap.empty[String, SourceFile]

    private val (RootPackage @ _, EmptyPackage @ _) = PackageSymbol.createRoots()

    private[tastyquery] def hasGenericTuples: Boolean = classloader.hasGenericTuples

    val defn: Definitions = Definitions(this: @unchecked, RootPackage, EmptyPackage)

    private[tastyquery] def internalClasspathForTestsOnly: Classpath = classloader.classpath

    private[tastyquery] def getSourceFile(path: String): SourceFile =
      sourceFiles.getOrElseUpdate(path, new SourceFile(path))

    /** For a given classpath entry, return a lazy view over all the roots covered by the entry. */
    def findSymbolsByClasspathEntry(entry: ClasspathEntry): Iterable[TermOrTypeSymbol] =
      classloader.lookupByEntry(entry).getOrElse {
        throw new UnknownClasspathEntry(entry)
      }

    def findPackageFromRoot(fullyQualifiedName: PackageFullName): PackageSymbol =
      @tailrec
      def rec(owner: PackageSymbol, path: List[Name]): PackageSymbol =
        path match
          case Nil =>
            owner
          case (name: SimpleName) :: pathRest =>
            val next = owner.getPackageDecl(name).getOrElse {
              throw MemberNotFoundException(owner, name, s"cannot find package member $name of $owner")
            }
            rec(next, pathRest)
          case name :: pathRest =>
            throw MemberNotFoundException(owner, name, s"cannot find package member $name of $owner")
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
                throw MemberNotFoundException(
                  symbol,
                  name,
                  s"$symbol does not declare a scope, cannot find member ${name.toDebugString}"
                )
            val next = owner.getDecl(name).getOrElse {
              throw MemberNotFoundException(owner, name, s"cannot find member ${name.toDebugString} in $symbol")
            }
            rec(next, pathRest)
      rec(RootPackage, path)
    end findSymbolFromRoot

    def findPackage(fullyQualifiedName: String): PackageSymbol =
      findPackageFromRoot(PackageFullName(fullyQualifiedName.split('.').toList.map(termName(_))))

    def findTopLevelClass(fullyQualifiedName: String): ClassSymbol =
      val (pkg, nameStr) = splitPackageAndName(fullyQualifiedName)
      val name = typeName(nameStr)
      pkg.getDecl(name) match
        case Some(cls: ClassSymbol) =>
          cls
        case _ =>
          throw MemberNotFoundException(pkg, name, s"cannot find class $nameStr in $pkg")
    end findTopLevelClass

    def findTopLevelModuleClass(fullyQualifiedName: String): ClassSymbol =
      val (pkg, nameStr) = splitPackageAndName(fullyQualifiedName)
      val name = termName(nameStr).withObjectSuffix.toTypeName
      pkg.getDecl(name) match
        case Some(cls: ClassSymbol) =>
          cls
        case _ =>
          throw MemberNotFoundException(pkg, name, s"cannot find module class $nameStr in $pkg")
    end findTopLevelModuleClass

    def findStaticClass(fullyQualifiedName: String): ClassSymbol =
      findStaticType(fullyQualifiedName) match
        case cls: ClassSymbol =>
          cls
        case sym =>
          throw InvalidProgramStructureException(s"expected class symbol but got $sym")
    end findStaticClass

    def findStaticModuleClass(fullyQualifiedName: String): ClassSymbol =
      findStaticTerm(fullyQualifiedName) match
        case sym if sym.isModuleVal =>
          sym.moduleClass.get
        case sym =>
          throw InvalidProgramStructureException(s"expected module symbol but got $sym")
    end findStaticModuleClass

    def findStaticType(fullyQualifiedName: String): TypeSymbol =
      val (owner, nameStr) = findStaticOwnerAndName(fullyQualifiedName)
      val name = typeName(nameStr)
      owner
        .getDecl(name)
        .getOrElse {
          throw MemberNotFoundException(owner, name)
        }
    end findStaticType

    def findStaticTerm(fullyQualifiedName: String): TermSymbol =
      val (owner, nameStr) = findStaticOwnerAndName(fullyQualifiedName)
      val name = termName(nameStr)
      owner
        .getDecl(name)
        .getOrElse {
          throw MemberNotFoundException(owner, name)
        }
        .asTerm
    end findStaticTerm

    private def findStaticOwnerAndName(fullyQualifiedName: String): (DeclaringSymbol, String) =
      val path = fullyQualifiedName.split('.').toList
      (findStaticOwner(path.init), path.last)

    private def findStaticOwner(path: List[String]): DeclaringSymbol =
      def loop(owner: DeclaringSymbol, path: List[String]): DeclaringSymbol =
        path match
          case Nil =>
            owner
          case nameStr :: rest =>
            val name = termName(nameStr)
            owner.getDecl(name) match
              case Some(pkg: PackageSymbol) =>
                loop(pkg, rest)
              case Some(sym: TermSymbol) =>
                if sym.isModuleVal then loop(sym.moduleClass.get, rest)
                else throw InvalidProgramStructureException(s"$sym is not a static owner")
              case None =>
                throw MemberNotFoundException(owner, name)
      end loop

      if path.isEmpty then EmptyPackage
      else loop(RootPackage, path)
    end findStaticOwner

    private def splitPackageAndName(fullyQualifiedName: String): (PackageSymbol, String) =
      fullyQualifiedName.split('.').toList match
        case name :: Nil => (EmptyPackage, name)
        case path        => (findPackageFromRoot(PackageFullName(path.init.map(termName(_)))), path.last)

    private[tastyquery] def findPackageFromRootOrCreate(fullyQualifiedName: PackageFullName): PackageSymbol =
      fullyQualifiedName.path.foldLeft(RootPackage) { (owner, name) =>
        owner.getPackageDeclOrCreate(name)
      }
  }
}
