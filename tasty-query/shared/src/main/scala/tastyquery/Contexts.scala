package tastyquery

import scala.annotation.tailrec

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
  transparent inline def ctx(using ctx: Context): Context = ctx

  /** Standard definitions of symbols and types. */
  transparent inline def defn(using ctx: Context): ctx.defn.type = ctx.defn

  /** Creates a new [[Context]] for the given [[Classpaths.Classpath]]. */
  def init(classpath: Classpath): Context =
    val classloader = Loader(classpath)
    val ctx = new Context(classloader)
    classloader.initPackages()(using ctx)
    ctx

  /** Has the root been initialised already? Does not force, but returns true if at least one root was entered */
  private[tastyquery] def initialisedRoot(root: Loader.Root): Boolean =
    root.pkg.getDeclInternal(root.rootName).isDefined // module value
      || root.pkg.getDeclInternal(root.rootName.toTypeName).isDefined // class value

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
  final class Context private[Contexts] (private[tastyquery] val classloader: Loader) {
    private given Context = this

    private val (RootPackage @ _, EmptyPackage @ _) = PackageSymbol.createRoots()

    val defn: Definitions = Definitions(this: @unchecked, RootPackage, EmptyPackage)

    /** basically an internal method for loading Java classes embedded in Java descriptors */
    private[tastyquery] def getClassFromBinaryName(binaryName: String): Either[MemberNotFoundException, ClassSymbol] =
      getRootIfDefined(binaryName).flatMap { root =>
        root.pkg
          .getDecl(root.rootName.toTypeName)
          .collect { case cls: ClassSymbol => cls }
          .toRight(
            MemberNotFoundException(
              root.pkg,
              root.rootName,
              s"no root ${root.rootName} in ${root.pkg.fullName}; perhaps it is not on the classpath"
            )
          )
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
    private def getRootIfDefined(binaryName: String): Either[MemberNotFoundException, Loader.Root] =
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
        val pkg = PackageRef(packageName).symbol
        pkg
          .possibleRoot(rootName)
          .toRight(MemberNotFoundException(pkg, rootName, s"no root $rootName exists in package $packageName"))
      catch
        case e: MemberNotFoundException =>
          Left(MemberNotFoundException(e.prefix, e.name, s"unknown package $packageName"))

    def findPackageFromRoot(fullyQualifiedName: FullyQualifiedName): PackageSymbol =
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
      // strip initial `_root_` if present, which is how user signals qualified from root names.
      val path0 = fullyQualifiedName.path match
        case nme.RootPackageName :: path => path
        case path                        => path
      rec(RootPackage, path0)
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

    private[tastyquery] def createPackageSymbolIfNew(name: SimpleName, owner: PackageSymbol): PackageSymbol =
      assert(owner != EmptyPackage, s"Trying to create a subpackage $name of $owner")
      owner.getPackageDeclInternal(name) match {
        case Some(pkg) => pkg
        case None      => PackageSymbol.create(name, owner)
      }

    private[tastyquery] def createPackageSymbolIfNew(fullyQualifiedName: FullyQualifiedName): PackageSymbol =
      fullyQualifiedName.path.foldLeft(RootPackage) { (owner, name) =>
        createPackageSymbolIfNew(name.asSimpleName, owner)
      }
  }
}
