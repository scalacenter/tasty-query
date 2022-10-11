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
