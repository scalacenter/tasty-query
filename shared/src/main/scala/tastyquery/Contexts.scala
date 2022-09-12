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
      val ctx = new Context(Definitions(), classloader)
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
  final class Context private[Contexts] (val defn: Definitions, val classloader: Loader) {
    private given Context = this

    /** basically an internal method for loading Java classes embedded in Java descriptors */
    private[tastyquery] def getClassFromBinaryName(binaryName: String): Either[SymResolutionProblem, ClassSymbol] =
      getRootIfDefined(binaryName).flatMap { root =>
        root.pkg
          .getDecl(root.rootName.toTypeName)
          .collect { case cls: ClassSymbol => cls }
          .toRight(SymbolLookupException(root.fullName, s"perhaps it is not on the classpath"))
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
          (nme.EmptyPackageName, rootName)
        else
          import scala.language.unsafeNulls
          val packageName = binaryName.substring(0, lastSep)
          val rootName = termName(binaryName.substring(lastSep + 1))
          (classloader.toPackageName(packageName), rootName)
      def fullName = packageName.toTermName.select(rootName)
      try
        val pkg = PackageRef(packageName).resolveToSymbol
        pkg.possibleRoot(rootName).toRight(SymbolLookupException(fullName, s"no root exists in package $packageName"))
      catch
        case e: SymResolutionProblem =>
          Left(SymbolLookupException(fullName, s"unknown package $packageName"))

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
      rec(defn.RootPackage, path)
    end findSymbolFromRoot

    def createClassSymbol(name: TypeName, owner: DeclaringSymbol): ClassSymbol =
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

      val AnyBounds = RealTypeBounds(NothingType, AnyType)
      val andOrParamNames = List(SimpleName("A").toTypeName, SimpleName("B").toTypeName)

      val andTypeAlias = createSymbol(typeName("&"), scalaPackage)
      andTypeAlias.withFlags(EmptyFlagSet)
      andTypeAlias.withDeclaredType(
        PolyType(andOrParamNames)(pt => List(AnyBounds, AnyBounds), pt => AndType(pt.paramRefs(0), pt.paramRefs(1)))
      )

      val orTypeAlias = createSymbol(typeName("|"), scalaPackage)
      orTypeAlias.withFlags(EmptyFlagSet)
      orTypeAlias.withDeclaredType(
        PolyType(andOrParamNames)(pt => List(AnyBounds, AnyBounds), pt => OrType(pt.paramRefs(0), pt.paramRefs(1)))
      )

      def fakeJavaLangClassIfNotFound(name: String): ClassSymbol =
        val tname = typeName(name)
        javaLangPackage.getDecl(tname) match
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
}
