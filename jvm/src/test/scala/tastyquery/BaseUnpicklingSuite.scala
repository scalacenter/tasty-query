package tastyquery

import tastyquery.Contexts
import tastyquery.Contexts.{defn, BaseContext}
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.Type
import tastyquery.ast.Names.{TypeName, SuffixedName, nme}
import tastyquery.reader.TastyUnpickler

import tastyquery.testutil.{testPlatform, TestPlatform}

import java.nio.file.{Files, Paths}
import tastyquery.ast.Names.Name

import BaseUnpicklingSuite.Decls.*
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}
import tastyquery.ast.Names.SimpleName
import dotty.tools.tasty.TastyFormat.NameTags
import scala.annotation.targetName
import tastyquery.ast.Symbols.ClassSymbol

abstract class BaseUnpicklingSuite(withClasses: Boolean, withStdLib: Boolean, allowDeps: Boolean)
    extends munit.FunSuite { outer =>
  given TestPlatform = tastyquery.testutil.jdk.JavaTestPlatform // TODO: make abstract so we can test scala.js

  lazy val testClasspath = testPlatform.loadClasspath(includeClasses = withClasses, includeStdLib = withStdLib)

  def getUnpicklingContext(path: TopLevelDeclPath, extraClasspath: TopLevelDeclPath*): BaseContext = {
    val (base, _) = findTopLevelClass(path)(extraClasspath*)
    base
  }

  def unpickle(path: TopLevelDeclPath): Tree = {
    val (base, classRoot) = findTopLevelClass(path)()
    val tree = base.classloader.topLevelTasty(classRoot)(using base) match
      case Some(trees) => trees.head
      case _           => fail(s"Missing tasty for ${path.fullClassName}, $classRoot")
    tree
  }

  class MissingTopLevelDecl(path: TopLevelDeclPath)
      extends Exception(s"Missing top-level declaration ${path.fullClassName}, perhaps it is not on the classpath?")

  private def findTopLevelClass(path: TopLevelDeclPath)(extras: TopLevelDeclPath*): (BaseContext, ClassSymbol) = {
    val topLevelClass = path.fullClassName
    val classpath =
      if allowDeps then testClasspath
      else testClasspath.withFilter(topLevelClass :: extras.map(_.fullClassName).toList)
    val base: BaseContext = Contexts.init(classpath)
    val classRoot = base.getClassIfDefined(topLevelClass) match
      case Some(cls) => cls
      case _         => throw MissingTopLevelDecl(path)
    if !base.classloader.scanClass(classRoot)(using base) then fail(s"could not initialise $topLevelClass, $classRoot")
    (base, classRoot)
  }

  /* TODO Currently this only resolves symbols that have already been loaded,
   * but the intent is that it will load symbols when required.
   */
  def resolve(path: DeclarationPath)(using BaseContext): Symbol =
    followPathImpl(defn.RootPackage, path).fold(fail(_), identity)

  def assertSymbolExistsAndIsLoaded(path: DeclarationPath)(implicit ctx: BaseContext): Unit =
    followPathImpl(defn.RootPackage, path).fold(fail(_), _ => ())

  def assertSymbolNotExistsOrNotLoadedYet(path: DeclarationPath)(implicit ctx: BaseContext): Unit =
    def unexpected(sym: Symbol) = fail(s"expected no symbol, but found ${sym.toDebugString}")
    followPathImpl(defn.RootPackage, path).fold(_ => (), unexpected)

  private def followPathImpl(root: DeclaringSymbol, path: DeclarationPath): Either[String, Symbol] = {
    def follow(selected: Symbol)(remainder: DeclarationPath): Either[String, Symbol] = selected match {
      case nextDecl: DeclaringSymbol =>
        followPathImpl(nextDecl, remainder)
      case someSym =>
        val symDebug = clue(someSym).toDebugString
        Left(s"Unexpected non-declaring symbol $symDebug with remaining path ${remainder.debug}")
    }
    for
      selected <- select(root, path.root)
      sym <- path.foldRemainder(Right(selected))(follow(selected))
    yield sym
  }

  private def select(root: DeclaringSymbol, next: Name): Either[String, Symbol] = {
    val sel = (root, next) match {
      case (p: PackageClassSymbol, s: SimpleName) if p.name != nme.RootName =>
        p.name.toTermName.select(s)
      case _ => next
    }
    root.getDecl(sel) match {
      case Some(someSym) => Right(someSym)
      case _ => Left(s"No declaration for ${next.toDebugString} [${sel.toDebugString}] in ${root.toDebugString}")
    }
  }

  extension (sc: StringContext)
    def name(args: Any*): SimpleName =
      SimpleName(sc.parts.mkString)
    def tname(args: Any*): TypeName =
      TypeName(SimpleName(sc.parts.mkString))
    def objclass(args: Any*): TypeName =
      TypeName(SuffixedName(NameTags.OBJECTCLASS, SimpleName(sc.parts.mkString)))
}

object BaseUnpicklingSuite {
  object Decls {

    opaque type DeclarationPath = List[Name] // Min 1 element
    opaque type PackageDeclPath <: DeclarationPath = List[Name] // packages
    opaque type TopLevelDeclPath <: DeclarationPath = List[Name] // top level classes
    opaque type MemberDeclPath <: DeclarationPath = List[Name] // local classes / values

    extension (pkg: SimpleName) {
      @targetName("selectPackage") def /(pkg1: SimpleName): PackageDeclPath = pkg :: pkg1 :: Nil
      @targetName("selectTopLevel") def /(cls: TypeName): TopLevelDeclPath = pkg :: cls :: Nil
      def singleton: PackageDeclPath = pkg :: Nil
    }
    extension (cls: TypeName) {
      def singleton: TopLevelDeclPath = cls :: Nil
    }
    extension (pkgs: PackageDeclPath) {
      @targetName("selectPackage") def /(pkg: SimpleName): PackageDeclPath = pkgs :+ pkg
      @targetName("selectTopLevel") def /(cls: TypeName): TopLevelDeclPath = pkgs :+ cls
    }
    extension (cls: TopLevelDeclPath) {
      @targetName("selectMember") def /(x: Name): MemberDeclPath = cls :+ x
      def fullClassName: String = cls.show
    }
    extension (member: MemberDeclPath) {
      @targetName("selectMemberFromMember") def /(x: Name): MemberDeclPath = member :+ x
    }
    extension (path: DeclarationPath) {
      def root: Name = path.head
      def foldRemainder[T](whenEmpty: => T)(follow: DeclarationPath => T): T = path.tail match {
        case Nil => whenEmpty
        case xs  => follow(xs)
      }
      def show: String = path.mkString(".")
      def debug: String = BaseUnpicklingSuite.toDebugString(path)
    }
  }

  extension (names: IterableOnce[Name]) {
    def toDebugString: String = names.map(_.toDebugString).mkString(".")
  }
}
