import tastyquery.Contexts
import tastyquery.Contexts.{FileContext, defn}
import tastyquery.ast.Trees.Tree
import tastyquery.ast.Types.Type
import tastyquery.reader.TastyUnpickler

import tastyquery.testutil.{testPlatform, TestPlatform}

import java.nio.file.{Files, Paths}
import tastyquery.ast.Names.Name

import BaseUnpicklingSuite.Decls.*
import tastyquery.ast.Symbols.{DeclaringSymbol, PackageClassSymbol, Symbol}
import tastyquery.ast.Names.SimpleName
import tastyquery.Contexts.BaseContext
import tastyquery.ast.Names.TypeName
import tastyquery.ast.Names.SuffixedName
import dotty.tools.tasty.TastyFormat.NameTags
import scala.annotation.targetName
import tastyquery.ast.Names

abstract class BaseUnpicklingSuite(val includeClasses: Boolean) extends munit.FunSuite { outer =>
  given TestPlatform = tastyquery.testutil.jdk.JavaTestPlatform // TODO: make abstract so we can test scala.js

  lazy val testClasspath = testPlatform.loadClasspath(includeClasses)

  def unpickleCtx(path: TopLevelDeclPath): FileContext = {
    val (ctx, _) = unpickleFull(path)
    ctx
  }

  def unpickle(path: TopLevelDeclPath): Tree = {
    val (_, tree) = unpickleFull(path)
    tree
  }

  def unpickleFull(path: TopLevelDeclPath): (FileContext, Tree) = {
    val base: BaseContext = Contexts.empty(testClasspath)
    val tasty = base.classloader.lookupTasty(path.fullClassName) match
      case Some(tasty) => tasty
      case _ =>
        fail(s"could not find TASTy for top level class ${path.fullClassName}, perhaps it is not on the classpath?")
    val ctx = base.withFile(tasty.debugPath)
    val unpickler = new TastyUnpickler(tasty.bytes)
    val tree = unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle(using ctx).head
    (ctx, tree)
  }

  def resolve(path: DeclarationPath)(implicit ctx: BaseContext): Symbol =
    followPath(defn.RootPackage, path)

  def absent(path: DeclarationPath)(implicit ctx: BaseContext): Unit =
    def unexpected(sym: Symbol) = fail(s"expected no symbol, but found ${sym.toDebugString}")
    followPathImpl(defn.RootPackage, path).fold(_ => (), unexpected)

  def followPath(root: DeclaringSymbol, path: DeclarationPath): Symbol =
    followPathImpl(root, path).fold(fail(_), identity)

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
      case (p: PackageClassSymbol, s: SimpleName) if p.name != tastyquery.ast.Names.RootName =>
        p.name.toTermName.select(s)
      case _ => next
    }
    root.getDecl(sel) match {
      case Some(someSym) => Right(someSym)
      case _             => Left(s"No declaration for ${next.toDebugString} in ${root.toDebugString}")
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
