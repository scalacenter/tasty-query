package tastyquery

import scala.annotation.targetName

import dotty.tools.tasty.TastyFormat.NameTags

import tastyquery.Contexts.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*

/** Utilities to work with top-level paths to symbols. */
object Paths:
  opaque type DeclarationPath = List[Name] // Min 1 element
  opaque type PackageDeclPath <: DeclarationPath = List[Name] // packages
  opaque type TopLevelDeclPath <: DeclarationPath = List[Name] // top level objects/classes
  opaque type TopLevelClassDeclPath <: TopLevelDeclPath = List[Name] // top level classes
  opaque type MemberDeclPath <: DeclarationPath = List[Name] // local classes / values

  def resolve(path: DeclarationPath)(using Context): Symbol =
    summon[Context].findSymbolFromRoot(path.toNameList)

  extension (sc: StringContext)
    def name(args: Any*): SimpleName =
      SimpleName(sc.parts.mkString)
    def tname(args: Any*): TypeName =
      TypeName(SimpleName(sc.parts.mkString))
    def objclass(args: Any*): TypeName =
      TypeName(SuffixedName(NameTags.OBJECTCLASS, SimpleName(sc.parts.mkString)))

  val RootPkg: PackageDeclPath = Nil
  val EmptyPkg: PackageDeclPath = nme.EmptyPackageName :: Nil

  extension (pkg: SimpleName)
    @targetName("selectPackage") def /(pkg1: SimpleName): PackageDeclPath = pkg :: pkg1 :: Nil
    @targetName("selectTopLevel") def /(cls: TypeName): TopLevelClassDeclPath = pkg :: cls :: Nil

  extension (pkgs: PackageDeclPath)
    @targetName("selectPackage") def /(pkg: SimpleName): PackageDeclPath = pkgs :+ pkg
    @targetName("selectTopLevel") def /(cls: TypeName): TopLevelClassDeclPath = pkgs :+ cls
    def obj: TopLevelDeclPath = pkgs

  extension (cls: TopLevelDeclPath)
    /** the binary name of the class root for this declaration */
    def rootClassName: String = cls.show

  extension (cls: TopLevelClassDeclPath)
    // currently we have not set up member selection from object values, only the object class itself
    @targetName("selectMember") def /(x: Name): MemberDeclPath = cls :+ x

  extension (member: MemberDeclPath) @targetName("selectMemberFromMember") def /(x: Name): MemberDeclPath = member :+ x

  extension (path: DeclarationPath)
    def toNameList: List[Name] = path
    def root: Name = path.head
    def foldRemainder[T](whenEmpty: => T)(follow: DeclarationPath => T): T = path.tail match {
      case Nil => whenEmpty
      case xs  => follow(xs)
    }
    def show: String = path.mkString(".")
    def debug: String = toDebugString(path)

  extension (names: IterableOnce[Name]) def toDebugString: String = names.map(_.toDebugString).mkString(".")
