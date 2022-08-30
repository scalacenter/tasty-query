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

  case object obj

  val RootPkg: PackageDeclPath = Nil
  val EmptyPkg: PackageDeclPath = nme.EmptyPackageName :: Nil

  extension (pkg: SimpleName)
    @targetName("selectPackage") def /(pkg1: SimpleName): PackageDeclPath = pkg :: pkg1 :: Nil
    @targetName("selectTopLevel") def /(cls: TypeName): TopLevelClassDeclPath = pkg :: cls :: Nil
    @targetName("selectModule") def /(asObj: obj.type): TopLevelDeclPath = pkg :: Nil

  extension (pkgs: PackageDeclPath)
    @targetName("selectPackage") def /(pkg: SimpleName): PackageDeclPath = pkgs :+ pkg
    @targetName("selectTopLevel") def /(cls: TypeName): TopLevelClassDeclPath = pkgs :+ cls
    @targetName("selectModule") def /(asObj: obj.type): TopLevelDeclPath = pkgs // no need to convert

  extension (cls: TopLevelDeclPath)
    /** the binary name of the class root for this declaration */
    def rootClassName: String = cls.show

  extension (cls: TopLevelClassDeclPath)
    // currently we have not set up member selection from object values, only the object class itself
    @targetName("selectMember") def /(x: Name): MemberDeclPath = cls :+ x
    @targetName("selectCompanion") def /(companion: obj.type): TopLevelClassDeclPath = cls.convertAsObject

  extension (member: MemberDeclPath)
    @targetName("selectMemberFromMember") def /(x: Name): MemberDeclPath = member :+ x
    @targetName("selectMemberAsModule") def /(companionOrSelf: obj.type): MemberDeclPath = member.convertAsObject

  extension (path: DeclarationPath)
    def toNameList: List[Name] = path
    def name: Name = if path.isEmpty then nme.RootName else path.last
    def root: Name = path.head
    def foldRemainder[T](whenEmpty: => T)(follow: DeclarationPath => T): T = path.tail match {
      case Nil => whenEmpty
      case xs  => follow(xs)
    }
    def show: String = path.mkString(".")
    def debug: String = toDebugString(path)

  extension [T <: DeclarationPath](path: T)
    private def convertAsObject: T =
      val pre :+ last = path: @unchecked
      last match
        case clsName: TypeName =>
          if clsName.wrapsObjectName then path // already an object
          else (pre :+ clsName.toTermName.withObjectSuffix.toTypeName).asInstanceOf[T] // select the companion object
        case _ => path

  extension (names: IterableOnce[Name]) def toDebugString: String = names.map(_.toDebugString).mkString(".")
