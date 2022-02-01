package tastyquery.reader.classfiles

import tastyquery.ast.Names.{SimpleName, TermName, EmptyPackageName, termName}

object Classpaths {

  /** Contains class data and tasty data. `name` is a Scala identifier */
  case class PackageData(name: SimpleName, classes: IArray[ClassData], tastys: IArray[TastyData])

  /** Contains class bytes. `simpleName` is a Scala identifier */
  case class ClassData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  /** Contains tasty bytes. `simpleName` is a Scala identifier */
  case class TastyData(simpleName: SimpleName, debugPath: String, bytes: IArray[Byte])

  sealed abstract class Classpath protected (val packages: IArray[PackageData]) {
    def loader: Loader = Loader(this)
  }

  object Classpath {
    case object Empty extends Classpath(IArray.empty)

    def from(packages: IArray[PackageData]): Classpath =
      if (packages.isEmpty) Empty
      else new Classpath(packages) {}
  }

  class Loader(val classpath: Classpath) {

    def lookupTasty(fullClassName: String): Option[TastyData] =
      def packageAndClass(fullClassName: String): (SimpleName, SimpleName) = {
        val lastSep = fullClassName.lastIndexOf('.')
        if (lastSep == -1) (EmptyPackageName, termName(fullClassName))
        else {
          import scala.language.unsafeNulls
          val packageName = termName(fullClassName.substring(0, lastSep))
          val className = termName(fullClassName.substring(lastSep + 1))
          (packageName, className)
        }
      }
      val (pkg, cls) = packageAndClass(fullClassName)
      classpath.packages.find(_.name == pkg) match {
        case Some(pkg) => pkg.tastys.find(_.simpleName == cls)
        case _         => None
      }
  }
}
