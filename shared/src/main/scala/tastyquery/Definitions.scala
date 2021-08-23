package tastyquery

import tastyquery.ast.Names.{RootName, EmptyPackageName}
import tastyquery.ast.Symbols.PackageClassSymbol

class Definitions {
  val RootPackage  = PackageClassSymbol(RootName, null)
  val EmptyPackage = PackageClassSymbol(EmptyPackageName, RootPackage)
}
