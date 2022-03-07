package tastyquery

import tastyquery.ast.Names.nme
import tastyquery.ast.Symbols.PackageClassSymbol

class Definitions {
  val RootPackage = PackageClassSymbol(nme.RootName, null)
  val EmptyPackage = PackageClassSymbol(nme.EmptyPackageName, RootPackage)
}
