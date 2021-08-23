package tastyquery

import tastyquery.ast.Names.RootName
import tastyquery.ast.Symbols.PackageClassSymbol

class Definitions {
  val RootPackage = PackageClassSymbol(RootName, null)
}
