package tastyquery

import tastyquery.ast.Names.RootName
import tastyquery.ast.Symbols.{NoSymbol, PackageClassSymbol}

class Definitions {
  val RootPackage = PackageClassSymbol(RootName, NoSymbol)
}
