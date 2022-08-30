package tastyquery

import tastyquery.ast.Names.nme
import tastyquery.ast.Symbols.PackageClassSymbolFactory

class Definitions:
  val (RootPackage @ _, EmptyPackage @ _) = PackageClassSymbolFactory.createRoots
