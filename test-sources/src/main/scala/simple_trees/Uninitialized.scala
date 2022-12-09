package simple_trees

import scala.compiletime.uninitialized as renamedUninitialized

abstract class Uninitialized:
  var uninitializedRHS: Product = scala.compiletime.uninitialized
  var renamedUninitializedRHS: String = renamedUninitialized
  var wildcardRHS: Int = _

  var abstractVar: Int // confidence check: an abstract var is marked Deferred
end Uninitialized
