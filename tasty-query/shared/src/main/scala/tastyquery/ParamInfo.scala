package tastyquery

import tastyquery.Contexts.*
import tastyquery.Variances.*

/** A common super trait of Symbol and LambdaParam.
  * Used to capture the attributes of type parameters which can be implemented as either.
  */
trait ParamInfo {

  /** The variance of the type parameter */
  def paramVariance(using Context): Variance
}

object ParamInfo {
  type TypeParamInfo = ParamInfo
}
