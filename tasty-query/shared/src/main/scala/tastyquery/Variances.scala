package tastyquery

import tastyquery.Flags.*

private[tastyquery] object Variances:
  opaque type Variance = FlagSet

  object Variance:
    /** Extracts the Variance from a FlagSet. */
    def fromFlags(flags: FlagSet): Variance =
      flags & VarianceFlags

  extension (variance: Variance)
    /** Is this covariant or bivariant? */
    def isCovariant: Boolean = variance.is(Covariant)

    /** Is this contravariant or bivariant? */
    def isContravariant: Boolean = variance.is(Contravariant)

    /** Flips between covariant and contravariant. */
    def flip: Variance =
      if variance == Covariant then Contravariant
      else if variance == Contravariant then Covariant
      else variance

    /** The sign of this variance, as a number -1, 0, +1.
      * Bivariant is mapped to 1, i.e., it is treated like Covariant.
      */
    def sign: Int =
      if variance.is(Covariant) then 1
      else if variance.is(Contravariant) then -1
      else 0
  end extension
end Variances
