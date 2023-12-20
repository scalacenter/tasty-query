package tastyquery

private[tastyquery] object Utils:
  /** A memoized computation `computed`, stored in `memo` using the `store` setter. */
  inline def memoized[A](memo: A | Null, inline store: A => Unit)(inline compute: => A): A =
    if memo != null then memo
    else
      // Extracted in a separate def for good jitting of the code calling `memoized`
      def computeAndStore(): A =
        val computed = compute
        store(computed)
        computed
      computeAndStore()
  end memoized
end Utils
