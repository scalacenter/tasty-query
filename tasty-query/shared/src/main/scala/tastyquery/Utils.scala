package tastyquery

import scala.annotation.targetName

private[tastyquery] object Utils:
  opaque type Memo[A] = A | Null

  opaque type SingleAssign[A] = A | Null

  // Memo

  inline def uninitializedMemo[A]: Memo[A] = null

  extension [A](memo: Memo[A])
    @targetName("isMemoInitialized")
    def isInitialized: Boolean = memo != null

  /** A memoized computation `computed`, stored in `memo` using the `store` setter. */
  inline def memoized[A](memo: Memo[A], inline store: Memo[A] => Unit)(inline compute: => A): A =
    if memo != null then memo
    else
      // Extracted in a separate def for good jitting of the code calling `memoized`
      def computeAndStore(): A =
        val computed = compute
        store(computed)
        computed
      computeAndStore()
  end memoized

  inline def memoized2[A](memo: Memo[A], inline store: Memo[A] => Unit)(
    inline compute: => A
  )(inline afterCompute: A => Unit): A =
    if memo != null then memo
    else
      // Extracted in a separate def for good jitting of the code calling `memoized2`
      def computeAndStore(): A =
        val computed = compute
        store(computed)
        afterCompute(computed)
        computed
      computeAndStore()
  end memoized2

  inline def initializeMemo[A](inline store: Memo[A] => Unit, value: A): Unit =
    store(value)

  inline def assignOnceMemo[A](existing: Memo[A], inline assign: Memo[A] => Unit, value: A)(
    inline msgIfAlreadyAssigned: => String
  ): Unit =
    if existing != null then throw IllegalStateException(msgIfAlreadyAssigned)
    assign(value)

  // SingleAssign

  inline def uninitializedSingleAssign[A]: SingleAssign[A] = null

  extension [A](singleAssign: SingleAssign[A])
    @targetName("isSingleAssignInitialized")
    def isInitialized: Boolean = singleAssign != null

  inline def assignOnce[A](existing: SingleAssign[A], inline assign: SingleAssign[A] => Unit, value: A)(
    inline msgIfAlreadyAssigned: => String
  ): Unit =
    // Methods calling `assignOnce` are not in fast paths, so no need to extract the exception in a local def
    if existing != null then throw IllegalStateException(msgIfAlreadyAssigned)
    assign(value)

  inline def overwriteSingleAssign[A](inline assign: SingleAssign[A] => Unit, value: A): Unit =
    assign(value)

  inline def getAssignedOnce[A](value: SingleAssign[A])(inline msgIfNotAssignedYet: => String): A =
    if value != null then value
    else
      // Extracted in a separate def for good jitting of the code calling `getAssignedOnce`
      def notAssignedYet(): Nothing =
        throw IllegalStateException(msgIfNotAssignedYet)
      notAssignedYet()
end Utils
