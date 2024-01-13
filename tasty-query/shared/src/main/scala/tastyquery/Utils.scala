package tastyquery

import scala.annotation.targetName

import java.util.concurrent.atomic.AtomicReference

private[tastyquery] object Utils:
  opaque type Memo[A] = AtomicReference[A]

  opaque type SingleAssign[A] = A | Null

  // Memo

  inline def uninitializedMemo[A]: Memo[A] = new AtomicReference[A]()

  extension [A](memo: Memo[A])
    @targetName("isMemoInitialized")
    def isInitialized: Boolean = memo.get() != null

  /** A memoized computation `computed`, stored in `memo` using the `store` setter. */
  inline def memoized[A](memo: Memo[A])(inline compute: => A): A =
    val existing = memo.get()
    if existing != null then existing
    else
      // Extracted in a separate def for good jitting of the code calling `memoized`
      def computeAndStore(): A =
        val computed = compute
        if memo.compareAndSet(null, computed) then computed
        else memo.get().nn
      computeAndStore()
  end memoized

  inline def memoized2[A](memo: Memo[A])(inline compute: => A)(inline afterCompute: A => Unit): A =
    val existing = memo.get()
    if existing != null then existing
    else
      // Extracted in a separate def for good jitting of the code calling `memoized2`
      def computeAndStore(): A =
        val computed = compute
        if memo.compareAndSet(null, computed) then
          afterCompute(computed)
          computed
        else
          // We wasted the computation; use the stored value so that only once instance survives for the GC
          memo.get().nn
      computeAndStore()
  end memoized2

  inline def initializeMemo[A](memo: Memo[A], value: A): Unit =
    memo.compareAndSet(null, value)

  inline def assignOnceMemo[A](existing: Memo[A], value: A)(inline msgIfAlreadyAssigned: => String): Unit =
    if !existing.compareAndSet(null, value) then throw IllegalStateException(msgIfAlreadyAssigned)

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
