package tastyquery

import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

object Exceptions:
  class InvalidProgramStructureException(msg: String, cause: Throwable | Null) extends Exception(msg, cause):
    def this(msg: String) = this(msg, null)

  final class CyclicReferenceException(kind: String)
      extends InvalidProgramStructureException(s"cyclic evaluation of $kind")

  final class NonMethodReferenceException(kind: String)
      extends InvalidProgramStructureException(s"reference to non method type in $kind")

  final class MemberNotFoundException(val prefix: Symbol | Type, val name: Name, msg: String)
      extends InvalidProgramStructureException(msg):
    def this(prefix: Symbol | Type, name: Name) =
      this(prefix, name, s"Member ${name.toDebugString} not found in $prefix")

  sealed abstract class UnpickleFormatException(msg: String, cause: Throwable | Null) extends Exception(msg, cause)

  final class ClassfileFormatException(msg: String, cause: Throwable | Null)
      extends UnpickleFormatException(msg, cause):
    def this(msg: String) = this(msg, null)

  final class Scala2PickleFormatException(msg: String, cause: Throwable | Null)
      extends UnpickleFormatException(msg, cause):
    def this(msg: String) = this(msg, null)

  final class TastyFormatException(msg: String, cause: Throwable | Null) extends UnpickleFormatException(msg, cause):
    def this(msg: String) = this(msg, null)
end Exceptions
