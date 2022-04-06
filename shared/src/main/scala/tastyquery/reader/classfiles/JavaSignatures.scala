package tastyquery.reader.classfiles

import tastyquery.Contexts.{BaseContext, baseCtx}
import tastyquery.ast.Types
import tastyquery.ast.Types.*
import tastyquery.ast.Symbols.*

object JavaSignatures:

  def parseSignature(member: Symbol, signature: String): Type =
    sys.error(s"$member signature: $signature")
    Types.AnyType
