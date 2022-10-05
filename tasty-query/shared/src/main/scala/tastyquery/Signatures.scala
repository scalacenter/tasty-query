package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

object Signatures:
  enum ParamSig:
    case Term(typ: FullyQualifiedName)
    case TypeLen(len: Int)
  end ParamSig

  final case class Signature(paramsSig: List[ParamSig], resSig: FullyQualifiedName) derives CanEqual:
    def toDebugString = paramsSig.map {
      case ParamSig.Term(typ)    => typ.toDebugString
      case ParamSig.TypeLen(len) => len.toString
    }.mkString("(", ",", ")") + ":" + resSig.toDebugString

    override def toString = paramsSig.map {
      case ParamSig.Term(typ)    => typ.toString
      case ParamSig.TypeLen(len) => len.toString
    }.mkString("(", ",", ")") + ":" + resSig.toString
  end Signature

  object Signature {
    private[tastyquery] def fromMethodic(info: MethodicType, optCtorReturn: Option[ClassSymbol])(
      using Context
    ): Signature =
      def rec(info: Type, acc: List[ParamSig]): Signature =
        info match {
          case info: MethodType =>
            val erased = info.paramTypes.map(tpe => ParamSig.Term(ErasedTypeRef.erase(tpe).toSigFullName))
            rec(info.resultType, acc ::: erased)
          case info: PolyType =>
            rec(info.resultType, acc ::: ParamSig.TypeLen(info.paramTypeBounds.length) :: Nil)
          case tpe =>
            val retType = optCtorReturn.map(_.typeRef).getOrElse(tpe)
            Signature(acc, ErasedTypeRef.erase(retType).toSigFullName)
        }

      info match
        case ExprType(resType) => Signature(Nil, ErasedTypeRef.erase(resType).toSigFullName)
        case _                 => rec(info, Nil)
    end fromMethodic
  }
end Signatures
