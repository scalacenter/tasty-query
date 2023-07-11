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

    private[tastyquery] def paramsCorrespond(that: Signature): Boolean =
      this.paramsSig == that.paramsSig
  end Signature

  object Signature {
    private[tastyquery] def fromType(
      info: TypeOrMethodic,
      language: SourceLanguage,
      optCtorReturn: Option[ClassSymbol]
    )(using Context): Signature =
      def rec(info: TypeOrMethodic, acc: List[ParamSig]): Signature =
        info match {
          case info: MethodType =>
            val erased = info.paramTypes.map(tpe => ParamSig.Term(ErasedTypeRef.erase(tpe, language).toSigFullName))
            rec(info.resultType, acc ::: erased)
          case info: PolyType =>
            rec(info.resultType, acc ::: ParamSig.TypeLen(info.paramTypeBounds.length) :: Nil)
          case tpe: Type =>
            val retType = optCtorReturn.map(_.localRef).getOrElse(tpe)
            Signature(acc, ErasedTypeRef.erase(retType, language).toSigFullName)
        }

      rec(info, Nil)
    end fromType
  }
end Signatures
