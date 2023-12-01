package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.Types.ErasedTypeRef.*

object Signatures:
  enum ParamSig:
    case Term(typ: SignatureName)
    case TypeLen(len: Int)
  end ParamSig

  final case class Signature(paramsSig: List[ParamSig], resSig: SignatureName) derives CanEqual:
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
    private def sigName(tpe: Type, language: SourceLanguage, keepUnit: Boolean)(using Context): SignatureName =
      toSigName(Erasure.eraseForSigName(tpe, language, keepUnit))

    private[tastyquery] def toSigName(typeRef: ErasedTypeRef): SignatureName = typeRef match
      case ClassRef(cls) =>
        cls.signatureName

      case ArrayTypeRef(base, dimensions) =>
        val suffix = "[]" * dimensions
        val baseName = base.cls.signatureName
        val suffixedLast = baseName.items.last match
          case ObjectClassName(baseModuleName) =>
            baseModuleName.append(suffix).withObjectSuffix
          case last: SimpleName =>
            last.append(suffix)
        SignatureName(baseName.items.init :+ suffixedLast)
    end toSigName

    private[tastyquery] def fromType(
      info: TypeOrMethodic,
      language: SourceLanguage,
      optCtorReturn: Option[ClassSymbol]
    )(using Context): Signature =
      def rec(info: TypeOrMethodic, acc: List[ParamSig]): Signature =
        info match {
          case info: MethodType =>
            val paramSigs = info.paramTypes.map(tpe => ParamSig.Term(sigName(tpe, language, keepUnit = false)))
            rec(info.resultType, acc ::: paramSigs)
          case info: PolyType =>
            val typeLenSig = ParamSig.TypeLen(info.paramTypeBounds.length)
            rec(info.resultType, acc ::: typeLenSig :: Nil)
          case tpe: Type =>
            val retType = optCtorReturn.map(_.appliedRefInsideThis).getOrElse(tpe)
            val resSig = sigName(retType, language, keepUnit = true)
            Signature(acc, resSig)
        }

      rec(info, Nil)
    end fromType
  }
end Signatures
