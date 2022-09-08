package tastyquery.ast

import tastyquery.ast.Names.TypeName
import tastyquery.ast.Types.{PolyType, MethodType, ExprType, MethodicType, ErasedTypeRef, Type}
import tastyquery.Contexts.Context

abstract class ParamSig

case class TermSig(typ: TypeName) extends ParamSig

case class TypeLenSig(len: Int) extends ParamSig

case class Signature(paramsSig: List[ParamSig], resSig: TypeName) derives CanEqual:
  def toDebugString = paramsSig.map {
    case TermSig(typ)    => typ.toDebugString
    case TypeLenSig(len) => len.toString
  }.mkString("(", ",", ")") + ":" + resSig.toDebugString

  override def toString = paramsSig.map {
    case TermSig(typ)    => typ.toString
    case TypeLenSig(len) => len.toString
  }.mkString("(", ",", ")") + ":" + resSig.toString

object Signature {
  def fromMethodic(info: MethodicType)(using Context): Signature =
    def rec(info: Type, acc: List[ParamSig]): Signature =
      info match {
        case info: MethodType =>
          val erased = info.paramTypes.map((ErasedTypeRef.erase) andThen (TermSig(_)))
          rec(info.resultType, acc ::: erased)
        case PolyType(_, tbounds, res) =>
          rec(res, acc ::: TypeLenSig(tbounds.length) :: Nil)
        case tpe =>
          Signature(acc, ErasedTypeRef.erase(tpe))
      }

    info match
      case ExprType(resType) => Signature(Nil, ErasedTypeRef.erase(resType))
      case _                 => rec(info, Nil)
  end fromMethodic
}
