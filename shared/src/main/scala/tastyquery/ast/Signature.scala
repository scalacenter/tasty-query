package tastyquery.ast

import tastyquery.ast.Names.*
import tastyquery.ast.Types.*
import tastyquery.Contexts.Context
import tastyquery.ast.Symbols.ClassSymbol

abstract class ParamSig

case class TermSig(typ: FullyQualifiedName) extends ParamSig

case class TypeLenSig(len: Int) extends ParamSig

case class Signature(paramsSig: List[ParamSig], resSig: FullyQualifiedName) derives CanEqual:
  def toDebugString = paramsSig.map {
    case TermSig(typ)    => typ.toDebugString
    case TypeLenSig(len) => len.toString
  }.mkString("(", ",", ")") + ":" + resSig.toDebugString

  override def toString = paramsSig.map {
    case TermSig(typ)    => typ.toString
    case TypeLenSig(len) => len.toString
  }.mkString("(", ",", ")") + ":" + resSig.toString

object Signature {
  def fromMethodic(info: MethodicType, optCtorReturn: Option[ClassSymbol])(using Context): Signature =
    def rec(info: Type, acc: List[ParamSig]): Signature =
      info match {
        case info: MethodType =>
          val erased = info.paramTypes.map(tpe => TermSig(ErasedTypeRef.erase(tpe).toSigFullName))
          rec(info.resultType, acc ::: erased)
        case PolyType(_, tbounds, res) =>
          rec(res, acc ::: TypeLenSig(tbounds.length) :: Nil)
        case tpe =>
          val retType = optCtorReturn.map(_.erasedName).getOrElse(ErasedTypeRef.erase(tpe).toSigFullName)
          Signature(acc, retType)
      }

    info match
      case ExprType(resType) => Signature(Nil, ErasedTypeRef.erase(resType).toSigFullName)
      case _                 => rec(info, Nil)
  end fromMethodic
}
