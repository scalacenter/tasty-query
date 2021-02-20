package tastyquery.ast

import tastyquery.ast.Names.TypeName

abstract class ParamSig

case class TermSig(typ: TypeName) extends ParamSig

case class TypeLenSig(len: Int) extends ParamSig

case class Signature(paramsSig: List[ParamSig], resSig: TypeName)
