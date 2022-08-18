package tastyquery.ast

import tastyquery.Contexts.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.*
import tastyquery.ast.TypeMaps.*

object Substituters:

  def subst(tp: Type, from: Binders, to: Binders)(using Context): Type =
    new SubstBindingMap(from, to).apply(tp)

  def subst(tp: Type | TypeBounds, from: Binders, to: Binders)(using Context): Type | TypeBounds =
    new SubstBindingMap(from, to).apply(tp)

  def substParams(tp: Type, from: Binders, to: List[Type])(using Context): Type =
    new SubstParamsMap(from, to).apply(tp)

  def substParams(tp: Type | TypeBounds, from: Binders, to: List[Type])(using Context): Type | TypeBounds =
    new SubstParamsMap(from, to).apply(tp)

  def subst(tp: Type, from: List[Symbol], to: List[Type])(using Context): Type =
    if from.isEmpty then tp
    else new SubstMap(from, to).apply(tp)

  def subst(bounds: TypeBounds, from: List[Symbol], to: List[Type])(using Context): TypeBounds =
    if from.isEmpty then bounds
    else new SubstMap(from, to).apply(bounds)

  final class SubstBindingMap(from: Binders, to: Binders)(using Context) extends DeepTypeMap:
    def apply(tp: Type): Type =
      tp match
        case tp: BoundType =>
          if (tp.binders eq from) tp.copyBoundType(to.asInstanceOf[tp.BindersType]) else tp
        case tp: NamedType =>
          if (tp.prefix `eq` NoPrefix) tp
          else tp.derivedSelect(apply(tp.prefix))
        case _: ThisType =>
          tp
        case tp: AppliedType =>
          tp.map(apply(_))
        case _ =>
          mapOver(tp)
    end apply
  end SubstBindingMap

  private final class SubstParamsMap(from: Binders, to: List[Type])(using Context) extends DeepTypeMap:
    def apply(tp: Type): Type =
      tp match
        case tp: ParamRef =>
          if (tp.binders == from) to(tp.paramNum) else tp
        case tp: NamedType =>
          if (tp.prefix `eq` NoPrefix) tp
          else tp.derivedSelect(apply(tp.prefix))
        case _: ThisType =>
          tp
        case tp: AppliedType =>
          tp.map(apply(_))
        case _ =>
          mapOver(tp)
    end apply
  end SubstParamsMap

  private final class SubstMap(from: List[Symbol], to: List[Type])(using Context) extends DeepTypeMap:
    def apply(tp: Type): Type =
      tp match
        case tp: NamedType =>
          if tp.prefix == NoPrefix then
            val sym = tp.symbol
            var fs = from
            var ts = to
            while fs.nonEmpty && ts.nonEmpty do
              if fs.head eq sym then return ts.head
              fs = fs.tail
              ts = ts.tail
            tp
          else tp.derivedSelect(this(tp.prefix))
        case _: ThisType | _: BoundType =>
          tp
        case _ =>
          mapOver(tp)
  end SubstMap

end Substituters
