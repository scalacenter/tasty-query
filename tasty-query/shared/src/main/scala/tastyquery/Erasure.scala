package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.Types.ErasedTypeRef.*

private[tastyquery] object Erasure:
  // TODO: improve this to match dotty:
  // - use correct type erasure algorithm from Scala 3, with specialisations
  //   for Java types and Scala 2 types (i.e. varargs, value-classes)

  def erase(tpe: Type)(using Context): ErasedTypeRef =
    tpe match
      case _: ExprType => ClassRef(defn.Function0Class)
      case _           => finishErase(preErase(tpe))
  end erase

  /** First pass of erasure, where some special types are preserved as is.
    *
    * In particular, `Any` is preserved as `Any`, instead of becoming
    * `java.lang.Object`.
    */
  private def preErase(tpe: Type)(using Context): ErasedTypeRef =
    def arrayOfBounds(bounds: TypeBounds): ErasedTypeRef =
      preErase(bounds.high) match
        case ClassRef(cls) if cls == defn.AnyClass || cls == defn.AnyValClass =>
          ClassRef(defn.ObjectClass)
        case typeRef =>
          typeRef.arrayOf()

    def arrayOf(tpe: Type): ErasedTypeRef = tpe match
      case tpe: AppliedType =>
        if tpe.tycon.isRef(defn.ArrayClass) then
          val List(targ) = tpe.args: @unchecked
          arrayOf(targ).arrayOf()
        else arrayOf(tpe.tycon)
      case tpe: TypeRef =>
        tpe.symbol match
          case cls: ClassSymbol     => ClassRef(cls).arrayOf()
          case sym: TypeParamSymbol => arrayOfBounds(sym.bounds)
          case sym: TypeMemberSymbol =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)          => arrayOf(alias)
              case TypeMemberDefinition.AbstractType(bounds)      => arrayOfBounds(bounds)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => arrayOf(alias)
      case tpe: TypeParamRef       => arrayOfBounds(tpe.bounds)
      case tpe: WildcardTypeBounds => arrayOfBounds(tpe.bounds)
      case _ =>
        preErase(tpe).arrayOf()
    end arrayOf

    tpe.widen match
      case tpe: AppliedType =>
        if tpe.tycon.isRef(defn.ArrayClass) then
          val List(targ) = tpe.args: @unchecked
          arrayOf(targ)
        else
          tpe.tycon match
            case tycon: TypeRef if tycon.symbol.isClass =>
              // Fast path
              ClassRef(tycon.symbol.asClass)
            case _ =>
              preErase(tpe.translucentSuperType)
      case tpe: TypeRef =>
        tpe.symbol match
          case cls: ClassSymbol =>
            ClassRef(cls)
          case sym: TypeParamSymbol =>
            preErase(sym.upperBound)
          case sym: TypeMemberSymbol =>
            sym.typeDef match
              case TypeMemberDefinition.TypeAlias(alias)          => preErase(alias)
              case TypeMemberDefinition.AbstractType(bounds)      => preErase(bounds.high)
              case TypeMemberDefinition.OpaqueTypeAlias(_, alias) => preErase(alias)
      case tpe: TypeParamRef =>
        preErase(tpe.bounds.high)
      case tpe: WildcardTypeBounds =>
        preErase(tpe.bounds.high)
      case tpe =>
        throw UnsupportedOperationException(s"Cannot erase $tpe")
  end preErase

  private def finishErase(typeRef: ErasedTypeRef)(using Context): ErasedTypeRef =
    def valueClass(cls: ClassSymbol): ErasedTypeRef =
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      val List(Left(List(paramRef))) = ctor.paramRefss.dropWhile(_.isRight): @unchecked
      val paramType = paramRef.underlying
      erase(paramType)

    typeRef match
      case ClassRef(cls) =>
        if cls == defn.AnyValClass then ClassRef(defn.ObjectClass)
        else if cls.isDerivedValueClass then valueClass(cls)
        else cls.specialErasure.fold(typeRef)(f => f())
      case ArrayTypeRef(_, _) =>
        typeRef
  end finishErase
end Erasure
