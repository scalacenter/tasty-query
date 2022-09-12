package tastyquery

import tastyquery.Contexts.*
import tastyquery.ast.Flags.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.*

final class Definitions private[tastyquery] (
  ctx: Context,
  rootPackage: PackageClassSymbol,
  emptyPackage: PackageClassSymbol
):
  private given Context = ctx

  val RootPackage = rootPackage
  val EmptyPackage = emptyPackage

  val scalaPackage = ctx.createPackageSymbolIfNew(nme.scalaPackageName, RootPackage)
  val javaLangPackage = ctx.createPackageSymbolIfNew(nme.javalangPackageName, RootPackage)

  private def markInitialised(cls: ClassSymbol): cls.type =
    cls.initialised = true
    cls

  val AnyClass = markInitialised(ctx.createClassSymbol(typeName("Any"), scalaPackage))

  val NullClass = markInitialised(ctx.createClassSymbol(typeName("Null"), scalaPackage))

  val NothingClass = markInitialised(ctx.createClassSymbol(typeName("Nothing"), scalaPackage))

  val NothingAnyBounds = RealTypeBounds(NothingClass.typeRef, AnyClass.typeRef)

  locally {
    val andOrParamNames = List(typeName("A"), typeName("B"))

    val andTypeAlias = ctx.createSymbol(typeName("&"), scalaPackage)
    andTypeAlias.withFlags(EmptyFlagSet)
    andTypeAlias.withDeclaredType(
      PolyType(andOrParamNames)(
        pt => List(NothingAnyBounds, NothingAnyBounds),
        pt => AndType(pt.paramRefs(0), pt.paramRefs(1))
      )
    )

    val orTypeAlias = ctx.createSymbol(typeName("|"), scalaPackage)
    orTypeAlias.withFlags(EmptyFlagSet)
    orTypeAlias.withDeclaredType(
      PolyType(andOrParamNames)(
        pt => List(NothingAnyBounds, NothingAnyBounds),
        pt => OrType(pt.paramRefs(0), pt.paramRefs(1))
      )
    )
  }

end Definitions
