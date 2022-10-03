package tastyquery

import tastyquery.Contexts.*
import tastyquery.ast.Flags.*
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Types.*

final class Definitions private[tastyquery] (ctx: Context, rootPackage: PackageSymbol, emptyPackage: PackageSymbol):
  private given Context = ctx

  // Core packages

  val RootPackage = rootPackage
  val EmptyPackage = emptyPackage

  val scalaPackage = ctx.createPackageSymbolIfNew(nme.scalaPackageName, RootPackage)
  private val javaPackage = ctx.createPackageSymbolIfNew(nme.javaPackageName, RootPackage)
  val javaLangPackage = ctx.createPackageSymbolIfNew(nme.langPackageName, javaPackage)

  // Magic symbols that are not found on the classpath, but rather created by hand

  private def createSpecialClass(name: TypeName, parents: List[Type], flags: FlagSet): ClassSymbol =
    val cls = ClassSymbol.create(name, scalaPackage)
    cls.withTypeParams(Nil, Nil)
    cls.withParentsDirect(parents)
    cls.withFlags(flags)
    cls

  val AnyClass = createSpecialClass(typeName("Any"), Nil, Abstract)

  val NullClass = createSpecialClass(typeName("Null"), AnyClass.typeRef :: Nil, Abstract | Final)

  val NothingClass = createSpecialClass(typeName("Nothing"), AnyClass.typeRef :: Nil, Abstract | Final)

  val NothingAnyBounds = RealTypeBounds(NothingClass.typeRef, AnyClass.typeRef)

  locally {
    val andOrParamNames = List(typeName("A"), typeName("B"))

    val andTypeAlias = TypeMemberSymbol.create(typeName("&"), scalaPackage)
    andTypeAlias.withFlags(EmptyFlagSet)
    andTypeAlias.withDefinition(
      TypeMemberDefinition.TypeAlias(
        PolyType(andOrParamNames)(
          pt => List(NothingAnyBounds, NothingAnyBounds),
          pt => AndType(pt.paramRefs(0), pt.paramRefs(1))
        )
      )
    )

    val orTypeAlias = TypeMemberSymbol.create(typeName("|"), scalaPackage)
    orTypeAlias.withFlags(EmptyFlagSet)
    orTypeAlias.withDefinition(
      TypeMemberDefinition.TypeAlias(
        PolyType(andOrParamNames)(
          pt => List(NothingAnyBounds, NothingAnyBounds),
          pt => OrType(pt.paramRefs(0), pt.paramRefs(1))
        )
      )
    )

    val AnyRefAlias = TypeMemberSymbol.create(typeName("AnyRef"), scalaPackage)
    AnyRefAlias.withFlags(EmptyFlagSet)
    val ObjectType = TypeRef(javaLangPackage.packageRef, typeName("Object"))
    AnyRefAlias.withDefinition(TypeMemberDefinition.TypeAlias(ObjectType))
  }

  private def createSpecialPolyClass(
    name: TypeName,
    paramFlags: FlagSet,
    parentConstrs: Type => List[Type]
  ): ClassSymbol =
    val cls = ClassSymbol.create(name, scalaPackage)

    val tparam = ClassTypeParamSymbol.create(typeName("T"), cls)
    tparam.withFlags(ClassTypeParam)
    tparam.setBounds(NothingAnyBounds)

    cls.withTypeParams(tparam :: Nil, NothingAnyBounds :: Nil)
    cls.withFlags(EmptyFlagSet | Artifact)

    val parents = parentConstrs(TypeRef(NoPrefix, tparam))
    cls.withParentsDirect(parents)
    cls
  end createSpecialPolyClass

  val ByNameParamClass2x: ClassSymbol =
    createSpecialPolyClass(tpnme.ByNameParamClassMagic, Covariant, _ => List(AnyType))

  val RepeatedParamClass: ClassSymbol =
    createSpecialPolyClass(tpnme.RepeatedParamClassMagic, Covariant, tp => List(ObjectType, SeqTypeOf(tp)))

  // Derived symbols, found on the classpath

  extension (pkg: PackageSymbol)
    private def requiredClass(name: String): ClassSymbol = pkg.getDecl(typeName(name)).get.asClass

  private lazy val scalaCollectionPackage = scalaPackage.getPackageDecl(termName("collection")).get
  private lazy val scalaCollectionImmutablePackage =
    scalaCollectionPackage.getPackageDecl(termName("immutable")).get

  lazy val ObjectClass = javaLangPackage.requiredClass("Object")

  lazy val AnyValClass = scalaPackage.requiredClass("AnyVal")
  lazy val ArrayClass = scalaPackage.requiredClass("Array")
  lazy val SeqClass = scalaCollectionImmutablePackage.requiredClass("Seq")
  lazy val Function0Class = scalaPackage.requiredClass("Function0")

  lazy val IntClass = scalaPackage.requiredClass("Int")
  lazy val LongClass = scalaPackage.requiredClass("Long")
  lazy val FloatClass = scalaPackage.requiredClass("Float")
  lazy val DoubleClass = scalaPackage.requiredClass("Double")
  lazy val BooleanClass = scalaPackage.requiredClass("Boolean")
  lazy val ByteClass = scalaPackage.requiredClass("Byte")
  lazy val ShortClass = scalaPackage.requiredClass("Short")
  lazy val CharClass = scalaPackage.requiredClass("Char")
  lazy val UnitClass = scalaPackage.requiredClass("Unit")

  def isPrimitiveValueClass(sym: ClassSymbol): Boolean =
    sym == IntClass || sym == LongClass || sym == FloatClass || sym == DoubleClass ||
      sym == BooleanClass || sym == ByteClass || sym == ShortClass || sym == CharClass ||
      sym == UnitClass

end Definitions
