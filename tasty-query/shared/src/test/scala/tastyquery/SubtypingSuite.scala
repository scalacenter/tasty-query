package tastyquery

import java.io.Serializable as JSerializable
import java.lang.{String as JString, Throwable as JThrowable}

import scala.collection.Seq as GSeq
import scala.collection.mutable
import scala.collection.immutable.{List as IList, Seq as ISeq}
import scala.util.NotGiven

import scala.Predef.String as PString

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import TestUtils.*

class SubtypingSuite extends UnrestrictedUnpicklingSuite:
  object EquivResult:
    def withRef[A, B](using A =:= B): Unit = ()

  object NeitherSubtypeResult:
    def withRef[A, B](using NotGiven[A <:< B], NotGiven[B <:< A]): Unit = ()

  object StrictSubtypeResult:
    def withRef[A, B](using A <:< B, NotGiven[B <:< A]): Unit = ()

  def assertSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    val sub = tp1.isSubtype(tp2)
    assert(sub, clues(tp1, tp2))

  def assertNotSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    val sub = tp1.isSubtype(tp2)
    assert(!sub, clues(tp1, tp2))

  def assertEquiv(tp1: Type, tp2: Type)(using Context): EquivResult.type =
    assertSubtype(tp1, tp2)
    assertSubtype(tp2, tp1)
    assert(clue(tp1).isSameType(clue(tp2)))
    EquivResult

  def assertNeitherSubtype(tp1: Type, tp2: Type)(using Context): NeitherSubtypeResult.type =
    assertNotSubtype(tp1, tp2)
    assertNotSubtype(tp2, tp1)
    assert(!clue(tp1.isSameType(clue(tp2))))
    NeitherSubtypeResult

  def assertStrictSubtype(tp1: Type, tp2: Type)(using Context): StrictSubtypeResult.type =
    assertSubtype(tp1, tp2)
    assertNotSubtype(tp2, tp1)
    assert(!clue(tp1.isSameType(clue(tp2))))
    StrictSubtypeResult

  extension (cls: ClassSymbol)
    /** A `TypeRef` for the given `cls` that is not `eq` to anything existing. */
    def newTypeRef(using Context): TypeRef =
      TypeRef(cls.typeRef.prefix, cls)

  def ProductClass(using Context): ClassSymbol =
    ctx.findTopLevelClass("scala.Product")

  def MatchErrorClass(using Context): ClassSymbol =
    ctx.findTopLevelClass("scala.MatchError")

  def ListClass(using Context): ClassSymbol =
    ctx.findTopLevelClass("scala.collection.immutable.List")

  def OptionClass(using Context): ClassSymbol =
    ctx.findTopLevelClass("scala.Option")

  def PredefModuleClass(using Context): ClassSymbol =
    ctx.findTopLevelModuleClass("scala.Predef")

  def PredefPrefix(using Context): Type =
    ctx.findStaticTerm("scala.Predef").staticRef

  def ScalaPackageObjectPrefix(using Context): Type =
    ctx.findStaticTerm("scala.package").staticRef

  def javaLangPrefix(using Context): Type =
    defn.javaLangPackage.packageRef

  def javaIOPrefix(using Context): Type =
    ctx.findPackage("java.io").packageRef

  def scalaPrefix(using Context): Type =
    defn.scalaPackage.packageRef

  def listOf(tpe: Type)(using Context): Type =
    ListClass.typeRef.appliedTo(tpe)

  def optionOf(tpe: Type)(using Context): Type =
    OptionClass.typeRef.appliedTo(tpe)

  def genSeqOf(tpe: Type)(using Context): Type =
    ctx.findTopLevelClass("scala.collection.Seq").typeRef.appliedTo(tpe)

  def mutableSeqOf(tpe: Type)(using Context): Type =
    ctx.findTopLevelClass("scala.collection.mutable.Seq").typeRef.appliedTo(tpe)

  def iarrayOf(tpe: Type)(using Context): Type =
    ctx.findStaticType("scala.IArray$package.IArray").staticRef.appliedTo(tpe)

  def findTypesFromTASTyNamed(name: String)(using Context): Type =
    ctx.findTopLevelClass("subtyping.TypesFromTASTy").findNonOverloadedDecl(termName(name)).declaredType

  def findTypesFromTASTyNamed(name: TypeName)(using Context): Type =
    ctx.findTopLevelClass("subtyping.TypesFromTASTy").findDecl(name).asInstanceOf[TypeMemberSymbol].aliasedType

  def thisTypeRefFromTASTy(name: TypeName)(using Context): TypeRef =
    ctx.findTopLevelClass("subtyping.TypesFromTASTy").thisType.select(name)

  testWithContext("same-monomorphic-class") {
    assertEquiv(defn.IntType, defn.IntClass.typeRef).withRef[Int, scala.Int]
    assertEquiv(defn.IntType, defn.IntClass.newTypeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanClass.typeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanClass.newTypeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanType).withRef[Int, Boolean]
    assertNeitherSubtype(defn.IntType, defn.ObjectType).withRef[Int, Object]

    assertEquiv(ProductClass.typeRef, ProductClass.newTypeRef).withRef[Product, Product]
    assertEquiv(MatchErrorClass.typeRef, MatchErrorClass.newTypeRef).withRef[MatchError, MatchError]
    assertNeitherSubtype(ProductClass.typeRef, MatchErrorClass.typeRef).withRef[Product, MatchError]
  }

  testWithContext("monomorphic-class-type-alias") {
    assertEquiv(defn.ObjectType, defn.AnyRefType).withRef[Object, AnyRef]

    assertEquiv(defn.StringType, PredefPrefix.select(tname"String")).withRef[JString, PString]
    assertNeitherSubtype(defn.StringType, ScalaPackageObjectPrefix.select(tname"Cloneable")).withRef[JString, Cloneable]

    assertEquiv(PredefPrefix.select(tname"String"), PredefPrefix.select(tname"String")).withRef[PString, PString]
    assertNeitherSubtype(PredefPrefix.select(tname"String"), ScalaPackageObjectPrefix.select(tname"Cloneable"))
      .withRef[PString, Cloneable]
  }

  testWithContext("anykind") {
    assertEquiv(defn.AnyKindType, defn.AnyKindClass.newTypeRef)

    assertStrictSubtype(defn.AnyType, defn.AnyKindType)
    assertStrictSubtype(defn.AnyRefType, defn.AnyKindType)
    assertStrictSubtype(defn.IntType, defn.AnyKindType)
    assertStrictSubtype(defn.StringType, defn.AnyKindType)
    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.AnyKindType)
    assertStrictSubtype(defn.ArrayTypeOf(defn.IntType), defn.AnyKindType)
    assertStrictSubtype(defn.SeqTypeOf(defn.IntType), defn.AnyKindType)
    assertStrictSubtype(defn.NullType, defn.AnyKindType)
    assertStrictSubtype(defn.NothingType, defn.AnyKindType)
    assertStrictSubtype(PredefModuleClass.typeRef, defn.AnyKindType)

    assertStrictSubtype(defn.UnappliedClassType, defn.AnyKindType)
    assertStrictSubtype(ctx.findStaticType("scala.IArray$package.IArray").staticRef, defn.AnyKindType)
  }

  testWithContext("any") {
    assertEquiv(defn.AnyType, defn.AnyClass.newTypeRef).withRef[Any, Any]

    assertStrictSubtype(defn.AnyRefType, defn.AnyType).withRef[AnyRef, Any]
    assertStrictSubtype(defn.IntType, defn.AnyType).withRef[Int, Any]
    assertStrictSubtype(defn.StringType, defn.AnyType).withRef[JString, Any]
    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.AnyType).withRef[PString, Any]
    assertStrictSubtype(defn.ArrayTypeOf(defn.IntType), defn.AnyType).withRef[Array[Int], Any]
    assertStrictSubtype(defn.SeqTypeOf(defn.IntType), defn.AnyType).withRef[ISeq[Int], Any]
    assertStrictSubtype(defn.NullType, defn.AnyType).withRef[Null, Any]
    assertStrictSubtype(defn.NothingType, defn.AnyType).withRef[Nothing, Any]
    assertStrictSubtype(PredefModuleClass.typeRef, defn.AnyType)

    assertNeitherSubtype(defn.UnappliedClassType, defn.AnyType)
    assertNeitherSubtype(ctx.findStaticType("scala.IArray$package.IArray").staticRef, defn.AnyType)
  }

  testWithContext("nothing") {
    assertEquiv(defn.NothingType, defn.NothingClass.newTypeRef).withRef[Nothing, Nothing]

    assertStrictSubtype(defn.NothingType, defn.AnyType).withRef[Nothing, Any]
    assertStrictSubtype(defn.NothingType, defn.AnyRefType).withRef[Nothing, AnyRef]
    assertStrictSubtype(defn.NothingType, defn.IntType).withRef[Nothing, Int]
    assertStrictSubtype(defn.NothingType, defn.StringType).withRef[Nothing, JString]
    assertStrictSubtype(defn.NothingType, PredefPrefix.select(tname"String")).withRef[Nothing, PString]
    assertStrictSubtype(defn.NothingType, defn.ArrayTypeOf(defn.IntType)).withRef[Nothing, Array[Int]]
    assertStrictSubtype(defn.NothingType, defn.SeqTypeOf(defn.IntType)).withRef[Nothing, ISeq[Int]]
    assertStrictSubtype(defn.NothingType, defn.NullType).withRef[Nothing, Null]
    assertStrictSubtype(defn.NothingType, PredefModuleClass.typeRef)
  }

  testWithContext("null") {
    assertEquiv(defn.NullType, defn.NullClass.newTypeRef).withRef[Null, Null]

    assertStrictSubtype(defn.NullType, defn.AnyType).withRef[Null, Any]

    // No withRef in this group because we implement sloppy Nulls but we compile this codebase with strict Nulls
    assertStrictSubtype(defn.NullType, defn.AnyRefType)
    assertStrictSubtype(defn.NullType, defn.StringType)
    assertStrictSubtype(defn.NullType, PredefPrefix.select(tname"String"))
    assertStrictSubtype(defn.NullType, defn.ArrayTypeOf(defn.IntType))
    assertStrictSubtype(defn.NullType, defn.SeqTypeOf(defn.IntType))

    assertNeitherSubtype(defn.NullType, defn.IntType).withRef[Null, Int]
    assertNeitherSubtype(defn.NullType, PredefModuleClass.typeRef)
  }

  testWithContext("subclasses") {
    assertStrictSubtype(defn.AnyValType, defn.AnyType).withRef[AnyVal, Any]
    assertStrictSubtype(defn.ObjectType, defn.AnyType).withRef[Object, Any]

    assertStrictSubtype(defn.IntType, defn.AnyType).withRef[Int, Any]
    assertStrictSubtype(defn.IntType, defn.AnyValType).withRef[Int, AnyVal]

    assertStrictSubtype(defn.StringType, defn.ObjectType).withRef[JString, Object]

    assertStrictSubtype(defn.StringType, javaIOPrefix.select(tname"Serializable")).withRef[JString, JSerializable]

    assertStrictSubtype(MatchErrorClass.typeRef, defn.ThrowableType).withRef[MatchError, JThrowable]
  }

  testWithContext("subclasses-with-type-aliases") {
    assertStrictSubtype(defn.AnyRefType, defn.AnyType).withRef[AnyRef, Any]
    assertStrictSubtype(defn.StringType, defn.AnyRefType).withRef[JString, AnyRef]

    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.ObjectType).withRef[PString, Object]
    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.AnyRefType).withRef[PString, AnyRef]

    assertStrictSubtype(defn.StringType, ScalaPackageObjectPrefix.select(tname"Serializable"))
      .withRef[JString, Serializable]
    assertStrictSubtype(PredefPrefix.select(tname"String"), ScalaPackageObjectPrefix.select(tname"Serializable"))
      .withRef[PString, Serializable]

    assertStrictSubtype(MatchErrorClass.typeRef, ScalaPackageObjectPrefix.select(tname"Throwable"))
      .withRef[MatchError, Throwable]
  }

  testWithContext("same-polymorphic-class") {
    assertEquiv(listOf(defn.IntType), listOf(defn.IntType)).withRef[IList[Int], IList[Int]]
    assertNeitherSubtype(listOf(defn.IntType), listOf(defn.StringType)).withRef[IList[Int], IList[JString]]

    assertEquiv(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.IntType)).withRef[Array[Int], Array[Int]]
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.StringType))
      .withRef[Array[Int], Array[JString]]

    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), listOf(defn.IntType)).withRef[Array[Int], IList[Int]]
  }

  testWithContext("same-polymorphic-class-variance") {
    assertStrictSubtype(listOf(defn.IntType), listOf(defn.AnyValType)).withRef[IList[Int], IList[AnyVal]]

    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.AnyValType))
      .withRef[Array[Int], Array[AnyVal]]
  }

  testWithContext("polymorphic-type-alias") {
    assertEquiv(ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType), listOf(defn.IntType))
      .withRef[List[Int], IList[Int]]

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.ArrayTypeOf(defn.IntType)
    ).withRef[List[Int], Array[Int]]

    val listOfInt = listOf(defn.IntType)
    assertEquiv(findTypesFromTASTyNamed("listFullyQualified"), listOfInt).withRef[IList[Int], IList[Int]]
    assertEquiv(findTypesFromTASTyNamed("listDefaultImport"), listOfInt).withRef[List[Int], IList[Int]]
    assertEquiv(findTypesFromTASTyNamed("listPackageAlias"), listOfInt).withRef[scala.List[Int], IList[Int]]
  }

  testWithContext("polymorphic-subclasses") {
    assertStrictSubtype(listOf(defn.IntType), defn.SeqTypeOf(defn.IntType)).withRef[IList[Int], ISeq[Int]]
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.SeqTypeOf(defn.IntType)).withRef[Array[Int], ISeq[Int]]
  }

  testWithContext("polymorphic-type-alias-subclasses") {
    assertStrictSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.IntType)
    ).withRef[List[Int], ISeq[Int]]
    assertStrictSubtype(listOf(defn.StringType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.StringType))
      .withRef[IList[JString], Seq[JString]]

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      mutableSeqOf(defn.IntType)
    ).withRef[List[Int], mutable.Seq[Int]]
    assertNeitherSubtype(
      mutableSeqOf(defn.StringType),
      ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.StringType)
    ).withRef[mutable.Seq[JString], Seq[JString]]
  }

  testWithContext("polymorphic-subclasses-variance") {
    assertStrictSubtype(listOf(defn.IntType), defn.SeqTypeOf(defn.AnyValType)).withRef[IList[Int], ISeq[AnyVal]]
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.SeqTypeOf(defn.IntType)).withRef[Array[Int], ISeq[Int]]

    assertStrictSubtype(listOf(defn.IntType), genSeqOf(defn.AnyValType)).withRef[IList[Int], GSeq[AnyVal]]
    assertNeitherSubtype(listOf(defn.IntType), mutableSeqOf(defn.AnyValType)).withRef[IList[Int], mutable.Seq[AnyVal]]

    assertStrictSubtype(listOf(defn.NothingType), genSeqOf(defn.IntType)).withRef[IList[Nothing], GSeq[Int]]
    assertNeitherSubtype(listOf(defn.NothingType), mutableSeqOf(defn.IntType)).withRef[IList[Nothing], mutable.Seq[Int]]

    assertNeitherSubtype(mutableSeqOf(defn.IntType), mutableSeqOf(defn.AnyValType))
      .withRef[mutable.Seq[Int], mutable.Seq[AnyVal]]
    assertStrictSubtype(mutableSeqOf(defn.IntType), genSeqOf(defn.AnyValType)).withRef[mutable.Seq[Int], GSeq[AnyVal]]
  }

  testWithContext("polymorphic-type-alias-subclasses-variance") {
    assertStrictSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.AnyValType)
    ).withRef[List[Int], ISeq[AnyVal]]
    assertStrictSubtype(listOf(defn.IntType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.AnyValType))
      .withRef[IList[Int], Seq[AnyVal]]

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.StringType)
    ).withRef[List[Int], ISeq[JString]]
    assertNeitherSubtype(listOf(defn.StringType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.IntType))
      .withRef[IList[JString], Seq[Int]]
  }

  testWithContext("polymorphic-opaque-type-alias") {
    val IArraySym = ctx.findStaticType("scala.IArray$package.IArray").asInstanceOf[TypeMemberSymbol]

    assertEquiv(iarrayOf(defn.IntType), iarrayOf(defn.IntType)).withRef[IArray[Int], IArray[Int]]
    assertEquiv(iarrayOf(defn.StringType), iarrayOf(defn.StringType)).withRef[IArray[JString], IArray[JString]]
    assertEquiv(findTypesFromTASTyNamed("iarrayOfInt"), iarrayOf(defn.IntType)).withRef[IArray[Int], IArray[Int]]

    assertNeitherSubtype(iarrayOf(defn.IntType), iarrayOf(defn.StringType)).withRef[IArray[Int], IArray[JString]]

    // FIXME Handle variance
    //assertStrictSubtype(iarrayOf(defn.IntType), iarrayOf(defn.AnyValType))
    //assertStrictSubtype(findTypesFromTASTyNamed("iarrayOfInt"), iarrayOf(defn.AnyValType))

    assertStrictSubtype(iarrayOf(defn.StringType), defn.AnyType).withRef[IArray[JString], Any]
    assertNeitherSubtype(iarrayOf(defn.StringType), defn.AnyRefType).withRef[IArray[JString], AnyRef]

    val invariantOpaqueRef = ctx.findStaticType("subtyping.TypesFromTASTy.InvariantOpaque").staticRef

    assertEquiv(invariantOpaqueRef.appliedTo(defn.IntType), invariantOpaqueRef.appliedTo(defn.IntType))
    assertEquiv(findTypesFromTASTyNamed("invariantOpaqueOfInt"), invariantOpaqueRef.appliedTo(defn.IntType))

    assertNeitherSubtype(invariantOpaqueRef.appliedTo(defn.IntType), invariantOpaqueRef.appliedTo(defn.AnyValType))
    assertNeitherSubtype(findTypesFromTASTyNamed("invariantOpaqueOfInt"), invariantOpaqueRef.appliedTo(defn.AnyValType))

    assertStrictSubtype(invariantOpaqueRef.appliedTo(defn.IntType), defn.AnyType)
  }

  testWithContext("crosspackage-toplevel-opaque-type-alias") {
    import crosspackagetasty.TopLevelOpaqueTypeAlias

    val TopLevelOpaqueTypeAliasSym =
      ctx
        .findStaticType("crosspackagetasty.TopLevelOpaqueTypeAlias$package.TopLevelOpaqueTypeAlias")
        .asInstanceOf[TypeMemberSymbol]

    assertEquiv(TopLevelOpaqueTypeAliasSym.staticRef, TopLevelOpaqueTypeAliasSym.staticRef)
      .withRef[TopLevelOpaqueTypeAlias, TopLevelOpaqueTypeAlias]

    assertNeitherSubtype(TopLevelOpaqueTypeAliasSym.staticRef, defn.IntType)
      .withRef[TopLevelOpaqueTypeAlias, Int]

    assertEquiv(findTypesFromTASTyNamed("toplevelOpaqueTypeAlias"), TopLevelOpaqueTypeAliasSym.staticRef)
  }

  testWithContext("this-type") {
    // No withRef's in this test because we cannot write code that refers to the `this` of an external class

    val TypeMemberClass = ctx.findTopLevelClass("simple_trees.TypeMember")
    val TypeMemberThis = ThisType(TypeMemberClass.typeRef)

    assertStrictSubtype(TypeMemberThis, TypeMemberClass.typeRef)
    assertStrictSubtype(TypeMemberThis, defn.ObjectType)

    assertNeitherSubtype(TypeMemberThis, defn.StringType)
  }

  testWithContext("type-member-this") {
    // No withRef's in this test because we cannot write code that refers to the `this` of an external class

    val TypeMemberClass = ctx.findTopLevelClass("simple_trees.TypeMember")
    val TypeMemberThis = ThisType(TypeMemberClass.typeRef)

    assertEquiv(TypeMemberThis.select(tname"TypeMember"), defn.IntType)
    assertEquiv(TypeMemberThis.select(tname"TypeMember"), TypeMemberThis.select(tname"TypeMember"))

    assertStrictSubtype(TypeMemberThis.select(tname"AbstractType"), defn.AnyType)
    assertEquiv(TypeMemberThis.select(tname"AbstractType"), TypeMemberThis.select(tname"AbstractType"))
    assertNeitherSubtype(TypeMemberThis.select(tname"AbstractType"), defn.ObjectType)
    assertNeitherSubtype(defn.NullType, TypeMemberThis.select(tname"AbstractType"))

    assertStrictSubtype(TypeMemberThis.select(tname"AbstractWithBounds"), ProductClass.typeRef)
    assertEquiv(TypeMemberThis.select(tname"AbstractWithBounds"), TypeMemberThis.select(tname"AbstractWithBounds"))
    assertStrictSubtype(defn.NullType, TypeMemberThis.select(tname"AbstractWithBounds"))
  }

  testWithContext("type-member-external") {
    import simple_trees.TypeMember

    val TypeMemberClass = ctx.findTopLevelClass("simple_trees.TypeMember")
    val TypeMemberRef = TypeMemberClass.typeRef

    assertEquiv(TypeMemberRef.select(tname"TypeMember"), defn.IntType).withRef[TypeMember#TypeMember, Int]
    assertEquiv(TypeMemberRef.select(tname"TypeMember"), TypeMemberRef.select(tname"TypeMember"))
      .withRef[TypeMember#TypeMember, TypeMember#TypeMember]

    assertStrictSubtype(TypeMemberRef.select(tname"AbstractType"), defn.AnyType).withRef[TypeMember#AbstractType, Any]
    assertEquiv(TypeMemberRef.select(tname"AbstractType"), TypeMemberRef.select(tname"AbstractType"))
      .withRef[TypeMember#AbstractType, TypeMember#AbstractType]
    assertNeitherSubtype(TypeMemberRef.select(tname"AbstractType"), defn.ObjectType)
      .withRef[TypeMember#AbstractType, Object]
    assertNeitherSubtype(defn.NullType, TypeMemberRef.select(tname"AbstractType"))
      .withRef[Null, TypeMember#AbstractType]

    // Should have `.withRef[TypeMember#AbstractWithBounds, Product]` but it does not work, for some reason
    assertStrictSubtype(TypeMemberRef.select(tname"AbstractWithBounds"), ProductClass.typeRef)

    assertEquiv(TypeMemberRef.select(tname"AbstractWithBounds"), TypeMemberRef.select(tname"AbstractWithBounds"))
      .withRef[TypeMember#AbstractWithBounds, TypeMember#AbstractWithBounds]
    assertStrictSubtype(defn.NullType, TypeMemberRef.select(tname"AbstractWithBounds"))
      .withRef[Null, TypeMember#AbstractWithBounds]
  }

  testWithContext("simple-paths") {
    import subtyping.paths.{A, B, C, SimplePaths, OtherSimplePaths}

    val paths = "subtyping.paths"
    val AClass = ctx.findTopLevelClass(s"$paths.A")
    val BClass = ctx.findTopLevelClass(s"$paths.B")
    val CClass = ctx.findTopLevelClass(s"$paths.C")
    val SimplePathsClass = ctx.findTopLevelClass(s"$paths.SimplePaths")
    val OtherSimplePathsClass = ctx.findTopLevelClass(s"$paths.OtherSimplePaths")

    val setupMethod = ctx.findTopLevelModuleClass(s"$paths.Setup").findNonOverloadedDecl(name"simplePaths")
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val xAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs.get, name"xAlias"))

    val refx: SimplePaths = new SimplePaths
    val refy: SimplePaths = new SimplePaths
    val refz: OtherSimplePaths = new OtherSimplePaths
    val refxAlias: refx.type = refx

    assertStrictSubtype(x, SimplePathsClass.typeRef)
    assertStrictSubtype(y, SimplePathsClass.typeRef)
    assertStrictSubtype(z, OtherSimplePathsClass.typeRef)
    assertStrictSubtype(xAlias, SimplePathsClass.typeRef)

    // Weird spec stuff: Null <: x.type is true because the declared type U of x is such that Null <: U
    // No 'withRef' because this codebase uses explicit nulls; we would need an Any-typed or (T | Null)-typed reference
    assertStrictSubtype(defn.NullType, x)
    assertStrictSubtype(defn.NullType, xAlias)
    assertStrictSubtype(defn.NullType, xAlias.symbol.declaredType)

    assertEquiv(x.select(tname"AbstractType"), x.select(tname"AbstractType"))
      .withRef[refx.AbstractType, refx.AbstractType]
    assertEquiv(x.select(tname"AbstractType"), x.select(tname"AliasOfAbstractType"))
      .withRef[refx.AbstractType, refx.AliasOfAbstractType]

    assertNeitherSubtype(x.select(tname"AbstractType"), y.select(tname"AbstractType"))
      .withRef[refx.AbstractType, refy.AbstractType]
    assertNeitherSubtype(x.select(tname"AbstractType"), z.select(tname"AbstractType"))
      .withRef[refx.AbstractType, refz.AbstractType]

    assertStrictSubtype(x.select(tname"AbstractTypeWithBounds"), AClass.typeRef).withRef[refx.AbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, x.select(tname"AbstractTypeWithBounds")).withRef[C, refx.AbstractTypeWithBounds]
    assertNeitherSubtype(x.select(tname"AbstractTypeWithBounds"), BClass.typeRef)
      .withRef[refx.AbstractTypeWithBounds, B]

    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), x.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[refx.AliasOfAbstractTypeWithBounds, refx.AliasOfAbstractTypeWithBounds]
    assertStrictSubtype(x.select(tname"AliasOfAbstractTypeWithBounds"), AClass.typeRef)
      .withRef[refx.AliasOfAbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, x.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[C, refx.AliasOfAbstractTypeWithBounds]
    assertNeitherSubtype(x.select(tname"AliasOfAbstractTypeWithBounds"), BClass.typeRef)
      .withRef[refx.AliasOfAbstractTypeWithBounds, B]

    assertEquiv(x, xAlias)

    assertEquiv(x.select(tname"AbstractType"), xAlias.select(tname"AbstractType"))
      .withRef[refx.AbstractType, refxAlias.AbstractType]
    assertEquiv(x.select(tname"AbstractType"), xAlias.select(tname"AliasOfAbstractType"))
      .withRef[refx.AbstractType, refxAlias.AliasOfAbstractType]
    assertEquiv(x.select(tname"AliasOfAbstractType"), xAlias.select(tname"AbstractType"))
      .withRef[refx.AliasOfAbstractType, refxAlias.AbstractType]
    assertEquiv(x.select(tname"AliasOfAbstractType"), xAlias.select(tname"AliasOfAbstractType"))
      .withRef[refx.AliasOfAbstractType, refxAlias.AliasOfAbstractType]

    assertEquiv(x.select(tname"AbstractTypeWithBounds"), xAlias.select(tname"AbstractTypeWithBounds"))
      .withRef[refx.AbstractTypeWithBounds, refxAlias.AbstractTypeWithBounds]
    assertEquiv(x.select(tname"AbstractTypeWithBounds"), xAlias.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[refx.AbstractTypeWithBounds, refxAlias.AliasOfAbstractTypeWithBounds]
    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), xAlias.select(tname"AbstractTypeWithBounds"))
      .withRef[refx.AliasOfAbstractTypeWithBounds, refxAlias.AbstractTypeWithBounds]
    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), xAlias.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[refx.AliasOfAbstractTypeWithBounds, refxAlias.AliasOfAbstractTypeWithBounds]
  }

  testWithContext("simple-paths-in-subclasses") {
    import subtyping.paths.{A, B, C, SimplePaths, ConcreteSimplePathsChild}

    val paths = "subtyping.paths"
    val AClass = ctx.findTopLevelClass(s"$paths.A")
    val BClass = ctx.findTopLevelClass(s"$paths.B")
    val CClass = ctx.findTopLevelClass(s"$paths.C")
    val SimplePathsClass = ctx.findTopLevelClass(s"$paths.SimplePaths")
    val ConcreteSimplePathsChildClass = ctx.findTopLevelClass(s"$paths.ConcreteSimplePathsChild")

    val setupMethod = ctx.findTopLevelModuleClass(s"$paths.Setup").findNonOverloadedDecl(name"subclassPaths")
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val yAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs.get, name"yAlias"))

    val refx: SimplePaths = new SimplePaths
    val refy: ConcreteSimplePathsChild = new ConcreteSimplePathsChild
    val refz: ConcreteSimplePathsChild = new ConcreteSimplePathsChild
    val refyAlias: refy.type = refy

    assertStrictSubtype(x, SimplePathsClass.typeRef)
    assertStrictSubtype(y, ConcreteSimplePathsChildClass.typeRef)
    assertStrictSubtype(z, ConcreteSimplePathsChildClass.typeRef)
    assertStrictSubtype(yAlias, ConcreteSimplePathsChildClass.typeRef)

    assertEquiv(y.select(tname"AbstractType"), defn.StringType).withRef[refy.AbstractType, JString]
    assertEquiv(y.select(tname"AbstractType"), z.select(tname"AbstractType"))
      .withRef[refy.AbstractType, refz.AbstractType]
    assertNeitherSubtype(x.select(tname"AbstractType"), y.select(tname"AbstractType"))
      .withRef[refx.AbstractType, refy.AbstractType]

    assertEquiv(y.select(tname"AliasOfAbstractType"), y.select(tname"AbstractType"))
      .withRef[refy.AliasOfAbstractType, refy.AbstractType]
    assertEquiv(y.select(tname"AliasOfAbstractType"), defn.StringType).withRef[refy.AliasOfAbstractType, JString]
    assertEquiv(y.select(tname"AliasOfAbstractType"), z.select(tname"AliasOfAbstractType"))
      .withRef[refy.AliasOfAbstractType, refz.AliasOfAbstractType]

    assertEquiv(y.select(tname"AbstractTypeWithBounds"), BClass.typeRef).withRef[refy.AbstractTypeWithBounds, B]
    assertStrictSubtype(y.select(tname"AbstractTypeWithBounds"), AClass.typeRef).withRef[refy.AbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, y.select(tname"AbstractTypeWithBounds")).withRef[C, refy.AbstractTypeWithBounds]

    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), BClass.typeRef)
      .withRef[refy.AliasOfAbstractTypeWithBounds, B]
    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), y.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[refy.AliasOfAbstractTypeWithBounds, refy.AliasOfAbstractTypeWithBounds]
    assertStrictSubtype(y.select(tname"AliasOfAbstractTypeWithBounds"), AClass.typeRef)
      .withRef[refy.AliasOfAbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, y.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[C, refy.AliasOfAbstractTypeWithBounds]

    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), z.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[refy.AliasOfAbstractTypeWithBounds, refz.AliasOfAbstractTypeWithBounds]

    assertEquiv(y, yAlias)
    assertEquiv(y.select(tname"AbstractType"), yAlias.select(tname"AbstractType"))
      .withRef[refy.AbstractType, refyAlias.AbstractType]
    assertEquiv(y.select(tname"AbstractType"), yAlias.select(tname"AliasOfAbstractType"))
      .withRef[refy.AbstractType, refyAlias.AliasOfAbstractType]
    assertEquiv(yAlias.select(tname"AbstractType"), defn.StringType).withRef[refyAlias.AbstractType, JString]
    assertEquiv(y.select(tname"AliasOfAbstractType"), yAlias.select(tname"AbstractType"))
      .withRef[refy.AliasOfAbstractType, refyAlias.AbstractType]
    assertEquiv(y.select(tname"AliasOfAbstractType"), yAlias.select(tname"AliasOfAbstractType"))
      .withRef[refy.AliasOfAbstractType, refyAlias.AliasOfAbstractType]
    assertEquiv(yAlias.select(tname"AliasOfAbstractType"), defn.StringType)
      .withRef[refyAlias.AliasOfAbstractType, JString]
  }

  testWithContext("paths-and-refinements") {
    import subtyping.paths.{A, B, C, SimplePaths, ConcreteSimplePathsChild}

    val paths = "subtyping.paths"
    val AClass = ctx.findTopLevelClass(s"$paths.A")
    val BClass = ctx.findTopLevelClass(s"$paths.B")
    val CClass = ctx.findTopLevelClass(s"$paths.C")
    val SimplePathsClass = ctx.findTopLevelClass(s"$paths.SimplePaths")
    val ConcreteSimplePathsChildClass = ctx.findTopLevelClass(s"$paths.ConcreteSimplePathsChild")

    val setupMethod = ctx.findTopLevelModuleClass(s"$paths.Setup").findNonOverloadedDecl(name"refinements")
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val yAsStringRefine = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs.get, name"yAsStringRefine"))
    val zAsIntRefine = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs.get, name"zAsIntRefine"))

    type StringRefine = SimplePaths {
      type AbstractType = String
      type AbstractTypeWithBounds <: B
      type ConcreteOnlyMember = Boolean
    }
    type IntRefine = SimplePaths { type AbstractType = Int }

    val refx: SimplePaths = new SimplePaths
    val refy: ConcreteSimplePathsChild = new ConcreteSimplePathsChild
    val refyAsStringRefine: StringRefine = refy
    val refzAsIntRefine: IntRefine = new SimplePaths {
      type AbstractType = Int
    }

    assertStrictSubtype(x, SimplePathsClass.typeRef)
    assertStrictSubtype(y, ConcreteSimplePathsChildClass.typeRef)
    assertStrictSubtype(yAsStringRefine, SimplePathsClass.typeRef)
    assertStrictSubtype(zAsIntRefine, SimplePathsClass.typeRef)

    assertNeitherSubtype(yAsStringRefine, ConcreteSimplePathsChildClass.typeRef)
    assertNeitherSubtype(zAsIntRefine, ConcreteSimplePathsChildClass.typeRef)

    assertNeitherSubtype(x.select(tname"AbstractType"), defn.StringType).withRef[refx.AbstractType, JString]
    assertEquiv(y.select(tname"AbstractType"), defn.StringType).withRef[refy.AbstractType, JString]

    assertEquiv(yAsStringRefine.select(tname"AbstractType"), defn.StringType)
      .withRef[refyAsStringRefine.AbstractType, JString]
    assertEquiv(yAsStringRefine.select(tname"AbstractType"), y.select(tname"AbstractType"))
      .withRef[refyAsStringRefine.AbstractType, refy.AbstractType]
    assertNeitherSubtype(yAsStringRefine.select(tname"AbstractType"), x.select(tname"AbstractType"))
      .withRef[refyAsStringRefine.AbstractType, refx.AbstractType]

    assertEquiv(yAsStringRefine.select(tname"ConcreteOnlyMember"), defn.BooleanType)
      .withRef[refyAsStringRefine.ConcreteOnlyMember, Boolean]
    assertEquiv(yAsStringRefine.select(tname"ConcreteOnlyMember"), y.select(tname"ConcreteOnlyMember"))
      .withRef[refyAsStringRefine.ConcreteOnlyMember, refy.ConcreteOnlyMember]
    assertNeitherSubtype(yAsStringRefine.select(tname"ConcreteOnlyMember"), x.select(tname"AbstractType"))
      .withRef[refyAsStringRefine.ConcreteOnlyMember, refx.AbstractType]

    assertEquiv(yAsStringRefine.select(tname"AliasOfAbstractType"), y.select(tname"AbstractType"))
      .withRef[refyAsStringRefine.AliasOfAbstractType, refy.AbstractType]
    assertEquiv(yAsStringRefine.select(tname"AliasOfAbstractType"), defn.StringType)
      .withRef[refyAsStringRefine.AliasOfAbstractType, JString]
    assertNeitherSubtype(
      yAsStringRefine.select(tname"AliasOfAbstractType"),
      zAsIntRefine.select(tname"AliasOfAbstractType")
    )
      .withRef[refyAsStringRefine.AliasOfAbstractType, refzAsIntRefine.AliasOfAbstractType]

    assertStrictSubtype(yAsStringRefine.select(tname"AbstractTypeWithBounds"), BClass.typeRef)
      .withRef[refyAsStringRefine.AbstractTypeWithBounds, B]
    assertStrictSubtype(yAsStringRefine.select(tname"AbstractTypeWithBounds"), AClass.typeRef)
      .withRef[refyAsStringRefine.AbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, yAsStringRefine.select(tname"AbstractTypeWithBounds"))
      .withRef[C, refyAsStringRefine.AbstractTypeWithBounds]

    assertStrictSubtype(yAsStringRefine.select(tname"AliasOfAbstractTypeWithBounds"), BClass.typeRef)
      .withRef[refyAsStringRefine.AliasOfAbstractTypeWithBounds, B]
    assertStrictSubtype(
      yAsStringRefine.select(tname"AliasOfAbstractTypeWithBounds"),
      y.select(tname"AliasOfAbstractTypeWithBounds")
    )
      .withRef[refyAsStringRefine.AliasOfAbstractTypeWithBounds, refy.AliasOfAbstractTypeWithBounds]
    assertStrictSubtype(yAsStringRefine.select(tname"AliasOfAbstractTypeWithBounds"), AClass.typeRef)
      .withRef[refyAsStringRefine.AliasOfAbstractTypeWithBounds, A]
    assertStrictSubtype(CClass.typeRef, yAsStringRefine.select(tname"AliasOfAbstractTypeWithBounds"))
      .withRef[C, refyAsStringRefine.AliasOfAbstractTypeWithBounds]

    assertNeitherSubtype(
      yAsStringRefine.select(tname"AliasOfAbstractTypeWithBounds"),
      zAsIntRefine.select(tname"AliasOfAbstractTypeWithBounds")
    )
      .withRef[refyAsStringRefine.AliasOfAbstractTypeWithBounds, refzAsIntRefine.AliasOfAbstractTypeWithBounds]
  }

  testWithContext("simple-paths-in-nested-classes") {
    import subtyping.paths.NestedClasses

    val paths = "subtyping.paths"
    val ParentClass = ctx.findStaticClass(s"$paths.NestedClasses.Parent")
    val inner = ctx.findStaticTerm(s"$paths.NestedClasses.inner")

    assertNeitherSubtype(inner.declaredType, defn.IntType).withRef[NestedClasses.inner.type, Int]
    assertStrictSubtype(inner.declaredType, ParentClass.typeRef).withRef[NestedClasses.inner.type, NestedClasses.Parent]
  }

  testWithContext("refinement-types-subtyping") {
    import subtyping.paths.{A, B, D, SimplePaths, ConcreteSimplePathsChild}

    val AClass = ctx.findTopLevelClass("subtyping.paths.A")
    val BClass = ctx.findTopLevelClass("subtyping.paths.B")
    val DClass = ctx.findTopLevelClass("subtyping.paths.D")
    val SimplePathsClass = ctx.findTopLevelClass("subtyping.paths.SimplePaths")
    val ConcreteSimplePathsChildClass = ctx.findTopLevelClass("subtyping.paths.ConcreteSimplePathsChild")
    val CharSequenceClass = ctx.findTopLevelClass("java.lang.CharSequence")

    val CharSequenceType = CharSequenceClass.appliedRef

    def refineTypeAlias(name: String, alias: Type): Type =
      TypeRefinement(SimplePathsClass.appliedRef, typeName(name), TypeAlias(alias))

    def refineTypeBound(name: String, high: Type): Type =
      TypeRefinement(SimplePathsClass.appliedRef, typeName(name), RealTypeBounds(defn.NothingType, high))

    def refinePolyTypeBound(name: String, high: Type): Type =
      val polyLow = TypeLambda(List(typeName("X")), List(defn.NothingAnyBounds), defn.NothingType)
      val polyHigh = TypeLambda(List(typeName("X")), List(defn.NothingAnyBounds), high)
      TypeRefinement(SimplePathsClass.appliedRef, typeName(name), RealTypeBounds(polyLow, polyHigh))

    def refineTerm(name: String, tpe: Type): Type =
      TermRefinement(SimplePathsClass.appliedRef, isStable = false, termName(name), tpe)

    // type refinement - exists in class

    assertEquiv(refineTypeAlias("AbstractType", defn.StringType), refineTypeAlias("AbstractType", defn.StringType))
      .withRef[SimplePaths { type AbstractType = String }, SimplePaths { type AbstractType = String }]
    assertNeitherSubtype(
      refineTypeAlias("AbstractType", defn.StringType),
      refineTypeAlias("AbstractType", defn.IntType)
    )
      .withRef[SimplePaths { type AbstractType = String }, SimplePaths { type AbstractType = CharSequence }]
    assertNeitherSubtype(
      refineTypeAlias("AbstractType", defn.StringType),
      refineTypeAlias("AbstractType", CharSequenceType)
    )
      .withRef[SimplePaths { type AbstractType = String }, SimplePaths { type AbstractType = Int }]
    assertStrictSubtype(
      refineTypeAlias("AbstractType", defn.StringType),
      refineTypeBound("AbstractType", CharSequenceType)
    )
      .withRef[SimplePaths { type AbstractType = String }, SimplePaths { type AbstractType <: CharSequence }]

    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeAlias("AbstractType", defn.StringType))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type AbstractType = String }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeAlias("AbstractType", defn.IntType))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type AbstractType = Int }]

    // type refinement - does not exist in class

    assertEquiv(refineTypeAlias("OtherType", defn.StringType), refineTypeAlias("OtherType", defn.StringType))
      .withRef[SimplePaths { type OtherType = String }, SimplePaths { type OtherType = String }]
    assertNeitherSubtype(refineTypeAlias("OtherType", defn.StringType), refineTypeAlias("OtherType", defn.IntType))
      .withRef[SimplePaths { type OtherType = String }, SimplePaths { type OtherType = Int }]
    assertNeitherSubtype(refineTypeAlias("OtherType", defn.StringType), refineTypeAlias("OtherType", CharSequenceType))
      .withRef[SimplePaths { type OtherType = String }, SimplePaths { type OtherType = CharSequence }]
    assertStrictSubtype(refineTypeAlias("OtherType", defn.StringType), refineTypeBound("OtherType", CharSequenceType))
      .withRef[SimplePaths { type OtherType = String }, SimplePaths { type OtherType <: CharSequence }]

    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeAlias("OtherType", defn.StringType))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type OtherType = String }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeAlias("OtherType", defn.IntType))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type OtherType = Int }]

    // type refinement - implemented by a class member

    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeBound("InnerClassMono", AClass.appliedRef))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type InnerClassMono <: A }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTypeBound("InnerClassMono", BClass.appliedRef))
      .withRef[ConcreteSimplePathsChild, SimplePaths { type InnerClassMono <: B }]

    assertStrictSubtype(
      ConcreteSimplePathsChildClass.appliedRef,
      refinePolyTypeBound("InnerClassPoly", AClass.appliedRef)
    )
      .withRef[ConcreteSimplePathsChild, SimplePaths { type InnerClassPoly[X] <: A }]
    assertNeitherSubtype(
      ConcreteSimplePathsChildClass.appliedRef,
      refinePolyTypeBound("InnerClassPoly", DClass.appliedRef)
    )
      .withRef[ConcreteSimplePathsChild, SimplePaths { type InnerClassPoly[X] <: D }]

    // term refinement - exists in class

    assertEquiv(refineTerm("abstractTerm", defn.StringType), refineTerm("abstractTerm", defn.StringType))
      .withRef[SimplePaths { def abstractTerm: String }, SimplePaths { def abstractTerm: String }]
    assertNeitherSubtype(refineTerm("abstractTerm", defn.StringType), refineTerm("abstractTerm", defn.IntType))
      .withRef[SimplePaths { def abstractTerm: String }, SimplePaths { def abstractTerm: Int }]
    assertStrictSubtype(refineTerm("abstractTerm", defn.StringType), refineTerm("abstractTerm", CharSequenceType))
      .withRef[SimplePaths { def abstractTerm: String }, SimplePaths { def abstractTerm: CharSequence }]

    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("abstractTerm", listOf(defn.IntType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def abstractTerm: List[Int] }]
    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("abstractTerm", listOf(defn.AnyType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def abstractTerm: List[Any] }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("abstractTerm", listOf(defn.BooleanType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def abstractTerm: List[Boolean] }]

    val refinedSomeMethodType =
      refineTerm("someMethod", MethodType(List(termName("x")), List(defn.IntType), defn.IntType))
    assertEquiv(
      refineTerm("someMethod", MethodType(List(termName("x")), List(defn.IntType), defn.IntType)),
      refinedSomeMethodType
    )
      .withRef[SimplePaths { def someMethod(x: Int): Int }, SimplePaths { def someMethod(x: Int): Int }]
    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refinedSomeMethodType)
      .withRef[ConcreteSimplePathsChild, SimplePaths { def someMethod(x: Int): Int }]
    assertNeitherSubtype(
      ConcreteSimplePathsChildClass.appliedRef,
      refineTerm("someMethod", MethodType(List(termName("x")), List(defn.IntType), defn.BooleanType))
    )
      .withRef[ConcreteSimplePathsChild, SimplePaths { def someMethod(x: Int): Boolean }]

    val refinedSomePolyMethodType =
      refineTerm(
        "somePolyMethod",
        PolyType(List(typeName("X")))(
          tl => List(defn.NothingAnyBounds),
          tl => MethodType(List(termName("x")), List(tl.paramRefs(0)), tl.paramRefs(0))
        )
      )
    assertEquiv(
      refineTerm(
        "somePolyMethod",
        PolyType(List(typeName("Y")))(
          tl => List(defn.NothingAnyBounds),
          tl => MethodType(List(termName("x")), List(tl.paramRefs(0)), tl.paramRefs(0))
        )
      ),
      refinedSomePolyMethodType
    )
      .withRef[SimplePaths { def somePolyMethod[X](x: X): X }, SimplePaths { def somePolyMethod[Y](x: Y): Y }]
    assertStrictSubtype(ConcreteSimplePathsChildClass.appliedRef, refinedSomePolyMethodType)
      .withRef[ConcreteSimplePathsChild, SimplePaths { def somePolyMethod[Y](x: Y): Y }]

    // term refinement - does not exist in class

    assertEquiv(refineTerm("otherTerm", defn.StringType), refineTerm("otherTerm", defn.StringType))
      .withRef[SimplePaths { def otherTerm: String }, SimplePaths { def otherTerm: String }]
    assertNeitherSubtype(refineTerm("otherTerm", defn.StringType), refineTerm("otherTerm", defn.IntType))
      .withRef[SimplePaths { def otherTerm: String }, SimplePaths { def otherTerm: Int }]
    assertStrictSubtype(refineTerm("otherTerm", defn.StringType), refineTerm("otherTerm", CharSequenceType))
      .withRef[SimplePaths { def otherTerm: String }, SimplePaths { def otherTerm: CharSequence }]

    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("otherTerm", listOf(defn.IntType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def otherTerm: List[Int] }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("otherTerm", listOf(defn.AnyType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def otherTerm: List[Any] }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refineTerm("otherTerm", listOf(defn.BooleanType)))
      .withRef[ConcreteSimplePathsChild, SimplePaths { def otherTerm: List[Boolean] }]

    val refinedSomeOtherMethodType =
      refineTerm("someOtherMethod", MethodType(List(termName("x")), List(defn.IntType), defn.IntType))
    assertEquiv(
      refineTerm("someOtherMethod", MethodType(List(termName("x")), List(defn.IntType), defn.IntType)),
      refinedSomeOtherMethodType
    )
      .withRef[SimplePaths { def someOtherMethod(x: Int): Int }, SimplePaths { def someOtherMethod(x: Int): Int }]
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refinedSomeOtherMethodType)
      .withRef[ConcreteSimplePathsChild, SimplePaths { def someOtherMethod(x: Int): Int }]
    assertNeitherSubtype(
      ConcreteSimplePathsChildClass.appliedRef,
      refineTerm("someOtherMethod", MethodType(List(termName("x")), List(defn.IntType), defn.BooleanType))
    )
      .withRef[ConcreteSimplePathsChild, SimplePaths { def someOtherMethod(x: Int): Boolean }]

    /* No `withRef` tests for a `someOtherPolyMethod` because dotc says:
     *
     * > Polymorphic refinement method someOtherPolyMethod without matching
     * > type in parent class SimplePaths is no longer allowed
     */
    val refinedSomeOtherPolyMethodType =
      refineTerm(
        "someOtherPolyMethod",
        PolyType(List(typeName("X")))(
          tl => List(defn.NothingAnyBounds),
          tl => MethodType(List(termName("x")), List(tl.paramRefs(0)), tl.paramRefs(0))
        )
      )
    assertEquiv(
      refineTerm(
        "someOtherPolyMethod",
        PolyType(List(typeName("Y")))(
          tl => List(defn.NothingAnyBounds),
          tl => MethodType(List(termName("x")), List(tl.paramRefs(0)), tl.paramRefs(0))
        )
      ),
      refinedSomeOtherPolyMethodType
    )
    assertNeitherSubtype(ConcreteSimplePathsChildClass.appliedRef, refinedSomeOtherPolyMethodType)
  }

  testWithContext("intersection-types") {
    assertStrictSubtype(Types.AndType.make(defn.IntType, defn.StringType), defn.IntType).withRef[Int & String, Int]

    assertStrictSubtype(Types.AndType.make(defn.StringType, defn.IntType), defn.IntType).withRef[String & Int, Int]

    assertEquiv(Types.AndType.make(defn.IntType, defn.StringType), Types.AndType.make(defn.StringType, defn.IntType))
      .withRef[Int & String, String & Int]

    assertNeitherSubtype(
      Types.AndType.make(defn.IntType, defn.StringType),
      Types.AndType.make(defn.IntType, defn.BooleanType)
    ).withRef[Int & String, Int & Boolean]

    val SerializableClass = ctx.findTopLevelClass("java.io.Serializable")
    assertEquiv(findTypesFromTASTyNamed("andType"), AndType(ProductClass.typeRef, SerializableClass.typeRef))
  }

  testWithContext("union-types") {
    assertStrictSubtype(defn.IntType, Types.OrType.make(defn.IntType, defn.StringType)).withRef[Int, Int | String]

    assertStrictSubtype(defn.IntType, Types.OrType.make(defn.StringType, defn.IntType)).withRef[Int, String | Int]

    assertEquiv(Types.OrType.make(defn.IntType, defn.StringType), Types.OrType.make(defn.StringType, defn.IntType))
      .withRef[Int | String, String | Int]

    assertNeitherSubtype(
      Types.OrType.make(defn.IntType, defn.StringType),
      Types.OrType.make(defn.IntType, defn.BooleanType)
    ).withRef[Int | String, Int | Boolean]

    assertEquiv(OrType(defn.IntType, defn.StringType), findTypesFromTASTyNamed("orType"))
  }

  testWithContext("by-name-params") {
    val Function1Class = ctx.findTopLevelClass("scala.Function1")
    def fun1Type(argType: Type, resultType: Type): Type =
      AppliedType(Function1Class.typeRef, argType :: resultType :: Nil)

    val PStringType = PredefPrefix.select(tname"String")

    assertEquiv(
      fun1Type(ByNameType(defn.StringType), defn.StringType),
      fun1Type(ByNameType(defn.StringType), defn.StringType)
    ).withRef[(=> JString) => JString, (=> JString) => JString]

    assertEquiv(fun1Type(ByNameType(defn.StringType), defn.StringType), fun1Type(ByNameType(PStringType), PStringType))
      .withRef[(=> JString) => JString, (=> PString) => PString]

    assertNeitherSubtype(
      fun1Type(ByNameType(defn.StringType), defn.StringType),
      fun1Type(defn.StringType, defn.StringType)
    ).withRef[(=> JString) => JString, JString => JString]

    assertNeitherSubtype(
      fun1Type(ByNameType(defn.StringType), defn.StringType),
      fun1Type(ByNameType(defn.IntType), defn.StringType)
    ).withRef[(=> JString) => JString, (=> Int) => JString]
  }

  testWithContext("wildcard-type-bounds") {
    val seqOfWildcardProduct = mutableSeqOf(WildcardTypeBounds(RealTypeBounds(defn.NothingType, ProductClass.typeRef)))
    val seqOfWildcardList = mutableSeqOf(WildcardTypeBounds(RealTypeBounds(defn.NothingType, listOf(defn.AnyType))))
    val seqOfWildcardOption = mutableSeqOf(WildcardTypeBounds(RealTypeBounds(defn.NothingType, optionOf(defn.AnyType))))

    assertEquiv(
      seqOfWildcardProduct,
      mutableSeqOf(WildcardTypeBounds(RealTypeBounds(defn.NothingType, ProductClass.typeRef)))
    ).withRef[mutable.Seq[? <: Product], mutable.Seq[? <: Product]]

    assertNeitherSubtype(seqOfWildcardProduct, seqOfWildcardList)
      .withRef[mutable.Seq[? <: Product], mutable.Seq[? <: List[Any]]]

    assertStrictSubtype(seqOfWildcardOption, seqOfWildcardProduct)
      .withRef[mutable.Seq[? <: Option[Any]], mutable.Seq[? <: Product]]
  }

  testWithContext("type-lambdas") {
    val Function1Class = ctx.findTopLevelClass("scala.Function1")
    def fun1Type(argType: Type, resultType: Type): Type =
      AppliedType(Function1Class.typeRef, argType :: resultType :: Nil)

    def makeTToTTypeLambda() = TypeLambda(typeName("T") :: Nil)(
      _ => List(defn.NothingAnyBounds),
      tl => fun1Type(tl.paramRefs(0), tl.paramRefs(0))
    )
    val tToTTypeLambda = makeTToTTypeLambda()

    val fromTasty = findTypesFromTASTyNamed(typeName("TToTType"))

    type TToTType = [T] => T => T

    assertEquiv(tToTTypeLambda, makeTToTTypeLambda()).withRef[TToTType, TToTType]
    assertEquiv(tToTTypeLambda, fromTasty)
  }

  testWithContext("higher-kinded-types") {
    val higherKindedPoly =
      PolyType(List(typeName("F"), typeName("T")))(
        pt =>
          List(
            RealTypeBounds(
              TypeLambda(List(typeName("X")))(tl => List(defn.NothingAnyBounds), tl => defn.NothingType),
              TypeLambda(List(typeName("X")))(tl => List(defn.NothingAnyBounds), tl => defn.AnyType)
            ),
            defn.NothingAnyBounds
          ),
        pt =>
          MethodType(List(termName("x")))(
            mt => List(AppliedType(pt.paramRefs(0), List(pt.paramRefs(1)))),
            mt => AppliedType(pt.paramRefs(0), List(pt.paramRefs(1)))
          )
      )

    val fromTASTy = findTypesFromTASTyNamed("higherKinded").asInstanceOf[PolyType]

    // within higherKindedPoly

    assertEquiv(higherKindedPoly.paramRefs(0), higherKindedPoly.paramRefs(0))
    assertEquiv(higherKindedPoly.paramRefs(1), higherKindedPoly.paramRefs(1))

    assertNeitherSubtype(higherKindedPoly.paramRefs(0), higherKindedPoly.paramRefs(1))

    assertEquiv(
      higherKindedPoly.paramRefs(0).appliedTo(higherKindedPoly.paramRefs(1)),
      higherKindedPoly.paramRefs(0).appliedTo(higherKindedPoly.paramRefs(1))
    )

    // within fromTASTy

    assertEquiv(fromTASTy.paramRefs(0), fromTASTy.paramRefs(0))
    assertEquiv(fromTASTy.paramRefs(1), fromTASTy.paramRefs(1))

    assertNeitherSubtype(fromTASTy.paramRefs(0), fromTASTy.paramRefs(1))

    assertEquiv(
      fromTASTy.paramRefs(0).appliedTo(fromTASTy.paramRefs(1)),
      fromTASTy.paramRefs(0).appliedTo(fromTASTy.paramRefs(1))
    )

    // between higherKindedPoly and fromTASTy

    assertNeitherSubtype(higherKindedPoly.paramRefs(0), fromTASTy.paramRefs(0))
    assertNeitherSubtype(higherKindedPoly.paramRefs(1), fromTASTy.paramRefs(1))

    assertNeitherSubtype(
      higherKindedPoly.paramRefs(0).appliedTo(higherKindedPoly.paramRefs(1)),
      fromTASTy.paramRefs(0).appliedTo(fromTASTy.paramRefs(1))
    )
  }

  testWithContext("annotated-types") {
    import scala.annotation.unchecked.uncheckedVariance as uV

    // TODO Differentiate *refining* annotations

    val uncheckedVarianceClass = ctx.findTopLevelClass("scala.annotation.unchecked.uncheckedVariance")
    val annot = Annotation(uncheckedVarianceClass)

    assertEquiv(AnnotatedType(defn.IntType, annot), AnnotatedType(defn.IntType, annot)).withRef[Int @uV, Int @uV]
    assertEquiv(defn.IntType, AnnotatedType(defn.IntType, annot)).withRef[Int, Int @uV]
    assertEquiv(AnnotatedType(defn.IntType, annot), defn.IntType).withRef[Int @uV, Int]

    assertStrictSubtype(AnnotatedType(defn.IntType, annot), AnnotatedType(defn.AnyValType, annot))
      .withRef[Int @uV, AnyVal @uV]
    assertStrictSubtype(defn.IntType, AnnotatedType(defn.AnyValType, annot)).withRef[Int, AnyVal @uV]
    assertStrictSubtype(AnnotatedType(defn.IntType, annot), defn.AnyValType).withRef[Int @uV, AnyVal]
  }

  testWithContext("match-types-mono-reduced") {
    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val matchTypeMono2 = findTypesFromTASTyNamed(typeName("MatchTypeMono2"))

    val matchTypeMono2Int = matchTypeMono2.appliedTo(defn.IntType).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2Int.reduced).isDefined)
    assertEquiv(matchTypeMono2Int.reduced.get, defn.StringType)
      .withRef[MatchTypeMono2[Int], String]
    assertEquiv(matchTypeMono2Int, defn.StringType)
      .withRef[MatchTypeMono2[Int], String]
    assertNeitherSubtype(matchTypeMono2Int, defn.DoubleType)
      .withRef[MatchTypeMono2[Int], Double]
    assertNeitherSubtype(matchTypeMono2Int, defn.BooleanType)
      .withRef[MatchTypeMono2[Int], Boolean]

    val matchTypeMono2Boolean = matchTypeMono2.appliedTo(defn.BooleanType).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2Boolean.reduced).isDefined)
    assertEquiv(matchTypeMono2Boolean.reduced.get, defn.DoubleType)
      .withRef[MatchTypeMono2[Boolean], Double]
    assertEquiv(matchTypeMono2Boolean, defn.DoubleType)
      .withRef[MatchTypeMono2[Boolean], Double]
    assertNeitherSubtype(matchTypeMono2Boolean, defn.StringType)
      .withRef[MatchTypeMono2[Boolean], String]
    assertNeitherSubtype(matchTypeMono2Boolean, defn.BooleanType)
      .withRef[MatchTypeMono2[Boolean], Boolean]

    val matchTypeMono2True = matchTypeMono2.appliedTo(ConstantType(Constant(true))).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2True.reduced).isDefined)
    assertEquiv(matchTypeMono2True.reduced.get, defn.DoubleType)
      .withRef[MatchTypeMono2[Boolean], Double]
    assertEquiv(matchTypeMono2True, defn.DoubleType)
      .withRef[MatchTypeMono2[Boolean], Double]
    assertNeitherSubtype(matchTypeMono2True, defn.StringType)
      .withRef[MatchTypeMono2[Boolean], String]
    assertNeitherSubtype(matchTypeMono2True, defn.BooleanType)
      .withRef[MatchTypeMono2[Boolean], Boolean]

    val matchTypeMono2String = matchTypeMono2.appliedTo(defn.StringType).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2String.reduced).isEmpty)

    val matchTypeMono2WithDefault = findTypesFromTASTyNamed(typeName("MatchTypeMono2WithDefault"))

    val matchTypeMono2WithDefaultString = matchTypeMono2WithDefault.appliedTo(defn.StringType).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2WithDefaultString.reduced).isDefined)
    assertEquiv(matchTypeMono2WithDefaultString.reduced.get, ProductClass.typeRef)
      .withRef[MatchTypeMono2WithDefault[String], Product]
    assertEquiv(matchTypeMono2WithDefaultString, ProductClass.typeRef)
      .withRef[MatchTypeMono2WithDefault[String], Product]
  }

  testWithContext("match-types-poly-reduced") {
    import subtyping.TypesFromTASTy.{Consumer, Inv}

    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val invRef = ctx.findStaticType("subtyping.TypesFromTASTy.Inv").staticRef
    val consumerRef = ctx.findStaticType("subtyping.TypesFromTASTy.Consumer").staticRef

    val matchTypePoly2 = findTypesFromTASTyNamed(typeName("MatchTypePoly2"))

    val matchTypePoly2ListInt = matchTypePoly2.appliedTo(listOf(defn.IntType)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2ListInt.reduced).isDefined)
    assertEquiv(matchTypePoly2ListInt.reduced.get, defn.IntType).withRef[MatchTypePoly2[List[Int]], Int]
    assertEquiv(matchTypePoly2ListInt, defn.IntType).withRef[MatchTypePoly2[List[Int]], Int]

    val matchTypePoly2ListWildcard =
      matchTypePoly2.appliedTo(listOf(WildcardTypeBounds.NothingAny)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2ListWildcard.reduced).isDefined)
    assertEquiv(matchTypePoly2ListWildcard.reduced.get, defn.AnyType).withRef[MatchTypePoly2[List[?]], Any]
    assertEquiv(matchTypePoly2ListWildcard, defn.AnyType).withRef[MatchTypePoly2[List[?]], Any]

    val nilType = ctx.findStaticTerm("scala.collection.immutable.Nil").staticRef
    val matchTypePoly2Nil = matchTypePoly2.appliedTo(nilType).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2Nil.reduced).isDefined)
    assertEquiv(matchTypePoly2Nil.reduced.get, defn.NothingType).withRef[MatchTypePoly2[Nil.type], Nothing]
    assertEquiv(matchTypePoly2Nil, defn.NothingType).withRef[MatchTypePoly2[Nil.type], Nothing]

    val matchTypePoly2InvInt = matchTypePoly2.appliedTo(invRef.appliedTo(defn.IntType)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2InvInt.reduced).isDefined)
    assertEquiv(matchTypePoly2InvInt.reduced.get, defn.IntType).withRef[MatchTypePoly2[Inv[Int]], Int]
    assertEquiv(matchTypePoly2InvInt, defn.IntType).withRef[MatchTypePoly2[Inv[Int]], Int]

    val matchTypePoly2InvWildcard =
      matchTypePoly2.appliedTo(invRef.appliedTo(WildcardTypeBounds.NothingAny)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2InvWildcard.reduced).isEmpty)

    val matchTypePoly2ConsumerInt =
      matchTypePoly2.appliedTo(consumerRef.appliedTo(defn.IntType)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2ConsumerInt.reduced).isDefined)
    assertEquiv(matchTypePoly2ConsumerInt.reduced.get, defn.IntType).withRef[MatchTypePoly2[Consumer[Int]], Int]
    assertEquiv(matchTypePoly2ConsumerInt, defn.IntType).withRef[MatchTypePoly2[Consumer[Int]], Int]

    val matchTypePoly2ConsumerWildcard =
      matchTypePoly2.appliedTo(consumerRef.appliedTo(WildcardTypeBounds.NothingAny)).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2ConsumerWildcard.reduced).isDefined)
    assertEquiv(matchTypePoly2ConsumerWildcard.reduced.get, defn.NothingType)
      .withRef[MatchTypePoly2[Consumer[?]], Nothing]
    assertEquiv(matchTypePoly2ConsumerWildcard, defn.NothingType).withRef[MatchTypePoly2[Consumer[?]], Nothing]
  }

  testWithContext("match-types-bound") {
    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val thisTypeMemberRef = thisTypeRefFromTASTy(typeName("TypeMember"))

    val matchTypeMono2 = findTypesFromTASTyNamed(typeName("MatchTypeMono2"))
    val matchTypeMono2TypeMember = matchTypeMono2.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2TypeMember.reduced).isEmpty)

    assertStrictSubtype(matchTypeMono2TypeMember, defn.AnyType).withRef[MatchTypeMono2[TypeMember], Any]
    assertNeitherSubtype(matchTypeMono2TypeMember, defn.AnyValType).withRef[MatchTypeMono2[TypeMember], AnyVal]

    val matchTypeMono2Bounded = findTypesFromTASTyNamed(typeName("MatchTypeMono2Bounded"))
    val matchTypeMono2BoundedTypeMember = matchTypeMono2Bounded.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2BoundedTypeMember.reduced).isEmpty)

    assertStrictSubtype(matchTypeMono2BoundedTypeMember, defn.AnyType).withRef[MatchTypeMono2Bounded[TypeMember], Any]
    assertStrictSubtype(matchTypeMono2BoundedTypeMember, defn.AnyValType)
      .withRef[MatchTypeMono2Bounded[TypeMember], AnyVal]
    assertNeitherSubtype(matchTypeMono2BoundedTypeMember, defn.AnyRefType)
      .withRef[MatchTypeMono2Bounded[TypeMember], AnyRef]
  }

  testWithContext("match-types-against-match-types") {
    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val thisTypeMemberRef = thisTypeRefFromTASTy(typeName("TypeMember"))

    val matchTypeMono2 = findTypesFromTASTyNamed(typeName("MatchTypeMono2"))
    val matchTypeMono2TypeMember = matchTypeMono2.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2TypeMember.reduced).isEmpty)

    val matchTypeMono2TypeMemberBis = matchTypeMono2.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]

    assertEquiv(matchTypeMono2TypeMember, matchTypeMono2TypeMemberBis)
      .withRef[MatchTypeMono2[TypeMember], MatchTypeMono2[TypeMember]]

    val matchTypeMono2Subtype = findTypesFromTASTyNamed(typeName("MatchTypeMono2Subtype"))
    val matchTypeMono2SubtypeTypeMember = matchTypeMono2Subtype.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]
    assert(clue(matchTypeMono2SubtypeTypeMember.reduced).isEmpty)

    assertStrictSubtype(matchTypeMono2SubtypeTypeMember, matchTypeMono2TypeMember)
      .withRef[MatchTypeMono2Subtype[TypeMember], MatchTypeMono2[TypeMember]]

    val matchTypePoly2 = findTypesFromTASTyNamed(typeName("MatchTypePoly2"))
    val matchTypePoly2TypeMember = matchTypePoly2.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]
    assert(clue(matchTypePoly2TypeMember.reduced).isEmpty)

    val matchTypePoly2TypeMemberBis = matchTypePoly2.appliedTo(thisTypeMemberRef).asInstanceOf[MatchType]

    assertEquiv(matchTypePoly2TypeMember, matchTypePoly2TypeMemberBis)
      .withRef[MatchTypePoly2[TypeMember], MatchTypePoly2[TypeMember]]
    assertNeitherSubtype(matchTypePoly2TypeMember, matchTypeMono2TypeMember)
      .withRef[MatchTypePoly2[TypeMember], MatchTypeMono2[TypeMember]]
  }

  testWithContext("match-types-with-literal-types") {
    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val matchTypeLiterals = findTypesFromTASTyNamed(typeName("MatchTypeLiterals"))

    def const(x: Int): ConstantType = ConstantType(Constant(x))

    assertEquiv(matchTypeLiterals.appliedTo(const(1)), defn.IntType).withRef[MatchTypeLiterals[1], Int]
    assertEquiv(matchTypeLiterals.appliedTo(const(3)), defn.StringType).withRef[MatchTypeLiterals[3], String]
    assertEquiv(matchTypeLiterals.appliedTo(const(5)), defn.BooleanType).withRef[MatchTypeLiterals[5], Boolean]

    assert(clue(matchTypeLiterals.appliedTo(const(2)).asInstanceOf[MatchType].reduced).isEmpty)
  }

  testWithContext("match-types-with-enums") {
    import subtyping.TypesFromTASTy.MyEnum

    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val matchTypeEnums = findTypesFromTASTyNamed(typeName("MatchTypeEnums"))
    val MyEnumPrefix = "subtyping.TypesFromTASTy.MyEnum"

    val ParametricTycon = ctx.findStaticType(s"$MyEnumPrefix.Parametric").staticRef

    assertEquiv(matchTypeEnums.appliedTo(ctx.findStaticTerm(s"$MyEnumPrefix.Singleton1").staticRef), defn.IntType)
      .withRef[MatchTypeEnums[MyEnum.Singleton1.type], Int]

    assertEquiv(matchTypeEnums.appliedTo(ParametricTycon.appliedTo(defn.IntType)), defn.DoubleType)
      .withRef[MatchTypeEnums[MyEnum.Parametric[Int]], Double]

    assertEquiv(matchTypeEnums.appliedTo(ctx.findStaticTerm(s"$MyEnumPrefix.Singleton2").staticRef), defn.StringType)
      .withRef[MatchTypeEnums[MyEnum.Singleton2.type], String]

    assertEquiv(matchTypeEnums.appliedTo(ParametricTycon.appliedTo(defn.StringType)), defn.StringType)
      .withRef[MatchTypeEnums[MyEnum.Parametric[String]], String]
  }

  testWithContext("match-types-with-old-style-enums") {
    import subtyping.TypesFromTASTy.OldStyleEnum

    val typesFromTasty = new subtyping.TypesFromTASTy
    import typesFromTasty.*

    val matchTypeEnums = findTypesFromTASTyNamed(typeName("MatchTypeOldStyleEnums"))
    val MyEnumPrefix = "subtyping.TypesFromTASTy.OldStyleEnum"

    val ParametricTycon = ctx.findStaticType(s"$MyEnumPrefix.Parametric").staticRef

    assertEquiv(matchTypeEnums.appliedTo(ctx.findStaticTerm(s"$MyEnumPrefix.Singleton1").staticRef), defn.IntType)
      .withRef[MatchTypeOldStyleEnums[OldStyleEnum.Singleton1.type], Int]

    assertEquiv(matchTypeEnums.appliedTo(ParametricTycon.appliedTo(defn.IntType)), defn.DoubleType)
      .withRef[MatchTypeOldStyleEnums[OldStyleEnum.Parametric[Int]], Double]

    assertEquiv(matchTypeEnums.appliedTo(ctx.findStaticTerm(s"$MyEnumPrefix.Singleton2").staticRef), defn.StringType)
      .withRef[MatchTypeOldStyleEnums[OldStyleEnum.Singleton2.type], String]

    assertEquiv(matchTypeEnums.appliedTo(ParametricTycon.appliedTo(defn.StringType)), defn.StringType)
      .withRef[MatchTypeOldStyleEnums[OldStyleEnum.Parametric[String]], String]
  }

  testWithContext("capture-conversion") {
    val TypeRefInClass = ctx.findTopLevelClass("simple_trees.TypeRefIn")

    def finalResultType(tpe: Type): Type = tpe match
      case tpe: MethodType => finalResultType(tpe.resultType)
      case tpe: PolyType   => finalResultType(tpe.resultType)
      case _               => tpe

    var applyBodyCount = 0

    for
      case (decl: TermSymbol) <- TypeRefInClass.declarations
      if decl.is(Method) && decl.name != nme.Constructor
    do
      val tree = decl.tree.get.asInstanceOf[DefDef].rhs.get
      assert(tree.tpe.isSubtype(finalResultType(decl.declaredType)))

      tree match
        case Apply(method @ TypeApply(poly, List(targ)), List(arg)) =>
          // Check that the term argument corresponds to the declared term param type
          val methodType = method.tpe.widen.asInstanceOf[MethodType]
          assert(clue(methodType.paramNames).sizeIs == 1)
          val argTpe = arg.tpe
          val paramTpe = methodType.instantiateParamTypes(List(argTpe)).head
          assertStrictSubtype(argTpe, paramTpe)

          // Check that the type argument corresponds to the declared type param bounds
          val polyType = poly.tpe.widen.asInstanceOf[PolyType]
          assert(clue(polyType.paramNames).sizeIs == 1)
          val targTpe = targ.toType
          val tParamBounds = polyType.instantiateParamTypeBounds(List(targTpe)).head
          assertStrictSubtype(tParamBounds.low, targTpe)
          assertStrictSubtype(targTpe, tParamBounds.high)

          applyBodyCount += 1

        case Literal(_) =>
          // Nothing to check here
          ()

        case _ =>
          fail(s"Unexpected method body $tree")
      end match
    end for

    assert(clue(applyBodyCount) == 4)
  }

  testWithContext("recursive-types") {
    val RefinedTypeTreeClass = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val innerRefValSym = RefinedTypeTreeClass.findDecl(termName("innerRefVal"))
    val valDef = innerRefValSym.tree.get.asInstanceOf[ValDef]
    val Block(List(anonClassDef: ClassDef), Typed(anonInstance, tpt)) = valDef.rhs.get: @unchecked

    val anonInstanceType = anonInstance.tpe

    val expectedType1 = tpt.toType
    assert(clue(expectedType1).isInstanceOf[RecType])
    assertStrictSubtype(anonInstanceType, expectedType1)

    val expectedType2 = valDef.tpt.toType
    assert(clue(expectedType2).isInstanceOf[RecType])
    assertEquiv(expectedType1, expectedType2)
  }

  testWithContext("from-java-object") {
    // By definition, tp <:< FromJavaObject is treated as tp <:< Any

    assertEquiv(defn.AnyType, defn.FromJavaObjectType)
    assertEquiv(defn.ObjectType, defn.FromJavaObjectType)
    assertStrictSubtype(defn.ObjectType, defn.AnyType) // yup, equivalence is not transitive

    assertStrictSubtype(defn.IntType, defn.FromJavaObjectType)
    assertStrictSubtype(defn.StringType, defn.FromJavaObjectType)

    assertEquiv(defn.ArrayTypeOf(defn.AnyType), defn.ArrayTypeOf(defn.FromJavaObjectType))
  }

end SubtypingSuite
