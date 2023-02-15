package tastyquery

import java.io.Serializable as JSerializable
import java.lang.{String as JString, Throwable as JThrowable}

import scala.collection.Seq as GSeq
import scala.collection.mutable
import scala.collection.immutable.{List as IList, Seq as ISeq}
import scala.util.NotGiven

import scala.Predef.String as PString

import tastyquery.Annotations.*
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

  testWithContext("simple-paths-in-subclasses") {
    import subtyping.paths.NestedClasses

    val paths = "subtyping.paths"
    val ParentClass = ctx.findStaticClass(s"$paths.NestedClasses.Parent")
    val inner = ctx.findStaticTerm(s"$paths.NestedClasses.inner")

    assertNeitherSubtype(inner.declaredType, defn.IntType).withRef[NestedClasses.inner.type, Int]
    assertStrictSubtype(inner.declaredType, ParentClass.typeRef).withRef[NestedClasses.inner.type, NestedClasses.Parent]
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

end SubtypingSuite
