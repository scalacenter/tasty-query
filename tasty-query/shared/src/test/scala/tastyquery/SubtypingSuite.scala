package tastyquery

import java.io.Serializable as JSerializable
import java.lang.{String as JString, Throwable as JThrowable}

import scala.collection.Seq as GSeq
import scala.collection.mutable
import scala.collection.immutable.{List as IList, Seq as ISeq}
import scala.util.NotGiven

import scala.Predef.String as PString

import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import Paths.*

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
    resolve(name"scala" / tname"Product").asClass

  def MatchErrorClass(using Context): ClassSymbol =
    resolve(name"scala" / tname"MatchError").asClass

  def ListClass(using Context): ClassSymbol =
    resolve(name"scala" / name"collection" / name"immutable" / tname"List").asClass

  def PredefModuleClass(using Context): ClassSymbol =
    resolve(name"scala" / tname"Predef" / obj).asClass

  def PredefPrefix(using Context): Type =
    PredefModuleClass.accessibleThisType

  def ScalaPackageObjectPrefix(using Context): Type =
    resolve(name"scala" / tname"package" / obj).asClass.accessibleThisType

  def javaLangPrefix(using Context): Type =
    defn.javaLangPackage.packageRef

  def javaIOPrefix(using Context): Type =
    resolve(name"java" / name"io").asPackage.packageRef

  def scalaPrefix(using Context): Type =
    defn.scalaPackage.packageRef

  def listOf(tpe: Type)(using Context): Type =
    ListClass.typeRef.appliedTo(tpe)

  def genSeqOf(tpe: Type)(using Context): Type =
    resolve(name"scala" / name"collection" / tname"Seq").asClass.typeRef.appliedTo(tpe)

  def mutableSeqOf(tpe: Type)(using Context): Type =
    resolve(name"scala" / name"collection" / name"mutable" / tname"Seq").asClass.typeRef.appliedTo(tpe)

  def findLocalValDef(body: Tree, name: TermName)(using Context): TermSymbol =
    var result: Option[TermSymbol] = None
    body.walkTree {
      case vd: ValDef if vd.name == name => result = Some(vd.symbol)
      case _                             => ()
    }
    result.getOrElse {
      throw new AssertionError(s"Could not find a local `val $name` in body\n$body")
    }
  end findLocalValDef

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

  testWithContext("this-type") {
    // No withRef's in this test because we cannot write code that refers to the `this` of an external class

    val TypeMemberClass = resolve(name"simple_trees" / tname"TypeMember").asClass
    val TypeMemberThis = ThisType(TypeMemberClass.typeRef)

    assertStrictSubtype(TypeMemberThis, TypeMemberClass.typeRef)
    assertStrictSubtype(TypeMemberThis, defn.ObjectType)

    assertNeitherSubtype(TypeMemberThis, defn.StringType)
  }

  testWithContext("type-member-this") {
    // No withRef's in this test because we cannot write code that refers to the `this` of an external class

    val TypeMemberClass = resolve(name"simple_trees" / tname"TypeMember").asClass
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

    val TypeMemberClass = resolve(name"simple_trees" / tname"TypeMember").asClass
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

    val paths = name"subtyping" / name"paths"
    val AClass = resolve(paths / tname"A").asClass
    val BClass = resolve(paths / tname"B").asClass
    val CClass = resolve(paths / tname"C").asClass
    val SimplePathsClass = resolve(paths / tname"SimplePaths").asClass
    val OtherSimplePathsClass = resolve(paths / tname"OtherSimplePaths").asClass

    val setupMethod = resolve(paths / tname"Setup" / obj / name"simplePaths").asTerm
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val xAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs, name"xAlias"))

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

    val paths = name"subtyping" / name"paths"
    val AClass = resolve(paths / tname"A").asClass
    val BClass = resolve(paths / tname"B").asClass
    val CClass = resolve(paths / tname"C").asClass
    val SimplePathsClass = resolve(paths / tname"SimplePaths").asClass
    val ConcreteSimplePathsChildClass = resolve(paths / tname"ConcreteSimplePathsChild").asClass

    val setupMethod = resolve(paths / tname"Setup" / obj / name"subclassPaths").asTerm
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val yAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs, name"yAlias"))

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
end SubtypingSuite
