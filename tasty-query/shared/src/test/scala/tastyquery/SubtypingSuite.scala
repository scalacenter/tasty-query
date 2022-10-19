package tastyquery

import scala.collection.mutable

import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import Paths.*

class SubtypingSuite extends UnrestrictedUnpicklingSuite:
  def assertSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    val sub = tp1.isSubtype(tp2)
    assert(sub, clues(tp1, tp2))

  def assertNotSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    val sub = tp1.isSubtype(tp2)
    assert(!sub, clues(tp1, tp2))

  def assertEquiv(tp1: Type, tp2: Type)(using Context): Unit =
    assertSubtype(tp1, tp2)
    assertSubtype(tp2, tp1)

  def assertNeitherSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    assertNotSubtype(tp1, tp2)
    assertNotSubtype(tp2, tp1)

  def assertStrictSubtype(tp1: Type, tp2: Type)(using Context): Unit =
    assertSubtype(tp1, tp2)
    assertNotSubtype(tp2, tp1)

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
    assertEquiv(defn.IntType, defn.IntClass.typeRef)
    assertEquiv(defn.IntType, defn.IntClass.newTypeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanClass.typeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanClass.newTypeRef)
    assertNeitherSubtype(defn.IntType, defn.BooleanType)
    assertNeitherSubtype(defn.IntType, defn.ObjectType)

    assertEquiv(ProductClass.typeRef, ProductClass.newTypeRef)
    assertNeitherSubtype(ProductClass.typeRef, MatchErrorClass.typeRef)

    assertEquiv(MatchErrorClass.typeRef, MatchErrorClass.newTypeRef)
    assertNeitherSubtype(MatchErrorClass.typeRef, ProductClass.typeRef)
  }

  testWithContext("monomorphic-class-type-alias") {
    assertEquiv(defn.ObjectType, defn.AnyRefType)

    assertEquiv(defn.StringType, PredefPrefix.select(tname"String"))
    assertNeitherSubtype(defn.StringType, ScalaPackageObjectPrefix.select(tname"Cloneable"))

    assertEquiv(PredefPrefix.select(tname"String"), PredefPrefix.select(tname"String"))
    assertNeitherSubtype(PredefPrefix.select(tname"String"), ScalaPackageObjectPrefix.select(tname"Cloneable"))
  }

  testWithContext("nothing") {
    assertEquiv(defn.NothingType, defn.NothingClass.newTypeRef)

    assertStrictSubtype(defn.NothingType, defn.AnyType)
    assertStrictSubtype(defn.NothingType, defn.AnyRefType)
    assertStrictSubtype(defn.NothingType, defn.IntType)
    assertStrictSubtype(defn.NothingType, defn.StringType)
    assertStrictSubtype(defn.NothingType, PredefPrefix.select(tname"String"))
    assertStrictSubtype(defn.NothingType, defn.ArrayTypeOf(defn.IntType))
    assertStrictSubtype(defn.NothingType, defn.SeqTypeOf(defn.IntType))
    assertStrictSubtype(defn.NothingType, defn.NullType)
    assertStrictSubtype(defn.NothingType, PredefModuleClass.typeRef)
  }

  testWithContext("null") {
    assertEquiv(defn.NullType, defn.NullClass.newTypeRef)

    assertStrictSubtype(defn.NullType, defn.AnyType)
    assertStrictSubtype(defn.NullType, defn.AnyRefType)
    assertStrictSubtype(defn.NullType, defn.StringType)
    assertStrictSubtype(defn.NullType, PredefPrefix.select(tname"String"))
    assertStrictSubtype(defn.NullType, defn.ArrayTypeOf(defn.IntType))
    assertStrictSubtype(defn.NullType, defn.SeqTypeOf(defn.IntType))

    assertNeitherSubtype(defn.NullType, defn.IntType)
    assertNeitherSubtype(defn.NullType, PredefModuleClass.typeRef)
  }

  testWithContext("subclasses") {
    assertStrictSubtype(defn.AnyValType, defn.AnyType)
    assertStrictSubtype(defn.ObjectType, defn.AnyType)

    assertStrictSubtype(defn.IntType, defn.AnyType)
    assertStrictSubtype(defn.IntType, defn.AnyValType)

    assertStrictSubtype(defn.StringType, defn.ObjectType)

    assertStrictSubtype(defn.StringType, javaIOPrefix.select(tname"Serializable"))

    assertStrictSubtype(MatchErrorClass.typeRef, defn.ThrowableType)
  }

  testWithContext("subclasses-with-type-aliases") {
    assertStrictSubtype(defn.AnyRefType, defn.AnyType)
    assertStrictSubtype(defn.StringType, defn.AnyRefType)

    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.ObjectType)
    assertStrictSubtype(PredefPrefix.select(tname"String"), defn.AnyRefType)

    assertStrictSubtype(defn.StringType, ScalaPackageObjectPrefix.select(tname"Serializable"))
    assertStrictSubtype(PredefPrefix.select(tname"String"), ScalaPackageObjectPrefix.select(tname"Serializable"))

    assertStrictSubtype(MatchErrorClass.typeRef, ScalaPackageObjectPrefix.select(tname"Throwable"))
  }

  testWithContext("same-polymorphic-class") {
    assertEquiv(listOf(defn.IntType), listOf(defn.IntType))
    assertNeitherSubtype(listOf(defn.IntType), listOf(defn.StringType))

    assertEquiv(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.IntType))
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.StringType))

    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), listOf(defn.IntType))
  }

  testWithContext("same-polymorphic-class-variance") {
    assertStrictSubtype(listOf(defn.IntType), listOf(defn.AnyValType))

    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.ArrayTypeOf(defn.AnyValType))
  }

  testWithContext("polymorphic-type-alias") {
    assertEquiv(ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType), listOf(defn.IntType))

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.ArrayTypeOf(defn.IntType)
    )
  }

  testWithContext("polymorphic-subclasses") {
    assertStrictSubtype(listOf(defn.IntType), defn.SeqTypeOf(defn.IntType))
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.SeqTypeOf(defn.IntType))
  }

  testWithContext("polymorphic-type-alias-subclasses") {
    assertStrictSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.IntType)
    )
    assertStrictSubtype(listOf(defn.StringType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.StringType))

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      mutableSeqOf(defn.IntType)
    )
    assertNeitherSubtype(
      mutableSeqOf(defn.StringType),
      ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.StringType)
    )
  }

  testWithContext("polymorphic-subclasses-variance") {
    assertStrictSubtype(listOf(defn.IntType), defn.SeqTypeOf(defn.IntType))
    assertNeitherSubtype(defn.ArrayTypeOf(defn.IntType), defn.SeqTypeOf(defn.IntType))

    assertStrictSubtype(listOf(defn.IntType), genSeqOf(defn.AnyValType))
    assertNeitherSubtype(listOf(defn.IntType), mutableSeqOf(defn.AnyValType))

    assertStrictSubtype(listOf(defn.NothingType), genSeqOf(defn.IntType))
    assertNeitherSubtype(listOf(defn.NothingType), mutableSeqOf(defn.IntType))

    assertNeitherSubtype(mutableSeqOf(defn.IntType), mutableSeqOf(defn.AnyValType))
    assertStrictSubtype(mutableSeqOf(defn.IntType), genSeqOf(defn.AnyValType))
  }

  testWithContext("polymorphic-type-alias-subclasses-variance") {
    assertStrictSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.AnyValType)
    )
    assertStrictSubtype(listOf(defn.IntType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.AnyValType))

    assertNeitherSubtype(
      ScalaPackageObjectPrefix.select(tname"List").appliedTo(defn.IntType),
      defn.SeqTypeOf(defn.StringType)
    )
    assertNeitherSubtype(listOf(defn.StringType), ScalaPackageObjectPrefix.select(tname"Seq").appliedTo(defn.IntType))
  }

  testWithContext("this-type") {
    val TypeMemberClass = resolve(name"simple_trees" / tname"TypeMember").asClass
    val TypeMemberThis = ThisType(TypeMemberClass.typeRef)

    assertStrictSubtype(TypeMemberThis, TypeMemberClass.typeRef)
    assertStrictSubtype(TypeMemberThis, defn.ObjectType)

    assertNeitherSubtype(TypeMemberThis, defn.StringType)
  }

  testWithContext("type-member-this") {
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
    val TypeMemberClass = resolve(name"simple_trees" / tname"TypeMember").asClass
    val TypeMemberRef = TypeMemberClass.typeRef

    assertEquiv(TypeMemberRef.select(tname"TypeMember"), defn.IntType)
    assertEquiv(TypeMemberRef.select(tname"TypeMember"), TypeMemberRef.select(tname"TypeMember"))

    assertStrictSubtype(TypeMemberRef.select(tname"AbstractType"), defn.AnyType)
    assertEquiv(TypeMemberRef.select(tname"AbstractType"), TypeMemberRef.select(tname"AbstractType"))
    assertNeitherSubtype(TypeMemberRef.select(tname"AbstractType"), defn.ObjectType)
    assertNeitherSubtype(defn.NullType, TypeMemberRef.select(tname"AbstractType"))

    assertStrictSubtype(TypeMemberRef.select(tname"AbstractWithBounds"), ProductClass.typeRef)
    assertEquiv(TypeMemberRef.select(tname"AbstractWithBounds"), TypeMemberRef.select(tname"AbstractWithBounds"))
    assertStrictSubtype(defn.NullType, TypeMemberRef.select(tname"AbstractWithBounds"))
  }

  testWithContext("simple-paths") {
    val paths = name"subtyping" / name"paths"
    val AClass = resolve(paths / tname"A").asClass
    val BClass = resolve(paths / tname"B").asClass
    val CClass = resolve(paths / tname"C").asClass
    val DClass = resolve(paths / tname"D").asClass
    val SimplePathsClass = resolve(paths / tname"SimplePaths").asClass
    val OtherSimplePathsClass = resolve(paths / tname"OtherSimplePaths").asClass

    val setupMethod = resolve(paths / tname"Setup" / obj / name"simplePaths").asTerm
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val xAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs, name"xAlias"))

    assertStrictSubtype(x, SimplePathsClass.typeRef)
    assertStrictSubtype(y, SimplePathsClass.typeRef)
    assertStrictSubtype(z, OtherSimplePathsClass.typeRef)
    assertStrictSubtype(xAlias, SimplePathsClass.typeRef)

    assertEquiv(x.select(tname"AbstractType"), x.select(tname"AbstractType"))
    assertEquiv(x.select(tname"AbstractType"), x.select(tname"AliasOfAbstractType"))

    assertNeitherSubtype(x.select(tname"AbstractType"), y.select(tname"AbstractType"))
    assertNeitherSubtype(x.select(tname"AbstractType"), z.select(tname"AbstractType"))

    assertStrictSubtype(x.select(tname"AbstractTypeWithBounds"), AClass.typeRef)
    assertStrictSubtype(CClass.typeRef, x.select(tname"AbstractTypeWithBounds"))
    assertNeitherSubtype(x.select(tname"AbstractTypeWithBounds"), BClass.typeRef)

    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), x.select(tname"AliasOfAbstractTypeWithBounds"))
    assertStrictSubtype(x.select(tname"AliasOfAbstractTypeWithBounds"), AClass.typeRef)
    assertStrictSubtype(CClass.typeRef, x.select(tname"AliasOfAbstractTypeWithBounds"))
    assertNeitherSubtype(x.select(tname"AliasOfAbstractTypeWithBounds"), BClass.typeRef)

    assertEquiv(x, xAlias)

    assertEquiv(x.select(tname"AbstractType"), xAlias.select(tname"AbstractType"))
    assertEquiv(x.select(tname"AbstractType"), xAlias.select(tname"AliasOfAbstractType"))
    assertEquiv(x.select(tname"AliasOfAbstractType"), xAlias.select(tname"AbstractType"))
    assertEquiv(x.select(tname"AliasOfAbstractType"), xAlias.select(tname"AliasOfAbstractType"))

    assertEquiv(x.select(tname"AbstractTypeWithBounds"), xAlias.select(tname"AbstractTypeWithBounds"))
    assertEquiv(x.select(tname"AbstractTypeWithBounds"), xAlias.select(tname"AliasOfAbstractTypeWithBounds"))
    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), xAlias.select(tname"AbstractTypeWithBounds"))
    assertEquiv(x.select(tname"AliasOfAbstractTypeWithBounds"), xAlias.select(tname"AliasOfAbstractTypeWithBounds"))
  }

  testWithContext("simple-paths-in-subclasses") {
    val paths = name"subtyping" / name"paths"
    val AClass = resolve(paths / tname"A").asClass
    val BClass = resolve(paths / tname"B").asClass
    val CClass = resolve(paths / tname"C").asClass
    val DClass = resolve(paths / tname"D").asClass
    val SimplePathsClass = resolve(paths / tname"SimplePaths").asClass
    val ConcreteSimplePathsChildClass = resolve(paths / tname"ConcreteSimplePathsChild").asClass

    val setupMethod = resolve(paths / tname"Setup" / obj / name"subclassPaths").asTerm
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]
    val Left(valDefs) = setupMethodDef.paramLists.head: @unchecked
    val List(x, y, z) = valDefs.map(valDef => TermRef(NoPrefix, valDef.symbol))
    val yAlias = TermRef(NoPrefix, findLocalValDef(setupMethodDef.rhs, name"yAlias"))

    assertStrictSubtype(x, SimplePathsClass.typeRef)
    assertStrictSubtype(y, ConcreteSimplePathsChildClass.typeRef)
    assertStrictSubtype(z, ConcreteSimplePathsChildClass.typeRef)
    assertStrictSubtype(yAlias, ConcreteSimplePathsChildClass.typeRef)

    assertEquiv(y.select(tname"AbstractType"), defn.StringType)
    assertEquiv(y.select(tname"AbstractType"), z.select(tname"AbstractType"))
    assertNeitherSubtype(x.select(tname"AbstractType"), y.select(tname"AbstractType"))

    assertEquiv(y.select(tname"AliasOfAbstractType"), y.select(tname"AbstractType"))
    assertEquiv(y.select(tname"AliasOfAbstractType"), defn.StringType)
    assertEquiv(y.select(tname"AliasOfAbstractType"), z.select(tname"AliasOfAbstractType"))

    assertEquiv(y.select(tname"AbstractTypeWithBounds"), BClass.typeRef)
    assertStrictSubtype(y.select(tname"AbstractTypeWithBounds"), AClass.typeRef)
    assertStrictSubtype(CClass.typeRef, y.select(tname"AbstractTypeWithBounds"))

    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), BClass.typeRef)
    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), y.select(tname"AliasOfAbstractTypeWithBounds"))
    assertStrictSubtype(y.select(tname"AliasOfAbstractTypeWithBounds"), AClass.typeRef)
    assertStrictSubtype(CClass.typeRef, y.select(tname"AliasOfAbstractTypeWithBounds"))

    assertEquiv(y.select(tname"AliasOfAbstractTypeWithBounds"), z.select(tname"AliasOfAbstractTypeWithBounds"))

    assertEquiv(y, yAlias)
    assertEquiv(y.select(tname"AbstractType"), yAlias.select(tname"AbstractType"))
    assertEquiv(y.select(tname"AbstractType"), yAlias.select(tname"AliasOfAbstractType"))
    assertEquiv(yAlias.select(tname"AbstractType"), defn.StringType)
    assertEquiv(y.select(tname"AliasOfAbstractType"), yAlias.select(tname"AbstractType"))
    assertEquiv(y.select(tname"AliasOfAbstractType"), yAlias.select(tname"AliasOfAbstractType"))
    assertEquiv(yAlias.select(tname"AliasOfAbstractType"), defn.StringType)
  }
end SubtypingSuite
