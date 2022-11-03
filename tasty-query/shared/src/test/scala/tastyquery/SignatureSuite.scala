package tastyquery

import munit.Location

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import Paths.*

class SignatureSuite extends UnrestrictedUnpicklingSuite:

  def assertIsSignedName(actual: Name, simpleName: String, signature: String)(using Location): Unit =
    actual match
      case name: SignedName =>
        assert(clue(name.underlying) == clue(termName(simpleName)))
        assert(clue(name.sig.toString) == clue(signature))
      case _ =>
        fail("not a Signed name", clues(actual))
  end assertIsSignedName

  def assertNotSignedName(actual: Name)(using Location): Unit =
    assert(!clue(actual).isInstanceOf[SignedName])

  testWithContext("java.lang.String") {
    val StringClass = defn.StringClass

    val charAt = StringClass.getDecl(name"charAt").get.asTerm
    assertIsSignedName(charAt.signedName, "charAt", "(scala.Int):scala.Char")

    val contains = StringClass.getDecl(name"contains").get.asTerm
    assertIsSignedName(contains.signedName, "contains", "(java.lang.CharSequence):scala.Boolean")

    val length = StringClass.getDecl(name"length").get.asTerm
    assertIsSignedName(length.signedName, "length", "():scala.Int")
  }

  testWithContext("GenericClass") {
    val GenericClass = ctx.findTopLevelClass("simple_trees.GenericClass")

    val field = GenericClass.getDecl(name"field").get.asTerm
    assertNotSignedName(field.signedName)

    val getter = GenericClass.getDecl(name"getter").get.asTerm
    assertIsSignedName(getter.signedName, "getter", "():java.lang.Object")

    val method = GenericClass.getDecl(name"method").get.asTerm
    assertIsSignedName(method.signedName, "method", "(java.lang.Object):java.lang.Object")
  }

  testWithContext("GenericMethod") {
    val GenericMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")

    val identity = GenericMethod.getDecl(name"identity").get.asTerm
    assertIsSignedName(identity.signedName, "identity", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("RichInt") {
    val RichInt = ctx.findTopLevelClass("scala.runtime.RichInt")

    val toHexString = RichInt.getDecl(name"toHexString").get.asTerm
    assertIsSignedName(toHexString.signedName, "toHexString", "():java.lang.String")
  }

  testWithContext("Product") {
    val Product = ctx.findTopLevelClass("scala.Product")

    val productIterator = Product.getDecl(name"productIterator").get.asTerm
    assertIsSignedName(productIterator.signedName, "productIterator", "():scala.collection.Iterator")
  }

  testWithContext("with type") {
    val RefinedTypeTree = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val andType = RefinedTypeTree.getDecl(name"andType").get.asTerm
    intercept[UnsupportedOperationException](andType.signedName)
  }

  testWithContext("array types") {
    val TypeRefIn = ctx.findTopLevelClass("simple_trees.TypeRefIn")

    // TODO The erasure is not actually correct here, but at least we don't crash

    val withArray = TypeRefIn.getDecl(name"withArray").get.asTerm
    assertIsSignedName(withArray.signedName, "withArray", "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtype = TypeRefIn.getDecl(name"withArrayOfSubtype").get.asTerm
    assertIsSignedName(withArrayOfSubtype.signedName, "withArrayOfSubtype", "(1,java.lang.Object):scala.Unit")

    val withArrayAnyRef = TypeRefIn.getDecl(name"withArrayAnyRef").get.asTerm
    assertIsSignedName(withArrayAnyRef.signedName, "withArrayAnyRef", "(1,java.lang.Object[]):scala.Unit")

    val withArrayOfSubtypeAnyRef = TypeRefIn.getDecl(name"withArrayOfSubtypeAnyRef").get.asTerm
    assertIsSignedName(
      withArrayOfSubtypeAnyRef.signedName,
      "withArrayOfSubtypeAnyRef",
      "(1,java.lang.Object[]):scala.Unit"
    )

    val withArrayAnyVal = TypeRefIn.getDecl(name"withArrayAnyVal").get.asTerm
    assertIsSignedName(withArrayAnyVal.signedName, "withArrayAnyVal", "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtypeAnyVal = TypeRefIn.getDecl(name"withArrayOfSubtypeAnyVal").get.asTerm
    assertIsSignedName(
      withArrayOfSubtypeAnyVal.signedName,
      "withArrayOfSubtypeAnyVal",
      "(1,java.lang.Object):scala.Unit"
    )

    val withArrayList = TypeRefIn.getDecl(name"withArrayList").get.asTerm
    assertIsSignedName(withArrayList.signedName, "withArrayList", "(1,scala.collection.immutable.List[]):scala.Unit")

    val withArrayOfSubtypeList = TypeRefIn.getDecl(name"withArrayOfSubtypeList").get.asTerm
    assertIsSignedName(
      withArrayOfSubtypeList.signedName,
      "withArrayOfSubtypeList",
      "(1,scala.collection.immutable.List[]):scala.Unit"
    )
  }

  testWithContext("type-member") {
    val TypeMember = ctx.findTopLevelClass("simple_trees.TypeMember")

    val mTypeAlias = TypeMember.getDecl(name"mTypeAlias").get.asTerm
    assertIsSignedName(mTypeAlias.signedName, "mTypeAlias", "(scala.Int):scala.Int")

    val mAbstractType = TypeMember.getDecl(name"mAbstractType").get.asTerm
    assertIsSignedName(mAbstractType.signedName, "mAbstractType", "(java.lang.Object):java.lang.Object")

    val mAbstractTypeWithBounds = TypeMember.getDecl(name"mAbstractTypeWithBounds").get.asTerm
    assertIsSignedName(mAbstractTypeWithBounds.signedName, "mAbstractTypeWithBounds", "(scala.Product):scala.Product")

    val mOpaque = TypeMember.getDecl(name"mOpaque").get.asTerm
    assertIsSignedName(mOpaque.signedName, "mOpaque", "(scala.Int):scala.Int")

    val mOpaqueWithBounds = TypeMember.getDecl(name"mOpaqueWithBounds").get.asTerm
    assertIsSignedName(mOpaqueWithBounds.signedName, "mOpaqueWithBounds", "(scala.Null):scala.Null")
  }

  testWithContext("scala2-case-class-varargs") {
    val StringContext = ctx.findTopLevelClass("scala.StringContext")

    val parts = StringContext.getDecl(name"parts").get.asTerm
    assertIsSignedName(parts.signedName, "parts", "():scala.collection.immutable.Seq")
  }

  testWithContext("scala2-method-byname") {
    val StringContext = ctx.findTopLevelClass("scala.Option")

    val getOrElse = StringContext.getDecl(name"getOrElse").get.asTerm
    assertIsSignedName(getOrElse.signedName, "getOrElse", "(1,scala.Function0):java.lang.Object")
  }

  testWithContext("scala2-existential-type") {
    val ClassTag = ctx.findTopLevelModuleClass("scala.reflect.ClassTag")

    val apply = ClassTag.getDecl(name"apply").get.asTerm
    assertIsSignedName(apply.signedName, "apply", "(1,java.lang.Class):scala.reflect.ClassTag")
  }

  testWithContext("iarray") {
    val IArraySig = ctx.findTopLevelClass("simple_trees.IArraySig")

    val from = IArraySig.getDecl(name"from").get.asTerm
    assertIsSignedName(from.signedName, "from", "():java.lang.String[]")
  }

  testWithContext("value-class-arrayOps-generic") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val genericArrayOps = MyArrayOps.getDecl(name"genericArrayOps").get.asTerm
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("value-class-arrayOps-int") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val intArrayOps = MyArrayOps.getDecl(name"intArrayOps").get.asTerm
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-generic") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val genericArrayOps = Predef.getDecl(name"genericArrayOps").get.asTerm
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-int") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val intArrayOps = Predef.getDecl(name"intArrayOps").get.asTerm
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("value-class-monomorphic") {
    val MyFlags = ctx.findTopLevelClass("inheritance.MyFlags")
    val merge = MyFlags.getDecl(name"merge").get.asTerm
    assertIsSignedName(merge.signedName, "merge", "(scala.Long):scala.Long")
  }

  testWithContext("value-class-monomorphic-arrayOf") {
    val MyFlags = ctx.findTopLevelModuleClass("inheritance.MyFlags")
    val mergeAll = MyFlags.getDecl(name"mergeAll").get.asTerm
    assertIsSignedName(mergeAll.signedName, "mergeAll", "(inheritance.MyFlags[]):scala.Long")
  }

  testWithContext("value-class-polymorphic-arrayOf") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val arrayOfIntArrayOps = MyArrayOps.getDecl(name"arrayOfIntArrayOps").get.asTerm
    assertIsSignedName(arrayOfIntArrayOps.signedName, "arrayOfIntArrayOps", "(scala.Int[][]):inheritance.MyArrayOps[]")
  }

  testWithContext("package-ref-from-tasty") {
    val LazyVals = ctx.findTopLevelModuleClass("javacompat.LazyVals")
    val getOffsetStatic = LazyVals.getDecl(name"getOffsetStatic").get.asTerm
    assertIsSignedName(getOffsetStatic.signedName, "getOffsetStatic", "(java.lang.reflect.Field):scala.Long")
  }

  testWithContext("Scala 3 special function types") {
    val SpecialFunctionTypes = ctx.findTopLevelClass("simple_trees.SpecialFunctionTypes")
    val contextFunction = SpecialFunctionTypes.getDecl(name"contextFunction").get.asTerm
    assertIsSignedName(contextFunction.signedName, "contextFunction", "(scala.Function1):scala.Unit")
  }

  testWithContext("inherited type member, same tasty") {
    val SubClass = ctx.findStaticClass("inheritance.SameTasty.Sub")
    val foo3 = SubClass.getDecl(name"foo3").get.asTerm
    assertIsSignedName(foo3.signedName, "foo3", "():scala.Int")

    val SubWithMixinClass = ctx.findStaticClass("inheritance.SameTasty.SubWithMixin")
    val bar3 = SubWithMixinClass.getDecl(name"bar3").get.asTerm
    assertIsSignedName(bar3.signedName, "bar3", "():scala.Int")
  }

  testWithContext("inherited type member, cross tasty") {
    val SubClass = ctx.findTopLevelClass("inheritance.crosstasty.Sub")
    val foo3 = SubClass.getDecl(name"foo3").get.asTerm
    assertIsSignedName(foo3.signedName, "foo3", "():scala.Int")

    val SubWithMixinClass = ctx.findTopLevelClass("inheritance.crosstasty.SubWithMixin")
    val bar3 = SubWithMixinClass.getDecl(name"bar3").get.asTerm
    assertIsSignedName(bar3.signedName, "bar3", "():scala.Int")
  }

  testWithContext("case class copy method") {
    val CaseClass = ctx.findTopLevelClass("synthetics.CaseClass")
    val copy = CaseClass.getDecl(name"copy").get.asTerm
    assertIsSignedName(copy.signedName, "copy", "(java.lang.String):synthetics.CaseClass")
  }

end SignatureSuite
