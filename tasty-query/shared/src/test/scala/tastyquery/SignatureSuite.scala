package tastyquery

import munit.Location

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import TestUtils.*

class SignatureSuite extends UnrestrictedUnpicklingSuite:

  def assertIsSignedName(actual: Name, simpleName: String, signature: String)(using Location): Unit =
    assertIsSignedName(actual, simpleName, signature, simpleName)

  def assertIsSignedName(actual: Name, simpleName: String, signature: String, targetName: String)(
    using Location
  ): Unit =
    actual match
      case name: SignedName =>
        assert(clue(name.underlying) == clue(termName(simpleName)))
        assert(clue(name.sig.toString) == clue(signature))
        assert(clue(name.target) == clue(termName(targetName)))
      case _ =>
        fail("not a Signed name", clues(actual))
  end assertIsSignedName

  def assertNotSignedName(actual: Name)(using Location): Unit =
    assert(!clue(actual).isInstanceOf[SignedName])

  testWithContext("java.lang.String") {
    val StringClass = defn.StringClass

    val charAt = StringClass.findNonOverloadedDecl(name"charAt")
    assertIsSignedName(charAt.signedName, "charAt", "(scala.Int):scala.Char")

    val contains = StringClass.findNonOverloadedDecl(name"contains")
    assertIsSignedName(contains.signedName, "contains", "(java.lang.CharSequence):scala.Boolean")

    val length = StringClass.findNonOverloadedDecl(name"length")
    assertIsSignedName(length.signedName, "length", "():scala.Int")
  }

  testWithContext("GenericClass") {
    val GenericClass = ctx.findTopLevelClass("simple_trees.GenericClass")

    val field = GenericClass.findDecl(name"field")
    assertNotSignedName(field.signedName)

    val getter = GenericClass.findDecl(name"getter")
    assertIsSignedName(getter.signedName, "getter", "():java.lang.Object")

    val method = GenericClass.findNonOverloadedDecl(name"method")
    assertIsSignedName(method.signedName, "method", "(java.lang.Object):java.lang.Object")
  }

  testWithContext("GenericMethod") {
    val GenericMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")

    val identity = GenericMethod.findNonOverloadedDecl(name"identity")
    assertIsSignedName(identity.signedName, "identity", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("targetName") {
    val GenericMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")

    val identity = GenericMethod.findNonOverloadedDecl(name"otherIdentity")
    assertIsSignedName(identity.signedName, "otherIdentity", "(1,java.lang.Object):java.lang.Object", "otherName")
  }

  testWithContext("JavaInnerClass") {
    val TreeMap = ctx.findTopLevelClass("java.util.TreeMap")

    val getFirstEntry = TreeMap.findNonOverloadedDecl(name"getFirstEntry")
    assertIsSignedName(getFirstEntry.signedName, "getFirstEntry", "():java.util.TreeMap.Entry")
  }

  testWithContext("RichInt") {
    val RichInt = ctx.findTopLevelClass("scala.runtime.RichInt")

    val toHexString = RichInt.findDecl(name"toHexString")
    assertIsSignedName(toHexString.signedName, "toHexString", "():java.lang.String")
  }

  testWithContext("Product") {
    val Product = ctx.findTopLevelClass("scala.Product")

    val productIterator = Product.findDecl(name"productIterator")
    assertIsSignedName(productIterator.signedName, "productIterator", "():scala.collection.Iterator")
  }

  testWithContext("with type") {
    val RefinedTypeTree = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val andType = RefinedTypeTree.findNonOverloadedDecl(name"andType")
    intercept[UnsupportedOperationException](andType.signedName)
  }

  testWithContext("array types") {
    val TypeRefIn = ctx.findTopLevelClass("simple_trees.TypeRefIn")

    // TODO The erasure is not actually correct here, but at least we don't crash

    val withArray = TypeRefIn.findNonOverloadedDecl(name"withArray")
    assertIsSignedName(withArray.signedName, "withArray", "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtype = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtype")
    assertIsSignedName(withArrayOfSubtype.signedName, "withArrayOfSubtype", "(1,java.lang.Object):scala.Unit")

    val withArrayAnyRef = TypeRefIn.findNonOverloadedDecl(name"withArrayAnyRef")
    assertIsSignedName(withArrayAnyRef.signedName, "withArrayAnyRef", "(1,java.lang.Object[]):scala.Unit")

    val withArrayOfSubtypeAnyRef = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeAnyRef")
    assertIsSignedName(
      withArrayOfSubtypeAnyRef.signedName,
      "withArrayOfSubtypeAnyRef",
      "(1,java.lang.Object[]):scala.Unit"
    )

    val withArrayAnyVal = TypeRefIn.findNonOverloadedDecl(name"withArrayAnyVal")
    assertIsSignedName(withArrayAnyVal.signedName, "withArrayAnyVal", "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtypeAnyVal = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeAnyVal")
    assertIsSignedName(
      withArrayOfSubtypeAnyVal.signedName,
      "withArrayOfSubtypeAnyVal",
      "(1,java.lang.Object):scala.Unit"
    )

    val withArrayList = TypeRefIn.findNonOverloadedDecl(name"withArrayList")
    assertIsSignedName(withArrayList.signedName, "withArrayList", "(1,scala.collection.immutable.List[]):scala.Unit")

    val withArrayOfSubtypeList = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeList")
    assertIsSignedName(
      withArrayOfSubtypeList.signedName,
      "withArrayOfSubtypeList",
      "(1,scala.collection.immutable.List[]):scala.Unit"
    )
  }

  testWithContext("type-member") {
    val TypeMember = ctx.findTopLevelClass("simple_trees.TypeMember")

    val mTypeAlias = TypeMember.findNonOverloadedDecl(name"mTypeAlias")
    assertIsSignedName(mTypeAlias.signedName, "mTypeAlias", "(scala.Int):scala.Int")

    val mAbstractType = TypeMember.findNonOverloadedDecl(name"mAbstractType")
    assertIsSignedName(mAbstractType.signedName, "mAbstractType", "(java.lang.Object):java.lang.Object")

    val mAbstractTypeWithBounds = TypeMember.findNonOverloadedDecl(name"mAbstractTypeWithBounds")
    assertIsSignedName(mAbstractTypeWithBounds.signedName, "mAbstractTypeWithBounds", "(scala.Product):scala.Product")

    val mOpaque = TypeMember.findNonOverloadedDecl(name"mOpaque")
    assertIsSignedName(mOpaque.signedName, "mOpaque", "(scala.Int):scala.Int")

    val mOpaqueWithBounds = TypeMember.findNonOverloadedDecl(name"mOpaqueWithBounds")
    assertIsSignedName(mOpaqueWithBounds.signedName, "mOpaqueWithBounds", "(scala.Null):scala.Null")
  }

  testWithContext("scala2-case-class-varargs") {
    val StringContext = ctx.findTopLevelClass("scala.StringContext")

    val parts = StringContext.findDecl(name"parts")
    assertIsSignedName(parts.signedName, "parts", "():scala.collection.immutable.Seq")
  }

  testWithContext("scala2-method-byname") {
    val StringContext = ctx.findTopLevelClass("scala.Option")

    val getOrElse = StringContext.findNonOverloadedDecl(name"getOrElse")
    assertIsSignedName(getOrElse.signedName, "getOrElse", "(1,scala.Function0):java.lang.Object")
  }

  testWithContext("scala2-existential-type") {
    val ClassTag = ctx.findTopLevelModuleClass("scala.reflect.ClassTag")

    val apply = ClassTag.findNonOverloadedDecl(name"apply")
    assertIsSignedName(apply.signedName, "apply", "(1,java.lang.Class):scala.reflect.ClassTag")
  }

  testWithContext("iarray") {
    val IArraySig = ctx.findTopLevelClass("simple_trees.IArraySig")

    val from = IArraySig.findNonOverloadedDecl(name"from")
    assertIsSignedName(from.signedName, "from", "():java.lang.String[]")
  }

  testWithContext("value-class-arrayOps-generic") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val genericArrayOps = MyArrayOps.findNonOverloadedDecl(name"genericArrayOps")
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("value-class-arrayOps-int") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val intArrayOps = MyArrayOps.findNonOverloadedDecl(name"intArrayOps")
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-generic") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val genericArrayOps = Predef.findNonOverloadedDecl(name"genericArrayOps")
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-int") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val intArrayOps = Predef.findNonOverloadedDecl(name"intArrayOps")
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("value-class-monomorphic") {
    val MyFlags = ctx.findTopLevelClass("inheritance.MyFlags")
    val merge = MyFlags.findNonOverloadedDecl(name"merge")
    assertIsSignedName(merge.signedName, "merge", "(scala.Long):scala.Long")
  }

  testWithContext("value-class-monomorphic-arrayOf") {
    val MyFlags = ctx.findTopLevelModuleClass("inheritance.MyFlags")
    val mergeAll = MyFlags.findNonOverloadedDecl(name"mergeAll")
    assertIsSignedName(mergeAll.signedName, "mergeAll", "(inheritance.MyFlags[]):scala.Long")
  }

  testWithContext("value-class-polymorphic-arrayOf") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val arrayOfIntArrayOps = MyArrayOps.findNonOverloadedDecl(name"arrayOfIntArrayOps")
    assertIsSignedName(arrayOfIntArrayOps.signedName, "arrayOfIntArrayOps", "(scala.Int[][]):inheritance.MyArrayOps[]")
  }

  testWithContext("package-ref-from-tasty") {
    val LazyVals = ctx.findTopLevelModuleClass("javacompat.LazyVals")
    val getOffsetStatic = LazyVals.findNonOverloadedDecl(name"getOffsetStatic")
    assertIsSignedName(getOffsetStatic.signedName, "getOffsetStatic", "(java.lang.reflect.Field):scala.Long")
  }

  testWithContext("Scala 3 special function types") {
    val SpecialFunctionTypes = ctx.findTopLevelClass("simple_trees.SpecialFunctionTypes")
    val contextFunction = SpecialFunctionTypes.findNonOverloadedDecl(name"contextFunction")
    assertIsSignedName(contextFunction.signedName, "contextFunction", "(scala.Function1):scala.Unit")
  }

  testWithContext("inherited type member, same tasty") {
    val SubClass = ctx.findStaticClass("inheritance.SameTasty.Sub")
    val foo3 = SubClass.findDecl(name"foo3")
    assertIsSignedName(foo3.signedName, "foo3", "():scala.Int")

    val SubWithMixinClass = ctx.findStaticClass("inheritance.SameTasty.SubWithMixin")
    val bar3 = SubWithMixinClass.findDecl(name"bar3")
    assertIsSignedName(bar3.signedName, "bar3", "():scala.Int")
  }

  testWithContext("inherited type member, cross tasty") {
    val SubClass = ctx.findTopLevelClass("inheritance.crosstasty.Sub")
    val foo3 = SubClass.findDecl(name"foo3")
    assertIsSignedName(foo3.signedName, "foo3", "():scala.Int")

    val SubWithMixinClass = ctx.findTopLevelClass("inheritance.crosstasty.SubWithMixin")
    val bar3 = SubWithMixinClass.findDecl(name"bar3")
    assertIsSignedName(bar3.signedName, "bar3", "():scala.Int")
  }

  testWithContext("case class copy method") {
    val CaseClass = ctx.findTopLevelClass("synthetics.CaseClass")
    val copy = CaseClass.findNonOverloadedDecl(name"copy")
    assertIsSignedName(copy.signedName, "copy", "(java.lang.String):synthetics.CaseClass")
  }

  testWithContext("union types") {
    val UnionType = ctx.findTopLevelClass("simple_trees.UnionType")

    val argWithOrType = UnionType.findNonOverloadedDecl(name"argWithOrType")
    assertIsSignedName(argWithOrType.signedName, "argWithOrType", "(java.lang.Object):java.lang.Object")

    val classesOrType = UnionType.findNonOverloadedDecl(name"classesOrType")
    assertIsSignedName(
      classesOrType.signedName,
      "classesOrType",
      "(scala.collection.generic.DefaultSerializable):scala.collection.immutable.Seq"
    )
  }

end SignatureSuite
