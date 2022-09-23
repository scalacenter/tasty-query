package tastyquery

import tastyquery.Contexts.Context
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import Paths.*
import tastyquery.Signature
import munit.Location
import tastyquery.ParamSig
import tastyquery.TermSig

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
    val StringClass = resolve(name"java" / name"lang" / tname"String").asClass

    val charAt = StringClass.getDecl(name"charAt").get.asTerm
    assertIsSignedName(charAt.signedName, "charAt", "(scala.Int):scala.Char")

    val contains = StringClass.getDecl(name"contains").get.asTerm
    assertIsSignedName(contains.signedName, "contains", "(java.lang.CharSequence):scala.Boolean")

    val length = StringClass.getDecl(name"length").get.asTerm
    assertIsSignedName(length.signedName, "length", "():scala.Int")
  }

  testWithContext("GenericClass") {
    val GenericClass = resolve(name"simple_trees" / tname"GenericClass").asClass

    val field = GenericClass.getDecl(name"field").get.asTerm
    assertNotSignedName(field.signedName)

    val getter = GenericClass.getDecl(name"getter").get.asTerm
    assertIsSignedName(getter.signedName, "getter", "():java.lang.Object")

    val method = GenericClass.getDecl(name"method").get.asTerm
    assertIsSignedName(method.signedName, "method", "(java.lang.Object):java.lang.Object")
  }

  testWithContext("GenericMethod") {
    val GenericMethod = resolve(name"simple_trees" / tname"GenericMethod").asClass

    val identity = GenericMethod.getDecl(name"identity").get.asTerm
    assertIsSignedName(identity.signedName, "identity", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("RichInt") {
    val RichInt = resolve(name"scala" / name"runtime" / tname"RichInt").asClass

    val toHexString = RichInt.getDecl(name"toHexString").get.asTerm
    assertIsSignedName(toHexString.signedName, "toHexString", "():java.lang.String")
  }

  testWithContext("Product") {
    val Product = resolve(name"scala" / tname"Product").asClass

    val productIterator = Product.getDecl(name"productIterator").get.asTerm
    assertIsSignedName(productIterator.signedName, "productIterator", "():scala.collection.Iterator")
  }

  testWithContext("with type") {
    val RefinedTypeTree = resolve(name"simple_trees" / tname"RefinedTypeTree").asClass

    val andType = RefinedTypeTree.getDecl(name"andType").get.asTerm
    assertIsSignedName(andType.signedName, "andType", "():simple_trees.RefinedTypeTree.AndTypeA")
  }

  testWithContext("array types") {
    val TypeRefIn = resolve(name"simple_trees" / tname"TypeRefIn").asClass

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
    val TypeMember = resolve(name"simple_trees" / tname"TypeMember").asClass

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
    val StringContext = resolve(name"scala" / tname"StringContext").asClass

    val parts = StringContext.getDecl(name"parts").get.asTerm
    assertIsSignedName(parts.signedName, "parts", "():scala.collection.immutable.Seq")
  }

  testWithContext("scala2-method-byname") {
    val StringContext = resolve(name"scala" / tname"Option").asClass

    val getOrElse = StringContext.getDecl(name"getOrElse").get.asTerm
    assertIsSignedName(getOrElse.signedName, "getOrElse", "(1,scala.Function0):java.lang.Object")
  }

  testWithContext("scala2-existential-type") {
    val ClassTag = resolve(name"scala" / name"reflect" / tname"ClassTag" / obj).asClass

    val apply = ClassTag.getDecl(name"apply").get.asTerm
    assertIsSignedName(apply.signedName, "apply", "(1,java.lang.Class):scala.reflect.ClassTag")
  }

  testWithContext("iarray") {
    val IArraySig = resolve(name"simple_trees" / tname"IArraySig").asClass

    val from = IArraySig.getDecl(name"from").get.asTerm
    assertIsSignedName(from.signedName, "from", "():java.lang.String[]")
  }

  testWithContext("value-class-arrayOps-generic") {
    val MyArrayOps = resolve(name"inheritance" / tname"MyArrayOps" / obj).asClass
    val genericArrayOps = MyArrayOps.getDecl(name"genericArrayOps").get.asTerm
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("value-class-arrayOps-int") {
    val MyArrayOps = resolve(name"inheritance" / tname"MyArrayOps" / obj).asClass
    val intArrayOps = MyArrayOps.getDecl(name"intArrayOps").get.asTerm
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-generic") {
    val Predef = resolve(name"scala" / tname"Predef" / obj).asClass
    val genericArrayOps = Predef.getDecl(name"genericArrayOps").get.asTerm
    assertIsSignedName(genericArrayOps.signedName, "genericArrayOps", "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-int") {
    val Predef = resolve(name"scala" / tname"Predef" / obj).asClass
    val intArrayOps = Predef.getDecl(name"intArrayOps").get.asTerm
    assertIsSignedName(intArrayOps.signedName, "intArrayOps", "(scala.Int[]):java.lang.Object")
  }

  testWithContext("value-class-monomorphic") {
    val MyFlags = resolve(name"inheritance" / tname"MyFlags").asClass
    val merge = MyFlags.getDecl(name"merge").get.asTerm
    assertIsSignedName(merge.signedName, "merge", "(scala.Long):scala.Long")
  }

  testWithContext("value-class-monomorphic-arrayOf") {
    val MyFlags = resolve(name"inheritance" / tname"MyFlags" / obj).asClass
    val mergeAll = MyFlags.getDecl(name"mergeAll").get.asTerm
    assertIsSignedName(mergeAll.signedName, "mergeAll", "(inheritance.MyFlags[]):scala.Long")
  }

  testWithContext("value-class-polymorphic-arrayOf") {
    val MyArrayOps = resolve(name"inheritance" / tname"MyArrayOps" / obj).asClass
    val arrayOfIntArrayOps = MyArrayOps.getDecl(name"arrayOfIntArrayOps").get.asTerm
    assertIsSignedName(arrayOfIntArrayOps.signedName, "arrayOfIntArrayOps", "(scala.Int[][]):inheritance.MyArrayOps[]")
  }

end SignatureSuite
