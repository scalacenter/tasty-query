package tastyquery

import tastyquery.Contexts.Context
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.*
import tastyquery.ast.Types.*

import Paths.*
import tastyquery.ast.Signature
import munit.Location
import tastyquery.ast.ParamSig
import tastyquery.ast.TermSig

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

    val charAt = StringClass.getDecl(name"charAt").get
    assertIsSignedName(charAt.signedName, "charAt", "(scala.Int):scala.Char")

    val contains = StringClass.getDecl(name"contains").get
    assertIsSignedName(contains.signedName, "contains", "(java.lang.CharSequence):scala.Boolean")

    val length = StringClass.getDecl(name"length").get
    assertIsSignedName(length.signedName, "length", "():scala.Int")
  }

  testWithContext("GenericClass") {
    val GenericClass = resolve(name"simple_trees" / tname"GenericClass").asClass

    val field = GenericClass.getDecl(name"field").get
    assertNotSignedName(field.signedName)

    val getter = GenericClass.getDecl(name"getter").get
    assertIsSignedName(getter.signedName, "getter", "():scala.Any")

    val method = GenericClass.getDecl(name"method").get
    assertIsSignedName(method.signedName, "method", "(scala.Any):scala.Any")
  }

  testWithContext("GenericMethod") {
    val GenericMethod = resolve(name"simple_trees" / tname"GenericMethod").asClass

    val identity = GenericMethod.getDecl(name"identity").get
    assertIsSignedName(identity.signedName, "identity", "(1,scala.Any):scala.Any")
  }

  testWithContext("RichInt") {
    val RichInt = resolve(name"scala" / name"runtime" / tname"RichInt").asClass

    val toHexString = RichInt.getDecl(name"toHexString").get
    assertIsSignedName(toHexString.signedName, "toHexString", "():java.lang.String")
  }

  testWithContext("Product") {
    val Product = resolve(name"scala" / tname"Product").asClass

    val productIterator = Product.getDecl(name"productIterator").get
    assertIsSignedName(productIterator.signedName, "productIterator", "():scala.collection.Iterator")
  }

  testWithContext("with type") {
    val RefinedTypeTree = resolve(name"simple_trees" / tname"RefinedTypeTree").asClass

    val andType = RefinedTypeTree.getDecl(name"andType").get
    assertIsSignedName(andType.signedName, "andType", "():simple_trees.RefinedTypeTree.AndTypeA")
  }

  testWithContext("array types") {
    val TypeRefIn = resolve(name"simple_trees" / tname"TypeRefIn").asClass

    // TODO The erasure is not actually correct here, but at least we don't crash

    val withArray = TypeRefIn.getDecl(name"withArray").get
    assertIsSignedName(withArray.signedName, "withArray", "(1,scala.Any[]):scala.Unit")

    val withArrayOfSubtype = TypeRefIn.getDecl(name"withArrayOfSubtype").get
    assertIsSignedName(withArrayOfSubtype.signedName, "withArrayOfSubtype", "(1,scala.Any[]):scala.Unit")
  }

  testWithContext("type-member") {
    val TypeMember = resolve(name"simple_trees" / tname"TypeMember").asClass

    val mTypeAlias = TypeMember.getDecl(name"mTypeAlias").get
    assertIsSignedName(mTypeAlias.signedName, "mTypeAlias", "(scala.Int):scala.Int")

    val mAbstractType = TypeMember.getDecl(name"mAbstractType").get
    assertIsSignedName(mAbstractType.signedName, "mAbstractType", "(scala.Any):scala.Any")

    val mAbstractTypeWithBounds = TypeMember.getDecl(name"mAbstractTypeWithBounds").get
    assertIsSignedName(mAbstractTypeWithBounds.signedName, "mAbstractTypeWithBounds", "(scala.Product):scala.Product")

    val mOpaque = TypeMember.getDecl(name"mOpaque").get
    assertIsSignedName(mOpaque.signedName, "mOpaque", "(scala.Int):scala.Int")

    val mOpaqueWithBounds = TypeMember.getDecl(name"mOpaqueWithBounds").get
    assertIsSignedName(mOpaqueWithBounds.signedName, "mOpaqueWithBounds", "(scala.Null):scala.Null")
  }

end SignatureSuite
