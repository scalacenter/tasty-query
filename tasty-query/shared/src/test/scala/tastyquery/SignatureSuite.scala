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

  def assertSigned(sym: TermSymbol, expectedSignature: String)(using Context, Location): Unit =
    assertSigned(sym, expectedSignature, sym.name)

  def assertSigned(sym: TermSymbol, expectedSignature: String, expectedTargetName: TermName)(
    using Context,
    Location
  ): Unit =
    val actualSignature = sym.signature
    assert(clue(actualSignature.toString) == clue(expectedSignature))
    assert(clue(sym.targetName) == clue(expectedTargetName))
    assert(clue(sym.signedName) == clue(SignedName(sym.name, actualSignature, expectedTargetName)))
  end assertSigned

  def assertNotSigned(sym: TermSymbol, expectedSignature: String)(using Context, Location): Unit =
    assertNotSigned(sym, expectedSignature, sym.name)

  def assertNotSigned(sym: TermSymbol, expectedSignature: String, expectedTargetName: TermName)(
    using Context,
    Location
  ): Unit =
    val actualSignature = sym.signature
    assert(clue(actualSignature.toString) == clue(expectedSignature))
    assert(clue(sym.targetName) == clue(expectedTargetName))
    assert(clue(sym.signedName) == clue(sym.name))
  end assertNotSigned

  testWithContext("java.lang.String") {
    val StringClass = defn.StringClass

    val charAt = StringClass.findNonOverloadedDecl(name"charAt")
    assertSigned(charAt, "(scala.Int):scala.Char")

    val contains = StringClass.findNonOverloadedDecl(name"contains")
    assertSigned(contains, "(java.lang.CharSequence):scala.Boolean")

    val length = StringClass.findNonOverloadedDecl(name"length")
    assertSigned(length, "():scala.Int")
  }

  testWithContext("Specials") {
    val equals = defn.Any_equals
    assertSigned(equals, "(java.lang.Object):scala.Boolean")
  }

  testWithContext("GenericClass") {
    val GenericClass = ctx.findTopLevelClass("simple_trees.GenericClass")

    val field = GenericClass.findDecl(name"field")
    assertNotSigned(field, "():java.lang.Object")

    val getter = GenericClass.findDecl(name"getter")
    assertNotSigned(getter, "():java.lang.Object")

    val method = GenericClass.findNonOverloadedDecl(name"method")
    assertSigned(method, "(java.lang.Object):java.lang.Object")
  }

  testWithContext("GenericMethod") {
    val GenericMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")

    val identity = GenericMethod.findNonOverloadedDecl(name"identity")
    assertSigned(identity, "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("targetName") {
    val GenericMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")

    val identity = GenericMethod.findNonOverloadedDecl(name"otherIdentity")
    assertSigned(identity, "(1,java.lang.Object):java.lang.Object", termName("otherName"))
  }

  testWithContext("JavaInnerClass") {
    val TreeMap = ctx.findTopLevelClass("java.util.TreeMap")

    val getFirstEntry = TreeMap.findNonOverloadedDecl(name"getFirstEntry")
    assertSigned(getFirstEntry, "():java.util.TreeMap.Entry")
  }

  testWithContext("RichInt") {
    val RichInt = ctx.findTopLevelClass("scala.runtime.RichInt")

    val toHexString = RichInt.findDecl(name"toHexString")
    assertNotSigned(toHexString, "():java.lang.String")
  }

  testWithContext("Product") {
    val Product = ctx.findTopLevelClass("scala.Product")

    val productIterator = Product.findDecl(name"productIterator")
    assertNotSigned(productIterator, "():scala.collection.Iterator")
  }

  testWithContext("empty package") {
    val ClassInEmptyPackage = ctx.findTopLevelClass("ClassInEmptyPackage")
    assert(ClassInEmptyPackage.owner == defn.EmptyPackage)

    val meth = ClassInEmptyPackage.findNonOverloadedDecl(termName("meth"))
    assertSigned(meth, "(ClassInEmptyPackage):scala.Int")
  }

  testWithContext("with type") {
    val RefinedTypeTree = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val andType = RefinedTypeTree.findNonOverloadedDecl(name"andType")
    intercept[UnsupportedOperationException](andType.signedName)
  }

  testWithContext("array types") {
    val TypeRefIn = ctx.findTopLevelClass("simple_trees.TypeRefIn")

    val withArray = TypeRefIn.findNonOverloadedDecl(name"withArray")
    assertSigned(withArray, "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtype = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtype")
    assertSigned(withArrayOfSubtype, "(1,java.lang.Object):scala.Unit")

    val withArrayAnyRef = TypeRefIn.findNonOverloadedDecl(name"withArrayAnyRef")
    assertSigned(withArrayAnyRef, "(1,java.lang.Object[]):scala.Unit")

    val withArrayOfSubtypeAnyRef = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeAnyRef")
    assertSigned(withArrayOfSubtypeAnyRef, "(1,java.lang.Object[]):scala.Unit")

    val withArrayAnyVal = TypeRefIn.findNonOverloadedDecl(name"withArrayAnyVal")
    assertSigned(withArrayAnyVal, "(1,java.lang.Object):scala.Unit")

    val withArrayOfSubtypeAnyVal = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeAnyVal")
    assertSigned(withArrayOfSubtypeAnyVal, "(1,java.lang.Object):scala.Unit")

    val withArrayList = TypeRefIn.findNonOverloadedDecl(name"withArrayList")
    assertSigned(withArrayList, "(1,scala.collection.immutable.List[]):scala.Unit")

    val withArrayOfSubtypeList = TypeRefIn.findNonOverloadedDecl(name"withArrayOfSubtypeList")
    assertSigned(withArrayOfSubtypeList, "(1,scala.collection.immutable.List[]):scala.Unit")

    val withArrayExactAny = TypeRefIn.findNonOverloadedDecl(name"withArrayExactAny")
    assertSigned(withArrayExactAny, "(java.lang.Object[]):scala.Unit")

    val withArrayExactAnyRef = TypeRefIn.findNonOverloadedDecl(name"withArrayExactAnyRef")
    assertSigned(withArrayExactAnyRef, "(java.lang.Object[]):scala.Unit")

    val withArrayExactAnyVal = TypeRefIn.findNonOverloadedDecl(name"withArrayExactAnyVal")
    assertSigned(withArrayExactAnyVal, "(java.lang.Object[]):scala.Unit")
  }

  testWithContext("type-member") {
    val TypeMember = ctx.findTopLevelClass("simple_trees.TypeMember")

    val mTypeAlias = TypeMember.findNonOverloadedDecl(name"mTypeAlias")
    assertSigned(mTypeAlias, "(scala.Int):scala.Int")

    val mAbstractType = TypeMember.findNonOverloadedDecl(name"mAbstractType")
    assertSigned(mAbstractType, "(java.lang.Object):java.lang.Object")

    val mAbstractTypeWithBounds = TypeMember.findNonOverloadedDecl(name"mAbstractTypeWithBounds")
    assertSigned(mAbstractTypeWithBounds, "(scala.Product):scala.Product")

    val mOpaque = TypeMember.findNonOverloadedDecl(name"mOpaque")
    assertSigned(mOpaque, "(scala.Int):scala.Int")

    val mOpaqueWithBounds = TypeMember.findNonOverloadedDecl(name"mOpaqueWithBounds")
    assertSigned(mOpaqueWithBounds, "(scala.Null):scala.Null")
  }

  testWithContext("scala2-case-class-varargs") {
    val StringContext = ctx.findTopLevelClass("scala.StringContext")

    val parts = StringContext.findDecl(name"parts")
    assertNotSigned(parts, "():scala.collection.immutable.Seq")
  }

  testWithContext("scala2-method-byname") {
    val StringContext = ctx.findTopLevelClass("scala.Option")

    val getOrElse = StringContext.findNonOverloadedDecl(name"getOrElse")
    assertSigned(getOrElse, "(1,scala.Function0):java.lang.Object")
  }

  testWithContext("scala2-existential-type") {
    val ClassTag = ctx.findTopLevelModuleClass("scala.reflect.ClassTag")

    val apply = ClassTag.findNonOverloadedDecl(name"apply")
    assertSigned(apply, "(1,java.lang.Class):scala.reflect.ClassTag")
  }

  testWithContext("iarray") {
    val IArraySig = ctx.findTopLevelClass("simple_trees.IArraySig")

    val from = IArraySig.findNonOverloadedDecl(name"from")
    assertSigned(from, "():java.lang.String[]")
  }

  testWithContext("value-class-arrayOps-generic") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val genericArrayOps = MyArrayOps.findNonOverloadedDecl(name"genericArrayOps")
    assertSigned(genericArrayOps, "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("value-class-arrayOps-int") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val intArrayOps = MyArrayOps.findNonOverloadedDecl(name"intArrayOps")
    assertSigned(intArrayOps, "(scala.Int[]):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-generic") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val genericArrayOps = Predef.findNonOverloadedDecl(name"genericArrayOps")
    assertSigned(genericArrayOps, "(1,java.lang.Object):java.lang.Object")
  }

  testWithContext("scala2-value-class-arrayOps-int") {
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    val intArrayOps = Predef.findNonOverloadedDecl(name"intArrayOps")
    assertSigned(intArrayOps, "(scala.Int[]):java.lang.Object")
  }

  testWithContext("value-class-monomorphic") {
    val MyFlags = ctx.findTopLevelClass("inheritance.MyFlags")
    val merge = MyFlags.findNonOverloadedDecl(name"merge")
    assertSigned(merge, "(scala.Long):scala.Long")
  }

  testWithContext("value-class-monomorphic-arrayOf") {
    val MyFlags = ctx.findTopLevelModuleClass("inheritance.MyFlags")
    val mergeAll = MyFlags.findNonOverloadedDecl(name"mergeAll")
    assertSigned(mergeAll, "(inheritance.MyFlags[]):scala.Long")
  }

  testWithContext("value-class-polymorphic-arrayOf") {
    val MyArrayOps = ctx.findTopLevelModuleClass("inheritance.MyArrayOps")
    val arrayOfIntArrayOps = MyArrayOps.findNonOverloadedDecl(name"arrayOfIntArrayOps")
    assertSigned(arrayOfIntArrayOps, "(scala.Int[][]):inheritance.MyArrayOps[]")
  }

  testWithContext("package-ref-from-tasty") {
    val LazyVals = ctx.findTopLevelModuleClass("javacompat.LazyVals")
    val getOffsetStatic = LazyVals.findNonOverloadedDecl(name"getOffsetStatic")
    assertSigned(getOffsetStatic, "(java.lang.reflect.Field):scala.Long")
  }

  testWithContext("Scala 3 special function types") {
    val SpecialFunctionTypes = ctx.findTopLevelClass("simple_trees.SpecialFunctionTypes")
    val contextFunction = SpecialFunctionTypes.findNonOverloadedDecl(name"contextFunction")
    assertSigned(contextFunction, "(scala.Function1):scala.Unit")
  }

  testWithContext("inherited type member, same tasty") {
    val SubClass = ctx.findStaticClass("inheritance.SameTasty.Sub")
    val foo3 = SubClass.findDecl(name"foo3")
    assertNotSigned(foo3, "():scala.Int")

    val SubWithMixinClass = ctx.findStaticClass("inheritance.SameTasty.SubWithMixin")
    val bar3 = SubWithMixinClass.findDecl(name"bar3")
    assertNotSigned(bar3, "():scala.Int")
  }

  testWithContext("inherited type member, cross tasty") {
    val SubClass = ctx.findTopLevelClass("inheritance.crosstasty.Sub")
    val foo3 = SubClass.findDecl(name"foo3")
    assertNotSigned(foo3, "():scala.Int")

    val SubWithMixinClass = ctx.findTopLevelClass("inheritance.crosstasty.SubWithMixin")
    val bar3 = SubWithMixinClass.findDecl(name"bar3")
    assertNotSigned(bar3, "():scala.Int")
  }

  testWithContext("case class copy method") {
    val CaseClass = ctx.findTopLevelClass("synthetics.CaseClass")
    val copy = CaseClass.findNonOverloadedDecl(name"copy")
    assertSigned(copy, "(java.lang.String):synthetics.CaseClass")
  }

  testWithContext("union types") {
    val UnionType = ctx.findTopLevelClass("simple_trees.UnionType")

    val argWithOrType = UnionType.findNonOverloadedDecl(name"argWithOrType")
    assertSigned(argWithOrType, "(java.lang.Object):java.lang.Object")

    val classesOrType = UnionType.findNonOverloadedDecl(name"classesOrType")
    assertSigned(classesOrType, "(scala.collection.generic.DefaultSerializable):scala.collection.immutable.Seq")

    val arrayOfUnion = UnionType.findNonOverloadedDecl(name"arrayOfUnion")
    assertSigned(arrayOfUnion, "(java.lang.Object[]):java.lang.Object[]")
  }

  testWithContext("refined types") {
    val RefinedTypeTree = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val sigRefined = RefinedTypeTree.findNonOverloadedDecl(name"sigRefined")
    assertSigned(sigRefined, "():simple_trees.TypeMember")

    val foo = RefinedTypeTree.findNonOverloadedDecl(name"foo")
    assertSigned(foo, "(simple_trees.RefinedTypeTree.A):scala.Int")

    val innerRef = RefinedTypeTree.findNonOverloadedDecl(name"innerRef")
    assertSigned(innerRef, "(simple_trees.RefinedTypeTree.C):scala.Int")

    val innerRefVal = RefinedTypeTree.findNonOverloadedDecl(name"innerRefVal")
    assertNotSigned(innerRefVal, "():simple_trees.RefinedTypeTree.C")
  }

  testWithContext("match types") {
    val MatchType = ctx.findTopLevelClass("simple_trees.MatchType")

    val unboundUnreducibleSig = MatchType.findNonOverloadedDecl(termName("unboundUnreducibleSig"))
    assertSigned(unboundUnreducibleSig, "(1,java.lang.Object):java.lang.Object")

    val unboundReducibleSig = MatchType.findNonOverloadedDecl(termName("unboundReducibleSig"))
    assertSigned(unboundReducibleSig, "(1,scala.Int):java.lang.String")

    val boundUnreducibleSig = MatchType.findNonOverloadedDecl(termName("boundUnreducibleSig"))
    assertSigned(boundUnreducibleSig, "(1,java.lang.Object):scala.Product")

    val boundReducibleSig = MatchType.findNonOverloadedDecl(termName("boundReducibleSig"))
    assertSigned(boundReducibleSig, "(1,scala.Int):scala.Some")

    // this one is suspicious, but it is what dotc does (I expected `Object` instead of `Object[]`)
    val arrayOfUnboundUnreducibleSig = MatchType.findNonOverloadedDecl(termName("arrayOfUnboundUnreducibleSig"))
    assertSigned(arrayOfUnboundUnreducibleSig, "(1,java.lang.Object):java.lang.Object[]")

    val arrayOfUnboundReducibleSig = MatchType.findNonOverloadedDecl(termName("arrayOfUnboundReducibleSig"))
    assertSigned(arrayOfUnboundReducibleSig, "(1,scala.Int):java.lang.String[]")

    val arrayOfBoundUnreducibleSig = MatchType.findNonOverloadedDecl(termName("arrayOfBoundUnreducibleSig"))
    assertSigned(arrayOfBoundUnreducibleSig, "(1,java.lang.Object):scala.Product[]")

    val arrayOfBoundReducibleSig = MatchType.findNonOverloadedDecl(termName("arrayOfBoundReducibleSig"))
    assertSigned(arrayOfBoundReducibleSig, "(1,scala.Int):scala.Some[]")
  }

  testWithContext("tuples") {
    val TuplesClass = ctx.findTopLevelClass("simple_trees.Tuples")

    val takeTupleSig = TuplesClass.findNonOverloadedDecl(termName("takeTuple"))
    assertSigned(takeTupleSig, "(scala.Product):scala.Unit")

    val takeNonEmptyTupleSig = TuplesClass.findNonOverloadedDecl(termName("takeNonEmptyTuple"))
    assertSigned(takeNonEmptyTupleSig, "(scala.Product):scala.Unit")

    val takeStarColonSig = TuplesClass.findNonOverloadedDecl(termName("takeStarColon"))
    assertSigned(takeStarColonSig, "(java.lang.Object):scala.Unit")

    val takeEmptyTupleSig = TuplesClass.findNonOverloadedDecl(termName("takeEmptyTuple"))
    assertSigned(takeEmptyTupleSig, "(scala.Tuple$package.EmptyTuple):scala.Unit")
  }

end SignatureSuite
