package tastyquery

import tastyquery.Contexts.BaseContext
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.*
import tastyquery.ast.Types.*

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

class TypeSuite extends BaseUnpicklingSuite(withClasses = true, withStdLib = true, allowDeps = true) {
  import BaseUnpicklingSuite.Decls.*

  def assertIsSymbolWithPath(path: DeclarationPath)(actualSymbol: Symbol)(using BaseContext): Unit = {
    val expectedSymbol = resolve(path)
    assert(actualSymbol eq expectedSymbol, clues(actualSymbol, expectedSymbol))
  }

  extension (tpe: Type | TypeBounds)
    def isWildcard(using BaseContext): Boolean =
      isBounded(_.isNothing, _.isAny)

    def typeOrNone: Type = tpe match
      case tpe: Type       => tpe
      case tpe: TypeBounds => NoType

    def isBounded(lo: Type => Boolean, hi: Type => Boolean)(using BaseContext): Boolean = tpe match
      case tpe: TypeBounds => lo(tpe.low) && hi(tpe.high)
      case _               => false

  extension (tpe: Type)
    def isAny(using BaseContext): Boolean = tpe.isRef(resolve(name"scala" / tname"Any"))

    def isNothing(using BaseContext): Boolean = tpe.isRef(resolve(name"scala" / tname"Nothing"))

    def isIntersectionOf(tpes: (Type => Boolean)*)(using BaseContext): Boolean =
      def parts(tpe: Type, acc: mutable.ListBuffer[Type]): acc.type = tpe match
        case AndType(tp1, tp2) => parts(tp2, parts(tp1, acc))
        case tpe: Type         => acc += tpe
      val all = parts(tpe.widen, mutable.ListBuffer[Type]()).toList
      all.corresponds(tpes)((tpe, test) => test(tpe))

    def isApplied(cls: Type => Boolean, argRefs: Seq[(Type | TypeBounds) => Boolean])(using BaseContext): Boolean =
      tpe.widen match
        case AppliedType(tycon, args) if cls(tycon) =>
          args.corresponds(argRefs)((arg, argRef) => argRef(arg))
        case _ => false

    def isArrayOf(arg: (Type | TypeBounds) => Boolean)(using BaseContext): Boolean =
      isApplied(_.isRef(resolve(name"scala" / tname"Array")), Seq(arg))

  test("apply-recursive") {
    val RecApply = name"simple_trees" / tname"RecApply"

    given BaseContext = getUnpicklingContext(RecApply)

    val gcdSym = resolve(RecApply / name"gcd")
    val NumClass = resolve(RecApply / tname"Num")

    val Some(gcdTree @ _: DefDef) = gcdSym.tree: @unchecked

    var recCallCount = 0

    gcdTree.walkTree { tree =>
      tree match
        case recCall @ Apply(gcdRef @ Select(_, SignedName(SimpleName("gcd"), _, _)), _) =>
          recCallCount += 1

          assert(gcdRef.tpe.isRef(gcdSym), clue(gcdRef))

          assert(recCall.tpe.isRef(NumClass), clue(recCall))
        case _ => ()
    }

    assert(recCallCount == 1)

  }

  test("java.lang-is-not-loaded".fail) {
    getUnpicklingContext(name"java" / name"lang" / tname"String")
  }

  def applyOverloadedTest(name: String)(callMethod: String, paramCls: DeclarationPath)(using munit.Location): Unit =
    test(name) {
      val OverloadedApply = name"simple_trees" / tname"OverloadedApply"

      given BaseContext = getUnpicklingContext(OverloadedApply)

      val callSym = resolve(OverloadedApply / termName(callMethod))
      val Acls = resolve(paramCls)
      val UnitClass = resolve(name"scala" / tname"Unit")

      val Some(callTree @ _: DefDef) = callSym.tree: @unchecked

      var callCount = 0

      callTree.walkTree { tree =>
        tree match
          case app @ Apply(fooRef @ Select(_, SignedName(SimpleName("foo"), _, _)), _) =>
            callCount += 1
            assert(app.tpe.isRef(UnitClass), clue(app)) // todo: resolve overloaded
            val fooSym = fooRef.tpe.termSymbol
            val List(List(aSym), _*) = fooSym.paramSymss: @unchecked
            assert(aSym.declaredType.isRef(Acls), clues(Acls.fullName, aSym.declaredType))
          case _ => ()
      }

      assert(callCount == 1)
    }

  applyOverloadedTest("apply-overloaded-int")("callA", name"scala" / tname"Int")
  applyOverloadedTest("apply-overloaded-gen")("callB", name"simple_trees" / tname"OverloadedApply" / tname"Box")
  applyOverloadedTest("apply-overloaded-nestedObj")(
    "callC",
    name"simple_trees" / tname"OverloadedApply" / objclass"Foo" / name"Bar"
  )
  // applyOverloadedTest("apply-overloaded-arrayObj")("callD", name"scala" / tname"Array") // TODO: re-enable when we add types to scala 2 symbols
  applyOverloadedTest("apply-overloaded-byName")("callE", name"simple_trees" / tname"OverloadedApply" / tname"Num")

  test("typeapply-recursive") {
    val RecApply = name"simple_trees" / tname"RecApply"

    given BaseContext = getUnpicklingContext(RecApply)

    val evalSym = resolve(RecApply / name"eval")
    val ExprClass = resolve(RecApply / tname"Expr")

    val evalParamss = evalSym.paramSymss

    val List(List(Tsym @ _), List(eSym)) = evalParamss: @unchecked

    val Some(evalTree @ _: DefDef) = evalSym.tree: @unchecked

    var recCallCount = 0

    evalTree.walkTree { tree =>
      tree match
        case recCall @ Apply(TypeApply(evalRef @ Select(_, SignedName(SimpleName("eval"), _, _)), _), _) =>
          recCallCount += 1

          assert(evalRef.tpe.isRef(evalSym), clue(evalRef))

          assert(recCall.tpe.isRef(Tsym), clue(recCall))
        case _ => ()
    }

    assert(recCallCount == 4) // 4 calls in the body of `eval`

  }

  test("basic-local-val") {
    val AssignPath = name"simple_trees" / tname"Assign"

    given BaseContext = getUnpicklingContext(AssignPath)

    val fSym = resolve(AssignPath / name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    val List(Left(List(xParamDef))) = fTree.paramLists: @unchecked

    val IntClass = resolve(name"scala" / tname"Int")
    assert(xParamDef.symbol.declaredType.isRef(IntClass))

    fSym.declaredType match
      case MethodType(_, List(paramTpe), resultTpe) =>
        assert(paramTpe.isRef(IntClass))
        assert(resultTpe.isRef(IntClass))
      case _ =>
        fail(s"$fSym does not have a MethodType", clues(fSym.declaredType))

    val x = SimpleName("x")
    val y = SimpleName("y")

    var xCount = 0
    var yCount = 0

    fTree.walkTree { tree =>
      tree match {
        case Ident(`x`) =>
          xCount += 1
          assert(tree.tpe.isOfClass(IntClass), clue(tree.tpe))
        case Ident(`y`) =>
          yCount += 1
          assert(tree.tpe.isOfClass(IntClass), clue(tree.tpe))
        case _ =>
          ()
      }
    }

    assert(xCount == 2, clue(xCount))
    assert(yCount == 1, clue(yCount))
  }

  test("term-ref") {
    val RepeatedPath = name"simple_trees" / tname"Repeated"

    given BaseContext = getUnpicklingContext(RepeatedPath)

    val fSym = resolve(RepeatedPath / name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var bitSetIdentCount = 0

    fTree.walkTree { tree =>
      tree match {
        case Ident(SimpleName("BitSet")) =>
          bitSetIdentCount += 1
          val sym = tree.tpe.asInstanceOf[Symbolic].resolveToSymbol
          assert(sym.name == name"BitSet", clue(sym.name.toDebugString))
          ()
        case _ =>
          ()
      }
    }

    assert(bitSetIdentCount == 1, clue(bitSetIdentCount))
  }

  test("free-ident") {
    val MatchPath = name"simple_trees" / tname"Match"

    given BaseContext = getUnpicklingContext(MatchPath)

    val fSym = resolve(MatchPath / name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    val List(Left(List(xParamDef))) = fTree.paramLists: @unchecked

    val IntClass = resolve(name"scala" / tname"Int")
    assert(xParamDef.symbol.declaredType.isRef(IntClass))

    var freeIdentCount = 0

    fTree.walkTree { tree =>
      tree match {
        case tree: FreeIdent =>
          freeIdentCount += 1
          assert(tree.name == nme.Wildcard, clue(tree.name))
          assert(tree.tpe.isOfClass(IntClass), clue(tree.tpe))
        case _ =>
          ()
      }
    }

    assert(freeIdentCount == 2, clue(freeIdentCount))
  }

  test("return") {
    val ReturnPath = name"simple_trees" / tname"Return"

    given BaseContext = getUnpicklingContext(ReturnPath)

    val withReturnSym = resolve(ReturnPath / name"withReturn")
    val withReturnTree = withReturnSym.tree.get.asInstanceOf[DefDef]

    var returnCount = 0

    withReturnTree.walkTree { tree =>
      tree match {
        case Return(expr, from: Ident) =>
          returnCount += 1
          assert(from.tpe.isRef(withReturnSym), clue(from.tpe))
          assert(tree.tpe.isRef(resolve(name"scala" / tname"Nothing")))
        case _ =>
          ()
      }
    }

    assert(returnCount == 1, clue(returnCount))
  }

  test("assign") {
    val AssignPath = name"simple_trees" / tname"Assign"

    given BaseContext = getUnpicklingContext(AssignPath)

    val fSym = resolve(AssignPath / name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var assignCount = 0

    fTree.walkTree { tree =>
      tree match {
        case Assign(lhs, rhs) =>
          assignCount += 1
          val UnitClass = resolve(name"scala" / tname"Unit")
          assert(tree.tpe.isOfClass(UnitClass), clue(tree.tpe))
        case _ =>
          ()
      }
    }

    assert(assignCount == 1, clue(assignCount))
  }

  test("basic-java-class-dependency") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val JavaDefined = name"javadefined" / tname"JavaDefined"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val boxedSym = resolve(BoxedJava / name"boxed")

    val (JavaDefinedRef @ _: Symbolic) = boxedSym.declaredType: @unchecked

    assertIsSymbolWithPath(JavaDefined)(JavaDefinedRef.resolveToSymbol)
  }

  test("bag-of-java-definitions") {
    val BagOfJavaDefinitions = name"javadefined" / tname"BagOfJavaDefinitions"

    given BaseContext = getUnpicklingContext(BagOfJavaDefinitions)
    val IntClass = resolve(name"scala" / tname"Int")
    val UnitClass = resolve(name"scala" / tname"Unit")

    def testDef(path: DeclarationPath)(op: Symbol => Unit): Unit =
      op(resolve(path))

    testDef(BagOfJavaDefinitions / name"x") { x =>
      assert(x.declaredType.isRef(IntClass))
    }

    testDef(BagOfJavaDefinitions / name"recField") { recField =>
      assert(recField.declaredType.isRef(resolve(BagOfJavaDefinitions)))
    }

    testDef(BagOfJavaDefinitions / name"printX") { printX =>
      assert(printX.declaredType.resultType.isRef(UnitClass))
    }

    testDef(BagOfJavaDefinitions / name"<init>") { ctor =>
      assert(ctor.declaredType.paramInfos.head.isRef(IntClass))
      assert(ctor.declaredType.resultType.isRef(UnitClass))
    }

    testDef(BagOfJavaDefinitions / name"wrapXArray") { wrapXArray =>
      assert(wrapXArray.declaredType.resultType.isArrayOf(_.typeOrNone.isRef(IntClass)))
    }

    testDef(BagOfJavaDefinitions / name"arrIdentity") { arrIdentity =>
      val JavaDefinedClass = resolve(name"javadefined" / tname"JavaDefined")
      assert(arrIdentity.declaredType.paramInfos.head.isArrayOf(_.typeOrNone.isRef(JavaDefinedClass)))
      assert(arrIdentity.declaredType.resultType.isArrayOf(_.typeOrNone.isRef(JavaDefinedClass)))
    }

  }

  test("bag-of-generic-java-definitions[signatures]") {
    val BagOfGenJavaDefinitions = name"javadefined" / tname"BagOfGenJavaDefinitions"

    given BaseContext = getUnpicklingContext(BagOfGenJavaDefinitions)

    val JavaDefinedClass = resolve(name"javadefined" / tname"JavaDefined")
    val GenericJavaClass = resolve(name"javadefined" / tname"GenericJavaClass")
    val JavaInterface1 = resolve(name"javadefined" / tname"JavaInterface1")
    val JavaInterface2 = resolve(name"javadefined" / tname"JavaInterface2")
    val ExceptionClass = resolve(name"java" / name"lang" / tname"Exception")

    def testDef(path: DeclarationPath)(op: Symbol => Unit): Unit =
      op(resolve(path))

    extension (tpe: Type)
      def isGenJavaClassOf(arg: (Type | TypeBounds) => Boolean)(using BaseContext): Boolean =
        tpe.isApplied(_.isRef(GenericJavaClass), List(arg))

    testDef(BagOfGenJavaDefinitions / name"x") { x =>
      assert(x.declaredType.isGenJavaClassOf(_.typeOrNone.isRef(JavaDefinedClass)))
    }

    testDef(BagOfGenJavaDefinitions / name"getX") { getX =>
      assert(getX.declaredType.resultType.isGenJavaClassOf(_.typeOrNone.isRef(JavaDefinedClass)))
    }

    testDef(BagOfGenJavaDefinitions / name"getXArray") { getXArray =>
      assert(
        getXArray.declaredType.resultType
          .isArrayOf(_.typeOrNone.isGenJavaClassOf(_.typeOrNone.isRef(JavaDefinedClass)))
      )
    }

    testDef(BagOfGenJavaDefinitions / name"printX") { printX =>
      assert(printX.declaredType.tparamBounds.head.high.isRef(ExceptionClass))
    }

    testDef(BagOfGenJavaDefinitions / name"recTypeParams") { recTypeParams =>
      val List(tparamRefA, tparamRefY) = recTypeParams.declaredType.tparamRefs: @unchecked
      assert(tparamRefA.bounds.high.isGenJavaClassOf(_ == tparamRefY))
    }

    testDef(BagOfGenJavaDefinitions / name"refInterface") { refInterface =>
      val List(tparamRefA) = refInterface.declaredType.tparamRefs: @unchecked
      assert(
        tparamRefA.bounds.high.isIntersectionOf(_.isAny, _.isRef(JavaInterface1), _.isRef(JavaInterface2)),
        clues(tparamRefA.bounds)
      )
    }

    testDef(BagOfGenJavaDefinitions / name"genraw") { genraw =>
      assert(genraw.declaredType.isGenJavaClassOf(_.isWildcard))
    }

    testDef(BagOfGenJavaDefinitions / name"mixgenraw") { mixgenraw =>
      assert(mixgenraw.declaredType.isGenJavaClassOf(_.typeOrNone.isGenJavaClassOf(_.isWildcard)))
    }

    testDef(BagOfGenJavaDefinitions / name"genwild") { genwild =>
      assert(genwild.declaredType.isGenJavaClassOf(_.isWildcard))
    }

    testDef(BagOfGenJavaDefinitions / name"gencovarient") { gencovarient =>
      assert(gencovarient.declaredType.isGenJavaClassOf(_.isBounded(_.isNothing, _.isRef(JavaDefinedClass))))
    }

    testDef(BagOfGenJavaDefinitions / name"gencontravarient") { gencontravarient =>
      assert(gencontravarient.declaredType.isGenJavaClassOf(_.isBounded(_.isRef(JavaDefinedClass), _.isAny)))
    }
  }

  test("java-class-parents") {
    val SubJavaDefined = name"javadefined" / tname"SubJavaDefined"

    given BaseContext = getUnpicklingContext(SubJavaDefined)

    val (SubJavaDefinedTpe @ _: ClassType) = resolve(SubJavaDefined).declaredType: @unchecked

    val JavaDefinedClass = resolve(name"javadefined" / tname"JavaDefined")
    val JavaInterface1Class = resolve(name"javadefined" / tname"JavaInterface1")
    val JavaInterface2Class = resolve(name"javadefined" / tname"JavaInterface2")

    assert(
      SubJavaDefinedTpe.rawParents
        .isIntersectionOf(_.isRef(JavaDefinedClass), _.isRef(JavaInterface1Class), _.isRef(JavaInterface2Class))
    )
  }

  test("java-class-signatures-[RecClass]") {
    val RecClass = name"javadefined" / tname"RecClass"
    given BaseContext = getUnpicklingContext(RecClass)

    val (RecClassTpe @ _: ClassType) = resolve(RecClass).declaredType: @unchecked

    val ObjectClass = resolve(name"java" / name"lang" / tname"Object")

    assert(RecClassTpe.rawParents.isRef(ObjectClass))
  }

  test("java-class-signatures-[SubRecClass]") {
    val SubRecClass = name"javadefined" / tname"SubRecClass"
    given BaseContext = getUnpicklingContext(SubRecClass)

    val (SubRecClassTpe @ _: ClassType) = resolve(SubRecClass).declaredType: @unchecked

    val RecClass = resolve(name"javadefined" / tname"RecClass")
    val JavaInterface1 = resolve(name"javadefined" / tname"JavaInterface1")

    val List(tparamT) = SubRecClassTpe.cls.typeParamSyms: @unchecked

    assert(
      SubRecClassTpe.rawParents.isIntersectionOf(
        _.isApplied(
          _.isRef(RecClass),
          List(_.typeOrNone.isApplied(_.isRef(SubRecClassTpe.cls), List(_.typeOrNone.isRef(tparamT))))
        ),
        _.isRef(JavaInterface1)
      )
    )
  }

  test("select-method-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val getX = name"javadefined" / tname"JavaDefined" / name"getX"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xMethodSym = resolve(BoxedJava / name"xMethod")

    val Some(DefDef(_, _, _, Apply(getXSelection, _), _)) = xMethodSym.tree: @unchecked

    val (getXRef @ _: Symbolic) = getXSelection.tpe: @unchecked

    assertIsSymbolWithPath(getX)(getXRef.resolveToSymbol)
  }

  test("select-field-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val x = name"javadefined" / tname"JavaDefined" / name"x"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xFieldSym = resolve(BoxedJava / name"xField")

    val Some(DefDef(_, _, _, xSelection, _)) = xFieldSym.tree: @unchecked

    val (xRef @ _: Symbolic) = xSelection.tpe: @unchecked

    assertIsSymbolWithPath(x)(xRef.resolveToSymbol)
  }

  test("basic-scala-2-stdlib-class-dependency") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val :: = name"scala" / name"collection" / name"immutable" / tname"::"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val boxedSym = resolve(BoxedCons / name"boxed")

    val (AppliedType(ConsRef @ _: Symbolic, _)) = boxedSym.declaredType: @unchecked

    assertIsSymbolWithPath(::)(ConsRef.resolveToSymbol)
  }

  test("select-method-from-scala-2-stdlib-class") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val canEqual = name"scala" / name"collection" / tname"Seq" / name"canEqual"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val fooSym = resolve(BoxedCons / name"foo")

    val Some(DefDef(_, _, _, Apply(canEqualSelection, _), _)) = fooSym.tree: @unchecked

    val (canEqualRef @ _: Symbolic) = canEqualSelection.tpe: @unchecked

    assertIsSymbolWithPath(canEqual)(canEqualRef.resolveToSymbol)
  }

  test("select-field-from-tasty-in-other-package:dependency-from-class-file") {
    val BoxedConstants = name"crosspackagetasty" / tname"BoxedConstants"
    val unitVal = name"simple_trees" / tname"Constants" / name"unitVal"

    given BaseContext = getUnpicklingContext(BoxedConstants)

    val boxedUnitValSym = resolve(BoxedConstants / name"boxedUnitVal")

    val Some(DefDef(_, _, _, unitValSelection, _)) = boxedUnitValSym.tree: @unchecked

    val (unitValRef @ _: Symbolic) = unitValSelection.tpe: @unchecked

    assertIsSymbolWithPath(unitVal)(unitValRef.resolveToSymbol)
  }

  test("select-method-from-java-class-same-package-as-tasty") {
    // This tests reading top level classes in the same package, defined by
    // both Java and Tasty. If we strictly require that all symbols are defined
    // exactly once, then we must be careful to not redefine `ScalaBox`/`JavaBox`
    // when scanning a package from the classpath.

    val ScalaBox = name"mixjavascala" / tname"ScalaBox"
    val getX = name"mixjavascala" / tname"JavaBox" / name"getX"

    given BaseContext = getUnpicklingContext(ScalaBox)

    val xMethodSym = resolve(ScalaBox / name"xMethod")

    val Some(DefDef(_, _, _, Apply(getXSelection, _), _)) = xMethodSym.tree: @unchecked

    val (getXRef @ _: Symbolic) = getXSelection.tpe: @unchecked

    assertIsSymbolWithPath(getX)(getXRef.resolveToSymbol)
  }

}
