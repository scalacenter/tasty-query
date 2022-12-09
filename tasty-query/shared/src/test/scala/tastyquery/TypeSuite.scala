package tastyquery

import scala.collection.mutable

import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import TestUtils.*

class TypeSuite extends UnrestrictedUnpicklingSuite {
  extension [T](elems: List[T])
    def isListOf(tests: (T => Boolean)*)(using Context): Boolean =
      elems.corresponds(tests)((t, test) => test(t))

  extension (tpe: Type)
    def isAny(using Context): Boolean = tpe.isRef(defn.AnyClass)

    def isNothing(using Context): Boolean = tpe.isRef(defn.NothingClass)

    def isWildcard(using Context): Boolean =
      isBounded(_.isNothing, _.isAny)

    def isBounded(lo: Type => Boolean, hi: Type => Boolean)(using Context): Boolean = tpe match
      case tpe: WildcardTypeBounds => lo(tpe.bounds.low) && hi(tpe.bounds.high)
      case _                       => false

    def isIntersectionOf(tpes: (Type => Boolean)*)(using Context): Boolean =
      def parts(tpe: Type): List[Type] = tpe match
        case tpe: AndType => tpe.parts
        case tpe: Type    => tpe :: Nil
      parts(tpe.widen).isListOf(tpes*)

    def isApplied(cls: Type => Boolean, argRefs: Seq[Type => Boolean])(using Context): Boolean =
      tpe.widen match
        case app: AppliedType if cls(app.tycon) =>
          app.args.corresponds(argRefs)((arg, argRef) => argRef(arg))
        case _ => false

    def isArrayOf(arg: Type => Boolean)(using Context): Boolean =
      isApplied(_.isRef(defn.ArrayClass), Seq(arg))

  testWithContext("apply-dependent") {
    val DependentMethodClass = ctx.findTopLevelClass("simple_trees.DependentMethod")
    val testVal = DependentMethodClass.findNonOverloadedDecl(name"test")
    val testDef = testVal.tree.get.asInstanceOf[ValDef]
    val applyTree = testDef.rhs.get.asInstanceOf[Apply]
    assert(applyTree.tpe.isOfClass(defn.StringClass))
  }

  testWithContext("apply-recursive") {
    val RecApplyClass = ctx.findTopLevelClass("simple_trees.RecApply")

    val gcdSym = RecApplyClass.findNonOverloadedDecl(name"gcd")
    val NumClass = RecApplyClass.findDecl(tname"Num").asClass

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

  testWithContext("java.lang.String") {
    val charAt = defn.StringClass.findNonOverloadedDecl(name"charAt")
    val tpe = charAt.declaredType.asInstanceOf[MethodType]
    assert(clue(tpe.resultType).isRef(defn.CharClass))
  }

  testWithContext("scala.compiletime.Error parents") {
    // #179 The parents of Error contain a TypeRef(PackageRef(scala), "Serializable")

    val ProductClass = ctx.findTopLevelClass("scala.Product")
    val SerializableClass = ctx.findTopLevelClass("java.io.Serializable")
    val CompTimeErrorClass = ctx.findTopLevelClass("scala.compiletime.testing.Error")

    val parentClasses = CompTimeErrorClass.parentClasses
    assert(clue(parentClasses) == List(defn.ObjectClass, ProductClass, SerializableClass))
  }

  def applyOverloadedTest(name: String)(callMethod: String, checkParamType: Context ?=> Type => Boolean): Unit =
    testWithContext(name) {
      val OverloadedApplyClass = ctx.findTopLevelClass("simple_trees.OverloadedApply")

      val callSym = OverloadedApplyClass.findDecl(termName(callMethod))

      val Some(callTree @ _: DefDef) = callSym.tree: @unchecked

      var callCount = 0

      callTree.walkTree { tree =>
        tree match
          case app @ Apply(fooRef @ Select(_, SignedName(SimpleName("foo"), _, _)), _) =>
            callCount += 1
            assert(app.tpe.isRef(defn.UnitClass), clue(app))
            val fooSym = fooRef.tpe.asInstanceOf[TermRef].symbol
            val mt = fooSym.declaredType.asInstanceOf[MethodType]
            assert(clue(mt.resultType).isRef(defn.UnitClass))
            assert(checkParamType(clue(mt.paramTypes.head)))
          case _ => ()
      }

      assert(callCount == 1)
    }

  applyOverloadedTest("apply-overloaded-int")("callA", _.isRef(defn.IntClass))
  applyOverloadedTest("apply-overloaded-gen")(
    "callB",
    _.isApplied(
      _.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Box")),
      List(_.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Num")))
    )
  )
  applyOverloadedTest("apply-overloaded-nestedObj")(
    "callC",
    _.isRef(
      ctx
        .findTopLevelClass("simple_trees.OverloadedApply")
        .findDecl(moduleClassName("Foo"))
        .asClass
        .findDecl(termName("Bar"))
    )
  )
  applyOverloadedTest("apply-overloaded-arrayObj")("callD", _.isRef(defn.ArrayClass))
  applyOverloadedTest("apply-overloaded-byName")(
    "callE",
    _.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Num"))
  )
  applyOverloadedTest("apply-overloaded-gen-target-name")(
    "callG",
    _.isApplied(
      _.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Box")),
      List(_.isRef(defn.IntClass))
    )
  )

  testWithContext("apply-overloaded-not-method") {
    val OverloadedApplyClass = ctx.findTopLevelClass("simple_trees.OverloadedApply")

    val callSym = OverloadedApplyClass.findNonOverloadedDecl(termName("callF"))

    val Some(callTree @ _: DefDef) = callSym.tree: @unchecked

    var callCount = 0

    callTree.walkTree { tree =>
      tree match
        case fooRef @ Select(_, SimpleName("foo")) =>
          callCount += 1
          val fooSym = fooRef.tpe.asInstanceOf[TermRef].symbol
          assert(clue(fooSym.paramRefss).isEmpty)
        case _ => ()
    }

    assert(callCount == 1)
  }

  testWithContext("typeapply-recursive") {
    val RecApplyClass = ctx.findTopLevelClass("simple_trees.RecApply")

    val evalSym = RecApplyClass.findNonOverloadedDecl(name"eval")
    val ExprClass = RecApplyClass.findDecl(tname"Expr")
    val NumClass = RecApplyClass.findDecl(tname"Num")
    val BoolClass = RecApplyClass.findDecl(tname"Bool")

    val evalParamRefss = evalSym.paramRefss

    val List(Right(List(TRef @ _)), Left(List(eRef))) = evalParamRefss: @unchecked

    val Some(evalTree @ _: DefDef) = evalSym.tree: @unchecked

    var recCallCount = 0

    evalTree.walkTree { tree =>
      tree match
        case recCall @ Apply(TypeApply(evalRef @ Select(_, SignedName(SimpleName("eval"), _, _)), List(targ)), _) =>
          recCallCount += 1

          assert(evalRef.tpe.isRef(evalSym), clue(evalRef))

          /* Because of GADT reasoning, the first two recursive call implicitly
           * have a [Num] type parameter, while the latter two have [Bool].
           */
          val expectedTargClass =
            if recCallCount <= 2 then NumClass
            else BoolClass

          assert(clue(targ).toType.isRef(expectedTargClass))
          assert(recCall.tpe.isRef(expectedTargClass), clue(recCall))
        case _ => ()
    }

    assert(recCallCount == 4) // 4 calls in the body of `eval`

  }

  testWithContext("basic-local-val") {
    val AssignPathClass = ctx.findTopLevelClass("simple_trees.Assign")

    val fSym = AssignPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    val List(Left(List(xParamDef))) = fTree.paramLists: @unchecked

    assert(xParamDef.symbol.asTerm.declaredType.isRef(defn.IntClass))

    fSym.declaredType match
      case mt: MethodType =>
        assert(mt.paramTypes.sizeIs == 1 && mt.paramTypes.head.isRef(defn.IntClass))
        assert(mt.resultType.isRef(defn.IntClass))
      case _ =>
        fail(s"$fSym does not have a MethodType", clues(fSym.declaredType))

    val x = SimpleName("x")
    val y = SimpleName("y")

    var xCount = 0
    var yCount = 0

    fTree.walkTree { tree =>
      tree match {
        case tree @ Ident(`x`) =>
          xCount += 1
          assert(tree.tpe.isOfClass(defn.IntClass), clue(tree.tpe))
        case tree @ Ident(`y`) =>
          yCount += 1
          assert(tree.tpe.isOfClass(defn.IntClass), clue(tree.tpe))
        case _ =>
          ()
      }
    }

    assert(xCount == 2, clue(xCount))
    assert(yCount == 1, clue(yCount))
  }

  testWithContext("term-ref") {
    val RepeatedPathClass = ctx.findTopLevelClass("simple_trees.Repeated")

    val fSym = RepeatedPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var bitSetIdentCount = 0

    fTree.walkTree { tree =>
      tree match {
        case tree @ Ident(SimpleName("BitSet")) =>
          bitSetIdentCount += 1
          val sym = tree.tpe.asInstanceOf[TermRef].symbol
          assert(sym.name == name"BitSet", clue(sym.name.toDebugString))
          ()
        case _ =>
          ()
      }
    }

    assert(bitSetIdentCount == 1, clue(bitSetIdentCount))
  }

  testWithContext("wildcard-pattern") {
    val MatchPathClass = ctx.findTopLevelClass("simple_trees.Match")

    val fSym = MatchPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    val List(Left(List(xParamDef))) = fTree.paramLists: @unchecked

    assert(xParamDef.symbol.asTerm.declaredType.isRef(defn.IntClass))

    var wildcardPatternCount = 0

    fTree.walkTree { tree =>
      tree match {
        case tree @ WildcardPattern(tpe) =>
          wildcardPatternCount += 1
          assert(tpe.isRef(defn.IntClass), clue(tpe))
        case _ =>
          ()
      }
    }

    assert(wildcardPatternCount == 2, clue(wildcardPatternCount))
  }

  testWithContext("return") {
    val ReturnPathClass = ctx.findTopLevelClass("simple_trees.Return")

    val withReturnSym = ReturnPathClass.findNonOverloadedDecl(name"withReturn")
    val withReturnTree = withReturnSym.tree.get.asInstanceOf[DefDef]

    var returnCount = 0

    withReturnTree.walkTree { tree =>
      tree match {
        case tree @ Return(expr, from) =>
          returnCount += 1
          assert(from == withReturnSym, clue(from))
          assert(tree.tpe.isNothing)
        case _ =>
          ()
      }
    }

    assert(returnCount == 1, clue(returnCount))
  }

  testWithContext("assign") {
    val AssignPathClass = ctx.findTopLevelClass("simple_trees.Assign")

    val fSym = AssignPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var assignCount = 0

    fTree.walkTree { tree =>
      tree match {
        case tree @ Assign(lhs, rhs) =>
          assignCount += 1
          assert(tree.tpe.isOfClass(defn.UnitClass), clue(tree.tpe))
        case _ =>
          ()
      }
    }

    assert(assignCount == 1, clue(assignCount))
  }

  testWithContext("basic-scala2-types") {
    val RangeClass = ctx.findTopLevelClass("scala.collection.immutable.Range")
    val Function1Class = ctx.findTopLevelClass("scala.Function1")
    val IndexedSeqClass = ctx.findTopLevelClass("scala.collection.immutable.IndexedSeq")

    // val start: Int
    val startSym = RangeClass.findDecl(name"start")
    assert(startSym.declaredType.isOfClass(defn.IntClass), clue(startSym.declaredType))
    assert(startSym.declaredType.isInstanceOf[ExprType], clue(startSym.declaredType)) // should this be TypeRef?

    // val isEmpty: Boolean
    val isEmptySym = RangeClass.findDecl(name"isEmpty")
    assert(isEmptySym.declaredType.isOfClass(defn.BooleanClass), clue(isEmptySym.declaredType))
    assert(isEmptySym.declaredType.isInstanceOf[ExprType], clue(isEmptySym.declaredType)) // should this be TypeRef?

    // def isInclusive: Boolean
    val isInclusiveSym = RangeClass.findDecl(name"isInclusive")
    assert(isInclusiveSym.declaredType.isOfClass(defn.BooleanClass), clue(isInclusiveSym.declaredType))
    assert(isInclusiveSym.declaredType.isInstanceOf[ExprType], clue(isInclusiveSym.declaredType))

    // def by(step: Int): Range
    locally {
      val bySym = RangeClass.findNonOverloadedDecl(name"by")
      val mt = bySym.declaredType.asInstanceOf[MethodType]
      assertEquals(List[TermName](name"step"), mt.paramNames, clue(mt.paramNames))
      assert(mt.paramTypes.sizeIs == 1)
      assert(mt.paramTypes.head.isOfClass(defn.IntClass), clue(mt.paramTypes.head))
      assert(mt.resultType.isOfClass(RangeClass), clue(mt.resultType))
    }

    // def map[B](f: Int => B): IndexedSeq[B]
    locally {
      val mapSym = RangeClass.findNonOverloadedDecl(name"map")
      val pt = mapSym.declaredType.asInstanceOf[PolyType]
      val mt = pt.resultType.asInstanceOf[MethodType]
      assertEquals(List[TypeName](name"B".toTypeName), pt.paramNames, clue(pt.paramNames))
      assert(pt.paramTypeBounds.sizeIs == 1)
      assertEquals(List[TermName](name"f"), mt.paramNames, clue(mt.paramNames))
      assert(mt.paramTypes.sizeIs == 1)
      assert(mt.paramTypes.head.isOfClass(Function1Class), clue(mt.paramTypes.head))
      assert(mt.resultType.isOfClass(IndexedSeqClass), clue(mt.resultType))
    }
  }

  testWithContext("basic-java-class-dependency") {
    val BoxedJavaClass = ctx.findTopLevelClass("javacompat.BoxedJava")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val boxedSym = BoxedJavaClass.getDecl(name"boxed").get.asTerm

    val (JavaDefinedRef @ _: TypeRef) = boxedSym.declaredType: @unchecked

    assert(clue(JavaDefinedRef.symbol) == JavaDefinedClass)
  }

  testWithContext("package-private-class") {
    val javadefinedPackage = ctx.findPackage("javadefined")
    val PkgPrivateClass = ctx.findTopLevelClass("javadefined.PkgPrivate")
    val PkgPrivateModule = ctx.findTopLevelModuleClass("javadefined.PkgPrivate")
    val PkgPrivateModuleClass = ctx.findStaticTerm("javadefined.PkgPrivate")

    def assertPrivateWithin(sym: Symbol, expected: Symbol)(using munit.Location) =
      assert(!sym.isAnyOf(Flags.Private | Flags.Protected))
      assert(sym.privateWithin == Some(expected))

    assertPrivateWithin(PkgPrivateClass, javadefinedPackage)
    assertPrivateWithin(PkgPrivateModule, javadefinedPackage)
    assertPrivateWithin(PkgPrivateModuleClass, javadefinedPackage)
  }

  testWithContext("bag-of-java-definitions[static]") {
    val BagOfJavaDefinitionsClassMod = ctx.findTopLevelModuleClass("javadefined.BagOfJavaDefinitions")
    val javadefinedPackage = ctx.findPackage("javadefined")

    def testDef(name: TermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfJavaDefinitionsClassMod.findNonOverloadedDecl(name))

    def assertJavaPublic(sym: Symbol)(using munit.Location) =
      assert(!sym.isAnyOf(Flags.Private | Flags.Protected))
      assert(sym.privateWithin == None)

    def assertPrivateWithin(sym: Symbol, expected: Symbol)(using munit.Location) =
      assert(!sym.isAnyOf(Flags.Private | Flags.Protected))
      assert(sym.privateWithin == Some(expected))

    testDef(name"STATIC_INT") { STATIC_INT =>
      assertJavaPublic(STATIC_INT)
      assert(STATIC_INT.declaredType.isRef(defn.IntClass))
    }

    testDef(name"defaultInt") { defaultInt =>
      assertJavaPublic(defaultInt)
      assert(defaultInt.declaredType.asInstanceOf[MethodType].resultType.isRef(defn.IntClass))
    }

    testDef(name"packagePrivateIntField") { packagePrivateIntField =>
      assertPrivateWithin(packagePrivateIntField, javadefinedPackage)
      assert(packagePrivateIntField.declaredType.isRef(defn.IntClass))
    }

    testDef(name"packagePrivateIntMethod") { packagePrivateIntMethod =>
      assertPrivateWithin(packagePrivateIntMethod, javadefinedPackage)
      assert(packagePrivateIntMethod.declaredType.asInstanceOf[MethodType].resultType.isRef(defn.IntClass))
    }
  }

  testWithContext("bag-of-java-definitions") {
    val BagOfJavaDefinitionsClass = ctx.findTopLevelClass("javadefined.BagOfJavaDefinitions")
    val javadefinedPackage = ctx.findPackage("javadefined")

    def assertJavaPublic(sym: Symbol)(using munit.Location) =
      assert(!sym.isAnyOf(Flags.Private | Flags.Protected))
      assert(sym.privateWithin == None)

    def assertPrivateWithin(sym: Symbol, expected: Symbol)(using munit.Location) =
      assert(!sym.isAnyOf(Flags.Private | Flags.Protected))
      assert(sym.privateWithin == Some(expected))

    def testDef(name: TermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfJavaDefinitionsClass.findNonOverloadedDecl(name))

    testDef(name"x") { x =>
      assertJavaPublic(x)
      assert(x.declaredType.isRef(defn.IntClass))
    }

    testDef(name"protectedY") { protectedY =>
      assert(protectedY.is(Flags.Protected))
      assert(!protectedY.is(Flags.Private))
      assert(protectedY.privateWithin == None)
      assert(protectedY.declaredType.isRef(defn.IntClass))
    }

    testDef(name"privateZ") { privateZ =>
      assert(privateZ.is(Flags.Private))
      assert(!privateZ.is(Flags.Protected))
      assert(privateZ.privateWithin == None)
      assert(privateZ.declaredType.isRef(defn.IntClass))
    }

    testDef(name"recField") { recField =>
      assertJavaPublic(recField)
      assert(recField.declaredType.isRef(BagOfJavaDefinitionsClass))
    }

    testDef(name"innerClassField") { innerClassField =>
      assertJavaPublic(innerClassField)
      val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")
      val MyInnerClass = JavaDefinedClass.findDecl(tname"MyInner").asClass

      assert(innerClassField.declaredType.isRef(MyInnerClass))
    }

    testDef(name"staticInnerClassField") { staticInnerClassField =>
      assertJavaPublic(staticInnerClassField)
      val MyStaticInnerClass = ctx.findStaticClass("javadefined.JavaDefined.MyStaticInner")

      assert(staticInnerClassField.declaredType.isRef(MyStaticInnerClass))
    }

    testDef(name"outerRefToInner") { outerRefToInner =>
      assertJavaPublic(outerRefToInner)
      val MyOwnInnerClass = BagOfJavaDefinitionsClass.findDecl(tname"MyOwnInner").asClass

      assert(outerRefToInner.declaredType.isRef(MyOwnInnerClass))
    }

    testDef(name"outerRefToStaticInner") { outerRefToStaticInner =>
      assertJavaPublic(outerRefToStaticInner)
      val MyOwnStaticInnerClass = ctx.findStaticClass("javadefined.BagOfJavaDefinitions.MyOwnStaticInner")

      assert(outerRefToStaticInner.declaredType.isRef(MyOwnStaticInnerClass))
    }

    testDef(name"scalaStaticInnerRefFromJava") { scalaStaticInnerRefFromJava =>
      assertPrivateWithin(scalaStaticInnerRefFromJava, javadefinedPackage)
      val StaticInnerClass = ctx.findStaticClass("mixjavascala.ScalaStaticOuter.StaticInnerClass")

      assert(scalaStaticInnerRefFromJava.declaredType.isRef(StaticInnerClass))
    }

    testDef(name"scalaInnerRefFromJava") { scalaInnerRefFromJava =>
      assertPrivateWithin(scalaInnerRefFromJava, javadefinedPackage)
      val ScalaOuterClass = ctx.findTopLevelClass("mixjavascala.ScalaOuter")
      val InnerClass = ScalaOuterClass.findDecl(tname"InnerClass").asClass

      assert(scalaInnerRefFromJava.declaredType.isRef(InnerClass))
    }

    testDef(name"printX") { printX =>
      assertJavaPublic(printX)
      val tpe = printX.declaredType.asInstanceOf[MethodType]
      assert(tpe.resultType.isRef(defn.UnitClass))
    }

    testDef(name"<init>") { ctor =>
      assertJavaPublic(ctor)
      val tpe = ctor.declaredType.asInstanceOf[MethodType]
      assert(tpe.paramTypes.head.isRef(defn.IntClass))
      assert(tpe.resultType.isRef(defn.UnitClass))
    }

    testDef(name"wrapXArray") { wrapXArray =>
      assertJavaPublic(wrapXArray)
      val tpe = wrapXArray.declaredType.asInstanceOf[MethodType]
      assert(tpe.resultType.isArrayOf(_.isRef(defn.IntClass)))
    }

    testDef(name"arrIdentity") { arrIdentity =>
      assertJavaPublic(arrIdentity)
      val tpe = arrIdentity.declaredType.asInstanceOf[MethodType]
      val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")
      assert(tpe.paramInfos.head.isArrayOf(_.isRef(JavaDefinedClass)))
      assert(tpe.resultType.isArrayOf(_.isRef(JavaDefinedClass)))
    }

    testDef(name"processBuilder") { processBuilder =>
      assertJavaPublic(processBuilder)
      val tpe = processBuilder.declaredType.asInstanceOf[MethodType]
      assert(tpe.resultType.isInstanceOf[TypeRef]) // do not call isRef, as we do not have the java lib
    }

  }

  testWithContext("bag-of-generic-java-definitions[signatures]") {
    val BagOfGenJavaDefinitionsClass = ctx.findTopLevelClass("javadefined.BagOfGenJavaDefinitions")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")
    val ScalaGenOuterClass = ctx.findTopLevelClass("mixjavascala.ScalaGenOuter")
    val GenericJavaClass = ctx.findTopLevelClass("javadefined.GenericJavaClass")
    val JavaInterface1 = ctx.findTopLevelClass("javadefined.JavaInterface1")
    val JavaInterface2 = ctx.findTopLevelClass("javadefined.JavaInterface2")
    val ExceptionClass = ctx.findTopLevelClass("java.lang.Exception")

    def testDef(name: TermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfGenJavaDefinitionsClass.findNonOverloadedDecl(name))

    extension (tpe: Type)
      def isGenJavaClassOf(arg: Type => Boolean)(using Context): Boolean =
        tpe.isApplied(_.isRef(GenericJavaClass), List(arg))

    testDef(name"x") { x =>
      assert(x.declaredType.isGenJavaClassOf(_.isRef(JavaDefinedClass)))
    }

    testDef(name"getX") { getX =>
      val tpe = getX.declaredType.asInstanceOf[MethodType]
      assert(tpe.resultType.isGenJavaClassOf(_.isRef(JavaDefinedClass)))
    }

    testDef(name"getXArray") { getXArray =>
      val tpe = getXArray.declaredType.asInstanceOf[MethodType]
      assert(tpe.resultType.isArrayOf(_.isGenJavaClassOf(_.isRef(JavaDefinedClass))))
    }

    testDef(name"printX") { printX =>
      val tpe = printX.declaredType.asInstanceOf[PolyType]
      assert(tpe.paramTypeBounds.head.high.isRef(ExceptionClass))
    }

    testDef(name"getInner") { getInner =>
      val MyInnerClass = GenericJavaClass.findDecl(tname"MyInner").asClass
      val tpe = getInner.declaredType.asInstanceOf[MethodType]

      // javadefined.GenericJavaClass[JavaDefined]#MyInner[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      // javadefined.GenericJavaClass[JavaDefined]
      val pre = res.tycon.asInstanceOf[TypeRef].prefix.asInstanceOf[Type]

      assert(res.isApplied(_.isRef(MyInnerClass), List(_.isRef(JavaDefinedClass))))
      assert(pre.isGenJavaClassOf(_.isRef(JavaDefinedClass)))
    }

    testDef(name"getStaticInner") { getStaticInner =>
      val MyStaticInnerClass = ctx.findStaticClass("javadefined.GenericJavaClass.MyStaticInner")
      val tpe = getStaticInner.declaredType.asInstanceOf[MethodType]

      // javadefined.GenericJavaClass.MyStaticInner[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      assert(res.isApplied(_.isRef(MyStaticInnerClass), List(_.isRef(JavaDefinedClass))))
    }

    testDef(name"getScalaInner") { getScalaInner =>
      val InnerGenClass = ScalaGenOuterClass.findDecl(tname"InnerGenClass").asClass
      val tpe = getScalaInner.declaredType.asInstanceOf[MethodType]

      // mixjavascala.ScalaGenOuter[JavaDefined]#InnerGenClass[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      // mixjavascala.ScalaGenOuter[JavaDefined]
      val pre = res.tycon.asInstanceOf[TypeRef].prefix.asInstanceOf[Type]

      assert(res.isApplied(_.isRef(InnerGenClass), List(_.isRef(JavaDefinedClass))))
      assert(pre.isApplied(_.isRef(ScalaGenOuterClass), List(_.isRef(JavaDefinedClass))))
    }

    testDef(name"getScalaStaticInner") { getScalaStaticInner =>
      val StaticInnerGenClass = ctx.findStaticClass("mixjavascala.ScalaStaticOuter.StaticInnerGenClass")
      val tpe = getScalaStaticInner.declaredType.asInstanceOf[MethodType]

      // mixjavascala.ScalaStaticOuter#StaticInnerGenClass[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      assert(res.isApplied(_.isRef(StaticInnerGenClass), List(_.isRef(JavaDefinedClass))))
    }

    testDef(name"getAbsurdInner") { getAbsurdInner =>
      val MyInnerClass = JavaDefinedClass.findDecl(tname"MyInner").asClass
      val MyInnerInnerClass = MyInnerClass.findDecl(tname"MyInnerInner").asClass
      val MyInnerInnerGenInnerClass = MyInnerInnerClass.findDecl(tname"MyInnerInnerGenInner").asClass
      val tpe = getAbsurdInner.declaredType.asInstanceOf[MethodType]

      // javadefined.JavaDefined.MyInner.MyInnerInner.MyInnerInnerGenInner[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      assert(res.isApplied(_.isRef(MyInnerInnerGenInnerClass), List(_.isRef(JavaDefinedClass))))
    }

    testDef(name"getAbsurdInner2") { getAbsurdInner2 =>
      val MyGenInnerClass = JavaDefinedClass.findDecl(tname"MyGenInner").asClass
      val MyInnerInnerClass = MyGenInnerClass.findDecl(tname"MyInnerInner").asClass
      val MyInnerInnerInnerClass = MyInnerInnerClass.findDecl(tname"MyInnerInnerInner").asClass
      val tpe = getAbsurdInner2.declaredType.asInstanceOf[MethodType]

      // javadefined.JavaDefined.MyGenInner[JavaDefined]#MyInnerInner.MyInnerInnerInner
      val res = tpe.resultType

      assert(res.isRef(MyInnerInnerInnerClass))
    }

    testDef(name"getAbsurdInner3") { getAbsurdInner3 =>
      val JavaDefinedPre = "javadefined.JavaDefined"
      val MyStaticGenInnerInnerInnerClass =
        ctx.findStaticClass(s"$JavaDefinedPre.MyStaticGenInner.MyStaticGenInnerInner.MyStaticGenInnerInnerInner")

      val tpe = getAbsurdInner3.declaredType.asInstanceOf[MethodType]

      // javadefined.JavaDefined.MyStaticGenInner.MyStaticGenInnerInner.MyStaticGenInnerInnerInner[JavaDefined]
      val res = tpe.resultType.asInstanceOf[AppliedType]

      assert(res.isApplied(_.isRef(MyStaticGenInnerInnerInnerClass), List(_.isRef(JavaDefinedClass))))
    }

    testDef(name"recTypeParams") { recTypeParams =>
      val tpe = recTypeParams.declaredType.asInstanceOf[TypeLambdaType]
      val List(tparamRefA, tparamRefY) = tpe.paramRefs: @unchecked
      assert(tparamRefA.bounds.high.isGenJavaClassOf(_ == tparamRefY))
    }

    testDef(name"refInterface") { refInterface =>
      val tpe = refInterface.declaredType.asInstanceOf[TypeLambdaType]
      val List(tparamRefA) = tpe.paramRefs: @unchecked
      assert(
        tparamRefA.bounds.high.isIntersectionOf(_.isAny, _.isRef(JavaInterface1), _.isRef(JavaInterface2)),
        clues(tparamRefA.bounds)
      )
    }

    testDef(name"genraw") { genraw =>
      /* Raw types are not really supported (see #80). They are read and
       * stored as if they were *monomorphic* class references, i.e., TypeRef's
       * without any AppliedType.
       */
      assert(genraw.declaredType.isRef(GenericJavaClass))
    }

    testDef(name"mixgenraw") { mixgenraw =>
      // Same comment about raw types.
      assert(mixgenraw.declaredType.isGenJavaClassOf(_.isRef(GenericJavaClass)))
    }

    testDef(name"genwild") { genwild =>
      assert(genwild.declaredType.isGenJavaClassOf(_.isWildcard))
    }

    testDef(name"gencovarient") { gencovarient =>
      assert(gencovarient.declaredType.isGenJavaClassOf(_.isBounded(_.isNothing, _.isRef(JavaDefinedClass))))
    }

    testDef(name"gencontravarient") { gencontravarient =>
      assert(gencontravarient.declaredType.isGenJavaClassOf(_.isBounded(_.isRef(JavaDefinedClass), _.isAny)))
    }
  }

  testWithContext("java-class-parents") {
    val SubJavaDefinedClass = ctx.findTopLevelClass("javadefined.SubJavaDefined")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")
    val JavaInterface1Class = ctx.findTopLevelClass("javadefined.JavaInterface1")
    val JavaInterface2Class = ctx.findTopLevelClass("javadefined.JavaInterface2")

    assert(
      SubJavaDefinedClass.parents
        .isListOf(_.isRef(JavaDefinedClass), _.isRef(JavaInterface1Class), _.isRef(JavaInterface2Class))
    )
  }

  testWithContext("Parents of special classes") {
    assert(clue(defn.AnyClass.parentClasses) == Nil)
    assert(clue(defn.MatchableClass.parentClasses) == List(defn.AnyClass))
    assert(clue(defn.ObjectClass.parentClasses) == List(defn.AnyClass, defn.MatchableClass))
    assert(clue(defn.AnyValClass.parentClasses) == List(defn.AnyClass, defn.MatchableClass))
    assert(clue(defn.NullClass.parentClasses) == List(defn.AnyClass, defn.MatchableClass))
    assert(clue(defn.NothingClass.parentClasses) == List(defn.AnyClass))
  }

  testWithContext("java-class-signatures-[RecClass]") {
    val RecClass = ctx.findTopLevelClass("javadefined.RecClass")

    assert(RecClass.parents.isListOf(_.isRef(defn.ObjectClass)))
  }

  testWithContext("java-class-signatures-[SubRecClass]") {
    val SubRecClass = ctx.findTopLevelClass("javadefined.SubRecClass")
    val RecClass = ctx.findTopLevelClass("javadefined.RecClass")
    val JavaInterface1 = ctx.findTopLevelClass("javadefined.JavaInterface1")

    val List(tparamT) = SubRecClass.typeParams: @unchecked

    assert(
      SubRecClass.parents.isListOf(
        _.isApplied(_.isRef(RecClass), List(_.isApplied(_.isRef(SubRecClass), List(_.isRef(tparamT))))),
        _.isRef(JavaInterface1)
      )
    )
  }

  testWithContext("select-method-from-java-class") {
    val BoxedJavaClass = ctx.findTopLevelClass("javacompat.BoxedJava")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val getX = JavaDefinedClass.findNonOverloadedDecl(name"getX")
    val xMethodSym = BoxedJavaClass.findNonOverloadedDecl(name"xMethod")

    val Some(DefDef(_, _, _, Some(Apply(getXSelection, _)), _)) = xMethodSym.tree: @unchecked

    val (getXRef @ _: TermRef) = getXSelection.tpe: @unchecked

    assert(clue(getXRef.symbol) == getX)
  }

  testWithContext("select-field-from-java-class") {
    val BoxedJavaClass = ctx.findTopLevelClass("javacompat.BoxedJava")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val x = JavaDefinedClass.findDecl(name"x")
    val xFieldSym = BoxedJavaClass.findDecl(name"xField")

    val Some(DefDef(_, _, _, Some(xSelection), _)) = xFieldSym.tree: @unchecked

    val (xRef @ _: TermRef) = xSelection.tpe: @unchecked

    assert(clue(xRef.symbol) == x)
  }

  testWithContext("basic-scala-2-stdlib-class-dependency") {
    val BoxedConsClass = ctx.findTopLevelClass("scala2compat.BoxedCons")
    val ConsClass = ctx.findTopLevelClass("scala.collection.immutable.::")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val boxedSym = BoxedConsClass.findDecl(name"boxed")

    val app = boxedSym.declaredType.asInstanceOf[AppliedType]
    assert(clue(app.tycon).isOfClass(ConsClass))
    assert(clue(app.args).isListOf(_.isOfClass(JavaDefinedClass)))
  }

  testWithContext("select-method-from-scala-2-stdlib-class") {
    val BoxedConsClass = ctx.findTopLevelClass("scala2compat.BoxedCons")

    val fooSym = BoxedConsClass.findDecl(name"foo")

    val Some(DefDef(_, _, _, Some(Apply(canEqualSelection, _)), _)) = fooSym.tree: @unchecked

    val underlyingType = canEqualSelection.tpe match
      case termRef: TermRef => termRef.underlying
      case tpe              => fail("expected TermRef", clues(tpe))

    val mt = underlyingType.asInstanceOf[MethodType]
    assertEquals(List[TermName](name"that"), mt.paramNames, clue(mt.paramNames))
    assert(mt.paramTypes.sizeIs == 1, clue(mt.paramTypes))
    assert(mt.paramTypes.head.isOfClass(defn.AnyClass), clue(mt.paramTypes.head))
    assert(mt.resultType.isOfClass(defn.BooleanClass), clue(mt.resultType))
  }

  testWithContext("select-field-from-tasty-in-other-package:dependency-from-class-file") {
    val BoxedConstantsClass = ctx.findTopLevelClass("crosspackagetasty.BoxedConstants")
    val ConstantsClass = ctx.findTopLevelClass("simple_trees.Constants")

    val unitVal = ConstantsClass.findDecl(name"unitVal")
    val boxedUnitValSym = BoxedConstantsClass.findDecl(name"boxedUnitVal")

    val Some(DefDef(_, _, _, Some(unitValSelection), _)) = boxedUnitValSym.tree: @unchecked

    val (unitValRef @ _: TermRef) = unitValSelection.tpe: @unchecked

    assert(clue(unitValRef.symbol) == unitVal)
  }

  testWithContext("select-method-from-java-class-same-package-as-tasty") {
    // This tests reads top-level classes in the same package, defined by
    // both Java and Tasty. If we strictly require that all symbols are defined
    // exactly once, then we must be careful to not redefine `ScalaBox`/`JavaBox`
    // when scanning a package from the classpath.

    val ScalaBoxClass = ctx.findTopLevelClass("mixjavascala.ScalaBox")
    val JavaBoxClass = ctx.findTopLevelClass("mixjavascala.JavaBox")

    val getX = JavaBoxClass.findNonOverloadedDecl(name"getX")
    val xMethodSym = ScalaBoxClass.findNonOverloadedDecl(name"xMethod")

    val Some(DefDef(_, _, _, Some(Apply(getXSelection, _)), _)) = xMethodSym.tree: @unchecked

    val (getXRef @ _: TermRef) = getXSelection.tpe: @unchecked

    assert(clue(getXRef.symbol) == getX)
  }

  testWithContext("select-field-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testField").tree: @unchecked

    val Select(qual, fieldName) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isOfClass(GenClass), List(_.isOfClass(defn.IntClass))))
    assertEquals(fieldName, name"field")
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("select-getter-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testGetter").tree: @unchecked

    val Select(qual, getterName) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isOfClass(GenClass), List(_.isOfClass(defn.IntClass))))
    assertEquals(getterName, name"getter")
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("select-and-apply-method-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testMethod").tree: @unchecked

    val Apply(fun @ Select(qual, methodName), List(arg)) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isOfClass(GenClass), List(_.isOfClass(defn.IntClass))))
    methodName match {
      case SignedName(_, _, simpleName) => assertEquals(simpleName, name"method")
    }
    fun.tpe.widen match {
      case mt: MethodType =>
        assert(clue(mt.paramNames) == List(name"x"))
        assert(clue(mt.paramTypes.head).isOfClass(defn.IntClass))
        assert(clue(mt.resultType).isOfClass(defn.IntClass))
    }
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("select-and-apply-poly-method") {
    val GenMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) =
      PolySelect.findNonOverloadedDecl(name"testGenericMethod").tree: @unchecked

    val Apply(tapp @ TypeApply(fun @ Select(qual, methodName), List(targ)), List(arg)) = body: @unchecked

    assert(clue(qual.tpe).isOfClass(GenMethod))
    methodName match {
      case SignedName(_, _, simpleName) => assertEquals(simpleName, name"identity")
    }
    tapp.tpe.widen match {
      case mt: MethodType =>
        assert(clue(mt.paramNames) == List(name"x"))
        assert(clue(mt.paramTypes.head).isOfClass(defn.IntClass))
        assert(clue(mt.resultType).isOfClass(defn.IntClass))
    }
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("console-outvar-issue-78") {
    val Console = ctx.findTopLevelModuleClass("scala.Console")
    val DynamicVariable = ctx.findTopLevelClass("scala.util.DynamicVariable")

    val outVar = Console.findDecl(name"outVar")
    assert(clue(outVar.declaredType).isApplied(_.isRef(DynamicVariable), List(_ => true)))
  }

  testWithContext("scala-predef-declared-type") {
    val predef = ctx.findStaticTerm("scala.Predef")
    val Predef = ctx.findTopLevelModuleClass("scala.Predef")
    assert(clue(predef.declaredType).isRef(Predef))
  }

  testWithContext("scala.math.Ordering") {
    val OrderingModClass = ctx.findTopLevelModuleClass("scala.math.Ordering")
    assert(OrderingModClass.getNonOverloadedDecl(name"by").isDefined)
  }

  testWithContext("scala.math.Ordering.IntOrdering") {
    val IntOrderingClass = ctx.findStaticClass("scala.math.Ordering.IntOrdering")

    val compare = IntOrderingClass.findNonOverloadedDecl(name"compare")
    val mt = compare.declaredType.asInstanceOf[MethodType]
    assert(clue(mt.paramTypes(0)).isRef(defn.IntClass))
    assert(clue(mt.paramTypes(1)).isRef(defn.IntClass))
    assert(clue(mt.resultType).isRef(defn.IntClass))
  }

  testWithContext("scala.math.Ordering.Float.TotalOrdering") {
    val FloatTotalOrderingClass = ctx.findStaticClass("scala.math.Ordering.Float.TotalOrdering")

    val compare = FloatTotalOrderingClass.findNonOverloadedDecl(name"compare")
    val mt = compare.declaredType.asInstanceOf[MethodType]
    assert(clue(mt.paramTypes(0)).isRef(defn.FloatClass))
    assert(clue(mt.paramTypes(1)).isRef(defn.FloatClass))
    assert(clue(mt.resultType).isRef(defn.IntClass))
  }

  testWithContext("read-scala2-type-ref-type") {
    val RichBoolean = ctx.findTopLevelClass("scala.runtime.RichBoolean")
    val BooleanOrdering = ctx.findStaticTerm("scala.math.Ordering.Boolean")
    val ord = RichBoolean.findDecl(name"ord")
    assert(clue(ord.declaredType).isRef(BooleanOrdering))
  }

  testWithContext("read-encoded-scala2-type-ref-type") {
    val Function1Class = ctx.findTopLevelClass("scala.Function1")
    val SerializableClass = ctx.findTopLevelClass("java.io.Serializable")
    val TypeEqClass = ctx.findTopLevelClass("scala.=:=")
    val SubtypeClass = ctx.findTopLevelClass("scala.<:<")

    assert(clue(SubtypeClass.parentClasses) == List(defn.ObjectClass, Function1Class, SerializableClass))
    assert(clue(TypeEqClass.parentClasses) == List(SubtypeClass, SerializableClass))
  }

  testWithContext("scala2-type-alias") {
    val PredefString = ctx.findStaticType("scala.Predef.String")

    assert(clue(PredefString).isTypeAlias)
    assert(clue(PredefString.asInstanceOf[TypeMemberSymbol].aliasedType).isRef(defn.StringClass))
  }

  testWithContext("scala2-module-and-def-with-same-name") {
    val StringContext = ctx.findTopLevelClass("scala.StringContext")
    val sModuleClass = StringContext.findDecl(moduleClassName("s")).asClass

    val sDecls = StringContext.getAllOverloadedDecls(name"s")
    assert(clue(sDecls).sizeIs == 2)

    val (sModule, sDef) =
      if sDecls(0).is(Module) then (sDecls(0), sDecls(1))
      else
        assert(sDecls(1).is(Module))
        (sDecls(1), sDecls(0))

    assert(clue(sModule.asTerm.declaredType).isRef(sModuleClass))
    assert(clue(sDef.asTerm.declaredType).isInstanceOf[MethodType])
  }

  testWithContext("scala2-class-type-params") {
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")

    val List(targList) = ListClass.typeParams: @unchecked
    // TODO Set flags ClassTypeParam on TypeParams
    //assert(clue(targList.flags).isAllOf(ClassTypeParam))

    val List(targArray) = defn.ArrayClass.typeParams: @unchecked
    // TODO Set flags ClassTypeParam on TypeParams
    //assert(clue(targArray.flags).isAllOf(ClassTypeParam))
  }

  testWithContext("poly-type-in-higher-kinded") {
    val HigherKindedClass = ctx.findTopLevelClass("simple_trees.HigherKinded")
    val polyMethod = HigherKindedClass.findNonOverloadedDecl(name"m")
    assert(polyMethod.declaredType.asInstanceOf[PolyType].resultType.isInstanceOf[MethodType])
  }

  testWithContext("scala.collection.:+") {
    // type parameter C <: SeqOps[A, CC, C]
    ctx.findStaticModuleClass("scala.collection.package.:+")
  }

  testWithContext("read-scala.collection.mutable.StringBuilder_after-force-scala-pkg") {
    val scalaPackage = ctx.findPackage("scala")
    scalaPackage.declarations

    ctx.findTopLevelClass("scala.collection.mutable.StringBuilder")
  }

  testWithContext("linearization") {
    val SuperMonoClass = ctx.findStaticClass("inheritance.Overrides.SuperMono")
    val SuperMonoTraitClass = ctx.findStaticClass("inheritance.Overrides.SuperMonoTrait")
    val MidMonoClass = ctx.findStaticClass("inheritance.Overrides.MidMono")
    val ChildMonoClass = ctx.findStaticClass("inheritance.Overrides.ChildMono")

    val linTail = defn.ObjectClass :: defn.MatchableClass :: defn.AnyClass :: Nil

    assert(clue(SuperMonoClass.linearization) == SuperMonoClass :: linTail)
    assert(clue(SuperMonoTraitClass.linearization) == SuperMonoTraitClass :: linTail)

    val expectedMidMonoLin = MidMonoClass :: SuperMonoTraitClass :: SuperMonoClass :: linTail
    assert(clue(MidMonoClass.linearization) == expectedMidMonoLin)
    assert(clue(ChildMonoClass.linearization) == ChildMonoClass :: expectedMidMonoLin)
  }

  testWithContext("overrides-mono-no-overloads") {
    val SuperMonoClass = ctx.findStaticClass("inheritance.Overrides.SuperMono")
    val SuperMonoTraitClass = ctx.findStaticClass("inheritance.Overrides.SuperMonoTrait")
    val MidMonoClass = ctx.findStaticClass("inheritance.Overrides.MidMono")
    val ChildMonoClass = ctx.findStaticClass("inheritance.Overrides.ChildMono")

    val fooInSuper = SuperMonoClass.findNonOverloadedDecl(name"foo")
    val fooInChild = ChildMonoClass.findNonOverloadedDecl(name"foo")

    val barInSuperTrait = SuperMonoTraitClass.findNonOverloadedDecl(name"bar")
    val barInChild = ChildMonoClass.findNonOverloadedDecl(name"bar")

    val foobazInSuper = SuperMonoClass.findNonOverloadedDecl(name"foobaz")
    val foobazInChild = ChildMonoClass.findNonOverloadedDecl(name"foobaz")

    // From fooInSuper

    assert(clue(fooInSuper.overriddenSymbol(SuperMonoClass)) == Some(fooInSuper))
    assert(clue(fooInSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(fooInSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(fooInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(fooInSuper.overridingSymbol(SuperMonoClass)) == Some(fooInSuper))
    assert(clue(fooInSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(fooInSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(fooInSuper.overridingSymbol(ChildMonoClass)) == Some(fooInChild))

    assert(clue(fooInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(fooInSuper.nextOverriddenSymbol) == None)

    // From fooInChild

    assert(clue(fooInChild.overriddenSymbol(SuperMonoClass)) == Some(fooInSuper))
    assert(clue(fooInChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(fooInChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(fooInChild.overriddenSymbol(ChildMonoClass)) == Some(fooInChild))

    assert(clue(fooInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(fooInChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(fooInChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(fooInChild.overridingSymbol(ChildMonoClass)) == Some(fooInChild))

    assert(clue(fooInChild.allOverriddenSymbols.toList) == List(fooInSuper))
    assert(clue(fooInChild.nextOverriddenSymbol) == Some(fooInSuper))

    // From barInSuperTrait

    assert(clue(barInSuperTrait.overriddenSymbol(SuperMonoClass)) == None)
    assert(clue(barInSuperTrait.overriddenSymbol(SuperMonoTraitClass)) == Some(barInSuperTrait))
    assert(clue(barInSuperTrait.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(barInSuperTrait.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(barInSuperTrait.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(barInSuperTrait.overridingSymbol(SuperMonoTraitClass)) == Some(barInSuperTrait))
    assert(clue(barInSuperTrait.overridingSymbol(MidMonoClass)) == None)
    assert(clue(barInSuperTrait.overridingSymbol(ChildMonoClass)) == Some(barInChild))

    assert(clue(barInSuperTrait.allOverriddenSymbols.toList) == Nil)
    assert(clue(barInSuperTrait.nextOverriddenSymbol) == None)

    // From barInChild

    assert(clue(barInChild.overriddenSymbol(SuperMonoClass)) == None)
    assert(clue(barInChild.overriddenSymbol(SuperMonoTraitClass)) == Some(barInSuperTrait))
    assert(clue(barInChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(barInChild.overriddenSymbol(ChildMonoClass)) == Some(barInChild))

    assert(clue(barInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(barInChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(barInChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(barInChild.overridingSymbol(ChildMonoClass)) == Some(barInChild))

    assert(clue(barInChild.allOverriddenSymbols.toList) == List(barInSuperTrait))
    assert(clue(barInChild.nextOverriddenSymbol) == Some(barInSuperTrait))

    // From foobazInSuper

    assert(clue(foobazInSuper.overriddenSymbol(SuperMonoClass)) == Some(foobazInSuper))
    assert(clue(foobazInSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(foobazInSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(foobazInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(foobazInSuper.overridingSymbol(SuperMonoClass)) == Some(foobazInSuper))
    assert(clue(foobazInSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(foobazInSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(foobazInSuper.overridingSymbol(ChildMonoClass)) == Some(foobazInChild))

    assert(clue(foobazInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(foobazInSuper.nextOverriddenSymbol) == None)

    // From foobazInChild

    assert(clue(foobazInChild.overriddenSymbol(SuperMonoClass)) == Some(foobazInSuper))
    assert(clue(foobazInChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(foobazInChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(foobazInChild.overriddenSymbol(ChildMonoClass)) == Some(foobazInChild))

    assert(clue(foobazInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(foobazInChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(foobazInChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(foobazInChild.overridingSymbol(ChildMonoClass)) == Some(foobazInChild))

    assert(clue(foobazInChild.allOverriddenSymbols.toList) == List(foobazInSuper))
    assert(clue(foobazInChild.nextOverriddenSymbol) == Some(foobazInSuper))
  }

  testWithContext("overrides-mono-overloads") {
    val SuperMonoClass = ctx.findStaticClass("inheritance.Overrides.SuperMono")
    val SuperMonoTraitClass = ctx.findStaticClass("inheritance.Overrides.SuperMonoTrait")
    val MidMonoClass = ctx.findStaticClass("inheritance.Overrides.MidMono")
    val ChildMonoClass = ctx.findStaticClass("inheritance.Overrides.ChildMono")

    val IntClass = defn.IntClass
    val StringClass = defn.StringClass

    extension (meth: TermSymbol)
      def firstParamTypeIsRef(cls: Symbol): Boolean =
        meth.declaredType.asInstanceOf[MethodType].paramTypes.head.isRef(cls)
      def typeParamCountIs(count: Int): Boolean =
        meth.declaredType.asInstanceOf[PolyType].paramNames.sizeIs == count

    val overloadedInSuper = SuperMonoClass.findAllOverloadedDecls(name"overloaded")
    val intInSuper = overloadedInSuper.find(_.firstParamTypeIsRef(IntClass)).get
    val stringInSuper = overloadedInSuper.find(_.firstParamTypeIsRef(StringClass)).get

    val overloadedInChild = ChildMonoClass.findAllOverloadedDecls(name"overloaded")
    val intInChild = overloadedInChild.find(_.firstParamTypeIsRef(IntClass)).get
    val stringInChild = overloadedInChild.find(_.firstParamTypeIsRef(StringClass)).get

    val polyInSuper = SuperMonoClass.findAllOverloadedDecls(name"overloadedPoly")
    val poly1InSuper = polyInSuper.find(_.typeParamCountIs(1)).get
    val poly2InSuper = polyInSuper.find(_.typeParamCountIs(2)).get

    val polyInChild = ChildMonoClass.findAllOverloadedDecls(name"overloadedPoly")
    val poly1InChild = polyInChild.find(_.typeParamCountIs(1)).get
    val poly2InChild = polyInChild.find(_.typeParamCountIs(2)).get

    // From intInSuper

    assert(clue(intInSuper.overriddenSymbol(SuperMonoClass)) == Some(intInSuper))
    assert(clue(intInSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(intInSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(intInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(intInSuper.overridingSymbol(SuperMonoClass)) == Some(intInSuper))
    assert(clue(intInSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(intInSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(intInSuper.overridingSymbol(ChildMonoClass)) == Some(intInChild))

    assert(clue(intInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(intInSuper.nextOverriddenSymbol) == None)

    // From intInChild

    assert(clue(intInChild.overriddenSymbol(SuperMonoClass)) == Some(intInSuper))
    assert(clue(intInChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(intInChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(intInChild.overriddenSymbol(ChildMonoClass)) == Some(intInChild))

    assert(clue(intInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(intInChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(intInChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(intInChild.overridingSymbol(ChildMonoClass)) == Some(intInChild))

    assert(clue(intInChild.allOverriddenSymbols.toList) == List(intInSuper))
    assert(clue(intInChild.nextOverriddenSymbol) == Some(intInSuper))

    // From stringInSuper

    assert(clue(stringInSuper.overriddenSymbol(SuperMonoClass)) == Some(stringInSuper))
    assert(clue(stringInSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(stringInSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(stringInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(stringInSuper.overridingSymbol(SuperMonoClass)) == Some(stringInSuper))
    assert(clue(stringInSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(stringInSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(stringInSuper.overridingSymbol(ChildMonoClass)) == Some(stringInChild))

    assert(clue(stringInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(stringInSuper.nextOverriddenSymbol) == None)

    // From stringInChild

    assert(clue(stringInChild.overriddenSymbol(SuperMonoClass)) == Some(stringInSuper))
    assert(clue(stringInChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(stringInChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(stringInChild.overriddenSymbol(ChildMonoClass)) == Some(stringInChild))

    assert(clue(stringInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(stringInChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(stringInChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(stringInChild.overridingSymbol(ChildMonoClass)) == Some(stringInChild))

    assert(clue(stringInChild.allOverriddenSymbols.toList) == List(stringInSuper))
    assert(clue(stringInChild.nextOverriddenSymbol) == Some(stringInSuper))

    // From poly1InSuper

    assert(clue(poly1InSuper.overriddenSymbol(SuperMonoClass)) == Some(poly1InSuper))
    assert(clue(poly1InSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly1InSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(poly1InSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(poly1InSuper.overridingSymbol(SuperMonoClass)) == Some(poly1InSuper))
    assert(clue(poly1InSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly1InSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(poly1InSuper.overridingSymbol(ChildMonoClass)) == Some(poly1InChild))

    assert(clue(poly1InSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(poly1InSuper.nextOverriddenSymbol) == None)

    // From poly1InChild

    assert(clue(poly1InChild.overriddenSymbol(SuperMonoClass)) == Some(poly1InSuper))
    assert(clue(poly1InChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly1InChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(poly1InChild.overriddenSymbol(ChildMonoClass)) == Some(poly1InChild))

    assert(clue(poly1InChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(poly1InChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly1InChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(poly1InChild.overridingSymbol(ChildMonoClass)) == Some(poly1InChild))

    assert(clue(poly1InChild.allOverriddenSymbols.toList) == List(poly1InSuper))
    assert(clue(poly1InChild.nextOverriddenSymbol) == Some(poly1InSuper))

    // From poly2InSuper

    assert(clue(poly2InSuper.overriddenSymbol(SuperMonoClass)) == Some(poly2InSuper))
    assert(clue(poly2InSuper.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly2InSuper.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(poly2InSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(poly2InSuper.overridingSymbol(SuperMonoClass)) == Some(poly2InSuper))
    assert(clue(poly2InSuper.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly2InSuper.overridingSymbol(MidMonoClass)) == None)
    assert(clue(poly2InSuper.overridingSymbol(ChildMonoClass)) == Some(poly2InChild))

    assert(clue(poly2InSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(poly2InSuper.nextOverriddenSymbol) == None)

    // From poly2InChild

    assert(clue(poly2InChild.overriddenSymbol(SuperMonoClass)) == Some(poly2InSuper))
    assert(clue(poly2InChild.overriddenSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly2InChild.overriddenSymbol(MidMonoClass)) == None)
    assert(clue(poly2InChild.overriddenSymbol(ChildMonoClass)) == Some(poly2InChild))

    assert(clue(poly2InChild.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(poly2InChild.overridingSymbol(SuperMonoTraitClass)) == None)
    assert(clue(poly2InChild.overridingSymbol(MidMonoClass)) == None)
    assert(clue(poly2InChild.overridingSymbol(ChildMonoClass)) == Some(poly2InChild))

    assert(clue(poly2InChild.allOverriddenSymbols.toList) == List(poly2InSuper))
    assert(clue(poly2InChild.nextOverriddenSymbol) == Some(poly2InSuper))
  }

  testWithContext("overrides-cannot-override") {
    val SuperMonoClass = ctx.findStaticClass("inheritance.Overrides.SuperMono")
    val ChildMonoClass = ctx.findStaticClass("inheritance.Overrides.ChildMono")

    val superCtor = SuperMonoClass.findNonOverloadedDecl(nme.Constructor)
    val childCtor = ChildMonoClass.findNonOverloadedDecl(nme.Constructor)

    val superPrivate = SuperMonoClass.findNonOverloadedDecl(name"privateMethod")
    val childPrivate = ChildMonoClass.findNonOverloadedDecl(name"privateMethod")

    // From superCtor

    assert(clue(superCtor.overriddenSymbol(SuperMonoClass)) == Some(superCtor))
    assert(clue(superCtor.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(superCtor.overridingSymbol(SuperMonoClass)) == Some(superCtor))
    assert(clue(superCtor.overridingSymbol(ChildMonoClass)) == None)

    assert(clue(superCtor.allOverriddenSymbols.toList) == Nil)
    assert(clue(superCtor.nextOverriddenSymbol) == None)

    // From childCtor

    assert(clue(childCtor.overriddenSymbol(SuperMonoClass)) == None)
    assert(clue(childCtor.overriddenSymbol(ChildMonoClass)) == Some(childCtor))

    assert(clue(childCtor.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(childCtor.overridingSymbol(ChildMonoClass)) == Some(childCtor))

    assert(clue(childCtor.allOverriddenSymbols.toList) == Nil)
    assert(clue(childCtor.nextOverriddenSymbol) == None)

    // From superPrivate

    assert(clue(superPrivate.overriddenSymbol(SuperMonoClass)) == Some(superPrivate))
    assert(clue(superPrivate.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(superPrivate.overridingSymbol(SuperMonoClass)) == Some(superPrivate))
    assert(clue(superPrivate.overridingSymbol(ChildMonoClass)) == None)

    assert(clue(superPrivate.allOverriddenSymbols.toList) == Nil)
    assert(clue(superPrivate.nextOverriddenSymbol) == None)

    // From childPrivate

    assert(clue(childPrivate.overriddenSymbol(SuperMonoClass)) == None)
    assert(clue(childPrivate.overriddenSymbol(ChildMonoClass)) == Some(childPrivate))

    assert(clue(childPrivate.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(childPrivate.overridingSymbol(ChildMonoClass)) == Some(childPrivate))

    assert(clue(childPrivate.allOverriddenSymbols.toList) == Nil)
    assert(clue(childPrivate.nextOverriddenSymbol) == None)
  }

  testWithContext("overrides-poly") {
    val SuperPolyClass = ctx.findStaticClass("inheritance.Overrides.SuperPoly")
    val ChildPolyClass = ctx.findStaticClass("inheritance.Overrides.ChildPoly")

    val List(superPolyA, superPolyB) = SuperPolyClass.typeParams: @unchecked
    val List(childPolyX) = ChildPolyClass.typeParams: @unchecked

    val IntClass = defn.IntClass

    extension (meth: TermSymbol)
      def firstParamTypeIsRef(cls: Symbol): Boolean =
        meth.declaredType.asInstanceOf[MethodType].paramTypes.head.isRef(cls)

    val fooInSuper = SuperPolyClass.findAllOverloadedDecls(name"foo")
    val fooAInSuper = fooInSuper.find(_.firstParamTypeIsRef(superPolyA)).get
    val fooBInSuper = fooInSuper.find(_.firstParamTypeIsRef(superPolyB)).get

    val fooInChild = ChildPolyClass.findAllOverloadedDecls(name"foo")
    val fooXInChild = fooInChild.find(_.firstParamTypeIsRef(childPolyX)).get
    val fooIntInChild = fooInChild.find(_.firstParamTypeIsRef(IntClass)).get

    // From fooAInSuper

    assert(clue(fooAInSuper.overriddenSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooAInSuper.overriddenSymbol(ChildPolyClass)) == None)

    assert(clue(fooAInSuper.overridingSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooAInSuper.overridingSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooAInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(fooAInSuper.nextOverriddenSymbol) == None)

    // From fooXInChild

    assert(clue(fooXInChild.overriddenSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooXInChild.overriddenSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooXInChild.overridingSymbol(SuperPolyClass)) == None)
    assert(clue(fooXInChild.overridingSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooXInChild.allOverriddenSymbols.toList) == List(fooAInSuper))
    assert(clue(fooXInChild.nextOverriddenSymbol) == Some(fooAInSuper))

    // From fooBInSuper

    assert(clue(fooBInSuper.overriddenSymbol(SuperPolyClass)) == Some(fooBInSuper))
    assert(clue(fooBInSuper.overriddenSymbol(ChildPolyClass)) == None)

    assert(clue(fooBInSuper.overridingSymbol(SuperPolyClass)) == Some(fooBInSuper))
    assert(clue(fooBInSuper.overridingSymbol(ChildPolyClass)) == Some(fooIntInChild))

    assert(clue(fooBInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(fooBInSuper.nextOverriddenSymbol) == None)

    // From fooIntInChild

    assert(clue(fooIntInChild.overriddenSymbol(SuperPolyClass)) == Some(fooBInSuper))
    assert(clue(fooIntInChild.overriddenSymbol(ChildPolyClass)) == Some(fooIntInChild))

    assert(clue(fooIntInChild.overridingSymbol(SuperPolyClass)) == None)
    assert(clue(fooIntInChild.overridingSymbol(ChildPolyClass)) == Some(fooIntInChild))

    assert(clue(fooIntInChild.allOverriddenSymbols.toList) == List(fooBInSuper))
    assert(clue(fooIntInChild.nextOverriddenSymbol) == Some(fooBInSuper))
  }

  testWithContext("overrides-relaxed") {
    val SuperMonoClass = ctx.findStaticClass("inheritance.Overrides.SuperMono")
    val ChildMonoClass = ctx.findStaticClass("inheritance.Overrides.ChildMono")

    val anyToString = defn.AnyClass.findNonOverloadedDecl(name"toString")
    val objectToString = defn.ObjectClass.findNonOverloadedDecl(name"toString")
    val superToString = SuperMonoClass.findNonOverloadedDecl(name"toString")
    val childToString = ChildMonoClass.findNonOverloadedDecl(name"toString")

    // From objectToString

    assert(clue(objectToString.overriddenSymbol(defn.ObjectClass)) == Some(objectToString))
    assert(clue(objectToString.overriddenSymbol(SuperMonoClass)) == None)
    assert(clue(objectToString.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(objectToString.overridingSymbol(defn.ObjectClass)) == Some(objectToString))
    assert(clue(objectToString.overridingSymbol(SuperMonoClass)) == Some(superToString))
    assert(clue(objectToString.overridingSymbol(ChildMonoClass)) == Some(childToString))

    assert(clue(objectToString.allOverriddenSymbols.toList) == List(anyToString))
    assert(clue(objectToString.nextOverriddenSymbol) == Some(anyToString))

    // From superToString

    assert(clue(superToString.overriddenSymbol(defn.ObjectClass)) == Some(objectToString))
    assert(clue(superToString.overriddenSymbol(SuperMonoClass)) == Some(superToString))
    assert(clue(superToString.overriddenSymbol(ChildMonoClass)) == None)

    assert(clue(superToString.overridingSymbol(defn.ObjectClass)) == None)
    assert(clue(superToString.overridingSymbol(SuperMonoClass)) == Some(superToString))
    assert(clue(superToString.overridingSymbol(ChildMonoClass)) == Some(childToString))

    assert(clue(superToString.allOverriddenSymbols.toList) == List(objectToString, anyToString))
    assert(clue(superToString.nextOverriddenSymbol) == Some(objectToString))

    // From childToString

    assert(clue(childToString.overriddenSymbol(defn.ObjectClass)) == Some(objectToString))
    assert(clue(childToString.overriddenSymbol(SuperMonoClass)) == Some(superToString))
    assert(clue(childToString.overriddenSymbol(ChildMonoClass)) == Some(childToString))

    assert(clue(childToString.overridingSymbol(defn.ObjectClass)) == None)
    assert(clue(childToString.overridingSymbol(SuperMonoClass)) == None)
    assert(clue(childToString.overridingSymbol(ChildMonoClass)) == Some(childToString))

    assert(clue(childToString.allOverriddenSymbols.toList) == List(superToString, objectToString, anyToString))
    assert(clue(childToString.nextOverriddenSymbol) == Some(superToString))
  }

  def companionClassFullCycle(owner: DeclaringSymbol, baseName: String)(using Context, munit.Location): Unit = {
    val cls: ClassSymbol = owner.getDecl(typeName(baseName)).get.asClass
    val moduleClass: ClassSymbol = owner.getDecl(moduleClassName(baseName)).get.asClass
    val moduleValue: TermSymbol = owner.getDecl(termName(baseName)).get.asTerm

    assert(clue(cls.companionClass) == Some(moduleClass))
    assert(clue(moduleClass.companionClass) == Some(cls))

    assert(clue(cls.moduleValue) == None)
    assert(clue(moduleClass.moduleValue) == Some(moduleValue))
  }

  testWithContext("companion-tests-module-value") {
    companionClassFullCycle(ctx.findPackage("companions"), "CompanionObject")
  }

  testWithContext("companion-tests-nested-module-value") {
    companionClassFullCycle(ctx.findTopLevelModuleClass("companions.CompanionObject"), "NestedObject")
  }

  testWithContext("companion-tests-class-nested-module-value") {
    companionClassFullCycle(ctx.findTopLevelClass("companions.CompanionObject"), "ClassNestedObject")
  }

  testWithContext("findMember and private members") {
    val PrivateOverridesClass = ctx.findTopLevelModuleClass("inheritance.PrivateOverrides")
    val ParentClass = ctx.findStaticClass("inheritance.PrivateOverrides.Parent")
    val ChildClass = ctx.findStaticClass("inheritance.PrivateOverrides.Child")
    val InnerClass = ChildClass.findDecl(typeName("Inner")).asClass

    val setupMethod = ctx.findTopLevelModuleClass("inheritance.PrivateOverrides").findNonOverloadedDecl(name"testSetup")
    val setupMethodDef = setupMethod.tree.get.asInstanceOf[DefDef]

    // Direct `findMember` test (whitebox)
    val child = findLocalValDef(setupMethodDef.rhs.get, name"child")
    val memberSym = ChildClass.findMember(TermRef(NoPrefix, child), termName("y")).get
    assert(clue(memberSym.owner) == ParentClass)

    val wInParent = ParentClass.findDecl(termName("w"))
    val xInParent = ParentClass.findDecl(termName("x"))
    val yInParent = ParentClass.findDecl(termName("y"))
    assert(clue(ParentClass.getDecl(termName("z"))).isEmpty)

    assert(!clue(wInParent.flags).isAnyOf(Local | ParamAccessor | Private))
    assert(clue(xInParent.flags).isAllOf(ParamAccessor, butNotAnyOf = Local | Private))
    assert(!clue(yInParent.flags).isAnyOf(Local | ParamAccessor | Private))

    assert(clue(ChildClass.getDecl(termName("w"))).isEmpty)
    val xInChild = ChildClass.findDecl(termName("x"))
    val yInChild = ChildClass.findDecl(termName("y"))
    val zInChild = ChildClass.findDecl(termName("z"))

    assert(clue(xInChild.flags).isAllOf(Local | ParamAccessor | Private))
    assert(clue(yInChild.flags).isAllOf(Local | ParamAccessor | Private))
    assert(clue(zInChild.flags).isAllOf(ParamAccessor, butNotAnyOf = Local | Private))

    assert(clue(InnerClass.getDecl(termName("w"))).isEmpty)
    assert(clue(InnerClass.getDecl(termName("x"))).isEmpty)
    val yInInner = InnerClass.findDecl(termName("y"))
    val zInInner = InnerClass.findDecl(termName("z"))

    assert(clue(yInInner.flags).isAllOf(Local | ParamAccessor | Private))
    assert(clue(zInInner.flags).isAllOf(Local | ParamAccessor | Private))

    // Test Select from outside the class
    for fStr <- List("w", "x", "y", "z") do
      val fStrUp = fStr.toUpperCase()
      val fName = termName(fStr)

      def fInParent = ParentClass.findDecl(fName)
      def fInChild = ChildClass.findDecl(fName)
      def fInInner = InnerClass.findDecl(fName)

      // Select nodes from outside the class
      locally {
        val selectNode = findTree(setupMethodDef.rhs.get) { case select @ Select(_, `fName`) =>
          select
        }
        val selectTpe = selectNode.tpe.asInstanceOf[TermRef]
        assert(clue(selectTpe.name) == clue(fName), fStr)
        val selectSym = selectTpe.symbol

        val expectedOwner = if fStr == "z" then ChildClass else ParentClass
        assert(clue(selectSym.owner) == clue(expectedOwner), fStr)

        val expectedParamAccessor = fStr != "w" && fStr != "y"
        assert(selectSym.is(ParamAccessor) == clue(expectedParamAccessor), fStr)

        assert(!selectSym.is(Private), fStr)
      }

      // Ident from inside the class
      locally {
        val methodSym = ChildClass.findNonOverloadedDecl(termName(s"readIdent$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) {
          case ident @ Ident(`fName`) if fStr != "w"      => ident.symbol
          case select @ Select(_, `fName`) if fStr == "w" => select.symbol
        }
        val expectedSym = if fStr == "w" then fInParent else fInChild
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Select with `this.` from inside the class
      locally {
        val methodSym = ChildClass.findNonOverloadedDecl(termName(s"readThis$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) { case select @ Select(_, `fName`) =>
          select.symbol
        }
        val expectedSym = if fStr == "w" then fInParent else fInChild
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Select with `self.` from inside the class
      locally {
        val methodSym = ChildClass.findNonOverloadedDecl(termName(s"readSelf$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) { case select @ Select(_, `fName`) =>
          select.symbol
        }
        val expectedSym = if fStr == "z" then fInChild else fInParent
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Select with `child.` from outside the class
      locally {
        val methodSym = PrivateOverridesClass.findNonOverloadedDecl(termName("testSetup"))
        val selectedSymbol = findTree(methodSym.tree.get) { case select @ Select(_, `fName`) =>
          select.symbol
        }
        val expectedSym = if fStr == "z" then fInChild else fInParent
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Ident from inside an inner class
      locally {
        val methodSym = InnerClass.findNonOverloadedDecl(termName(s"readIdent$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) {
          case ident @ Ident(`fName`) if fStr == "y" || fStr == "z"      => ident.symbol
          case select @ Select(_, `fName`) if fStr == "w" || fStr == "x" => select.symbol
        }
        val expectedSym =
          if fStr == "w" then fInParent
          else if fStr == "x" then fInChild
          else fInInner
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Select with `Child.this.` from an inner class
      locally {
        val methodSym = InnerClass.findNonOverloadedDecl(termName(s"readChildThis$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) { case select @ Select(_, `fName`) =>
          select.symbol
        }
        val expectedSym = if fStr == "w" then fInParent else fInChild
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      }

      // Select with `this.` from an inner class -- only for 'y' and 'z'
      if fStr == "y" || fStr == "z" then
        val methodSym = InnerClass.findNonOverloadedDecl(termName(s"readThis$fStrUp"))
        val selectedSymbol = findTree(methodSym.tree.get) { case select @ Select(_, `fName`) =>
          select.symbol
        }
        val expectedSym = fInInner
        assert(clue(selectedSymbol) == clue(expectedSym), fStr)
      end if
    end for
  }

  testWithContext("annotations") {
    val AnnotationsClass = ctx.findTopLevelClass("simple_trees.Annotations")
    val inlineClass = ctx.findTopLevelClass("scala.inline")
    val deprecatedClass = ctx.findTopLevelClass("scala.deprecated")

    locally {
      val inlineMethodSym = AnnotationsClass.findNonOverloadedDecl(termName("inlineMethod"))
      val List(inlineAnnot) = inlineMethodSym.annotations
      assert(clue(inlineAnnot.symbol) == inlineClass)
      assert(clue(inlineAnnot.arguments).isEmpty)

      assert(inlineMethodSym.hasAnnotation(inlineClass))
      assert(!inlineMethodSym.hasAnnotation(deprecatedClass))

      assert(inlineMethodSym.getAnnotations(inlineClass) == List(inlineAnnot))
      assert(inlineMethodSym.getAnnotations(deprecatedClass) == Nil)

      assert(inlineMethodSym.getAnnotation(inlineClass) == Some(inlineAnnot))
      assert(inlineMethodSym.getAnnotation(deprecatedClass) == None)
    }

    locally {
      val deprecatedValSym = AnnotationsClass.findNonOverloadedDecl(termName("deprecatedVal"))
      val List(deprecatedAnnot) = deprecatedValSym.annotations

      assert(clue(deprecatedAnnot.symbol) == deprecatedClass)
      assert(clue(deprecatedAnnot.annotConstructor) == deprecatedClass.findNonOverloadedDecl(nme.Constructor))
      assert(clue(deprecatedAnnot.argCount) == 2)

      deprecatedAnnot.arguments match
        case List(Literal(Constant("reason")), Literal(Constant("forever"))) =>
          () // OK
        case args =>
          fail("unexpected arguments", clues(args))

      assert(clue(deprecatedAnnot.argIfConstant(0)) == Some(Constant("reason")))
      assert(clue(deprecatedAnnot.argIfConstant(1)) == Some(Constant("forever")))
    }
  }

  testWithContext("uninitialized-var") {
    val UninitializedClass = ctx.findTopLevelClass("simple_trees.Uninitialized")

    val uninitializedMethod = defn.uninitializedMethod.get

    for varName <- List("wildcardRHS", "uninitializedRHS", "renamedUninitializedRHS") do
      val varSym = UninitializedClass.findDecl(termName(varName))
      val ValDef(_, _, Some(rhs), _) = varSym.tree.get: @unchecked
      assert(clue(rhs.tpe).isRef(uninitializedMethod))
  }

  testWithContext("methods on Any") {
    val AnyMethodsClass = ctx.findTopLevelClass("simple_trees.AnyMethods")
    val ClassClass = ctx.findTopLevelClass("java.lang.Class")
    val ProductClass = ctx.findTopLevelClass("scala.Product")

    def rhsOf(methodName: String): TermTree =
      AnyMethodsClass.findNonOverloadedDecl(termName(methodName)).tree.get.asInstanceOf[DefDef].rhs.get

    def isAnyMethod(sym: Symbol, name: SimpleName): Boolean =
      sym.owner == defn.AnyClass && sym.name == name

    def testApply(testMethodName: String, targetMethodName: SimpleName, expectedType: Type => Boolean): Unit =
      val rhs @ Apply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    def testDirect(testMethodName: String, targetMethodName: SimpleName, expectedType: Type => Boolean): Unit =
      val fun @ (_: Select) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(fun.tpe.widen)), testMethodName)

    def testTypeApply(testMethodName: String, targetMethodName: SimpleName, expectedType: Type => Boolean): Unit =
      val rhs @ TypeApply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    def testApplyTypeApply(testMethodName: String, targetMethodName: SimpleName, expectedType: Type => Boolean): Unit =
      val rhs @ Apply(TypeApply(fun: Select, _), _) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    testApply("testEqEq", nme.m_==, _.isRef(defn.BooleanClass))
    testApply("testNEq", nme.m_!=, _.isRef(defn.BooleanClass))
    testDirect("testHashHash", nme.m_##, _.isRef(defn.IntClass))

    testApply("testEquals", nme.m_equals, _.isRef(defn.BooleanClass))
    testApply("testHashCode", nme.m_hashCode, _.isRef(defn.IntClass))

    testApply("testToString", nme.m_toString, _.isRef(defn.StringClass))

    testTypeApply("testIsInstanceOfInt", nme.m_isInstanceOf, _.isRef(defn.BooleanClass))
    testTypeApply("testIsInstanceOfProduct", nme.m_isInstanceOf, _.isRef(defn.BooleanClass))

    testTypeApply("testAsInstanceOfInt", nme.m_asInstanceOf, _.isRef(defn.IntClass))
    testTypeApply("testAsInstanceOfProduct", nme.m_asInstanceOf, _.isRef(ProductClass))

    testTypeApply("testTypeCast", termName("$asInstanceOf$"), _.isRef(defn.IntClass))

    testApplyTypeApply(
      "testGetClassAny",
      nme.m_getClass,
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isRef(defn.NothingClass), _.isRef(defn.AnyClass))))
    )
    testApplyTypeApply(
      "testGetClassProduct",
      nme.m_getClass,
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isRef(defn.NothingClass), _.isRef(ProductClass))))
    )

    /* `int.getClass()` should select the `Int.getClass(): Class[Int]` overload,
     * and hence have type `Class[Int]`, not `Class[? <: Int]`.
     * However, the TASTy contains a `SelectIn` with a `TypeRef` to `scala.Any`
     * as selection owner, which gives the result type `Class[? <: Int]`.
     * Despite that, Scala 3 allows to assign the result to a `Class[Int]`,
     * so there is a bug somewhere in the compiler.
     */
    testApplyTypeApply(
      "testGetClassInt",
      nme.m_getClass,
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isRef(defn.NothingClass), _.isRef(defn.IntClass))))
    )
  }

}
