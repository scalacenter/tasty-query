package tastyquery

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Modifiers.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Traversers.TreeTraverser
import tastyquery.Trees.*
import tastyquery.Types.*

import TestUtils.*

class TypeSuite extends UnrestrictedUnpicklingSuite {
  extension [T](elems: List[T])
    def isListOf(tests: (T => Boolean)*)(using Context): Boolean =
      elems.corresponds(tests)((t, test) => test(t))

  extension (tpe: TypeMappable)
    def isType(pred: Type => Boolean)(using Context): Boolean = tpe match
      case tpe: Type => pred(tpe)
      case _         => false

    def isWildcard(using Context): Boolean =
      isBounded(_.isNothing, _.isAny)

    def isBounded(lo: Type => Boolean, hi: Type => Boolean)(using Context): Boolean = tpe match
      case tpe: WildcardTypeArg => lo(tpe.bounds.low) && hi(tpe.bounds.high)
      case _                    => false

    def isTypeRefOf(cls: ClassSymbol)(using Context): Boolean = tpe match
      case TypeRef.OfClass(tpeCls) => tpeCls == cls
      case _                       => false

    def isRef(sym: TypeSymbol)(using Context): Boolean = tpe match
      case tpe: TypeRef => tpe.optSymbol.contains(sym)
      case _            => false

    def isRef(sym: TermSymbol)(using Context): Boolean = tpe match
      case tpe: TermRef => tpe.symbol == sym
      case _            => false

    def isOfClass(cls: ClassSymbol)(using Context): Boolean = tpe match
      case tpe: TermRef => tpe.underlying.isRef(cls)
      case _            => false

    def isAny(using Context): Boolean = tpe.isRef(defn.AnyClass)

    def isNothing(using Context): Boolean = tpe.isType(_.dealias.isInstanceOf[NothingType])

    def isIntersectionOf(tpes: (Type => Boolean)*)(using Context): Boolean =
      tpe match
        case tpe: Type =>
          def parts(tpe: Type): List[Type] = tpe match
            case tpe: AndType => tpe.parts
            case tpe: Type    => tpe :: Nil
          parts(tpe).isListOf(tpes*)
        case _ =>
          false
    end isIntersectionOf

    def isUnionOf(tpes: (Type => Boolean)*)(using Context): Boolean =
      tpe match
        case tpe: Type =>
          def parts(tpe: Type): List[Type] = tpe match
            case tpe: OrType => parts(tpe.first) ::: parts(tpe.second)
            case _           => tpe :: Nil
          parts(tpe).isListOf(tpes*)
        case _ =>
          false
    end isUnionOf

    def isApplied(cls: Type => Boolean, argRefs: Seq[TypeOrWildcard => Boolean])(using Context): Boolean =
      tpe match
        case tpe: TermType =>
          tpe.widenTermRef match
            case app: AppliedType if cls(app.tycon) =>
              app.args.corresponds(argRefs)((arg, argRef) => argRef(arg))
            case _ => false
        case _ =>
          false
    end isApplied

    def isByName(arg: Type => Boolean)(using Context): Boolean =
      tpe match
        case tpe: ByNameType => arg(tpe.resultType)
        case _               => false

    def isRepeated(elemType: Type => Boolean)(using Context): Boolean =
      tpe match
        case tpe: RepeatedType => elemType(tpe.elemType)
        case _                 => false

    def isArrayOf(arg: TypeOrWildcard => Boolean)(using Context): Boolean =
      isApplied(_.isTypeRefOf(defn.ArrayClass), Seq(arg))

    def isConstant(constant: Constant)(using Context): Boolean = tpe match
      case tpe: ConstantType => tpe.value == constant
      case _                 => false

    def isAnnotated(parent: Type => Boolean, annotation: Annotation => Boolean)(using Context): Boolean = tpe match
      case tpe: AnnotatedType => parent(tpe.typ) && annotation(tpe.annotation)
      case _                  => false
  end extension

  extension (bounds: TypeBounds)
    def isNothingAnyBounds(using Context): Boolean =
      isBounds(_.isNothing, _.isAny)

    def isJavaNothingAnyBounds(using Context): Boolean =
      isBounds(_.isNothing, _.isFromJavaObject)

    def isBounds(low: Type => Boolean, high: Type => Boolean)(using Context): Boolean =
      low(bounds.low) && high(bounds.high)
  end extension

  testWithContext("hierarchy-partitions") {
    /* These no-op matches test that the set of all possible `TypeMappable`s is
     * partitioned into certain sets of sub-classes and sub-traits.
     */

    def groundAndProxy(tp: Type): Int = tp match
      case _: GroundType => 1
      case _: TypeProxy  => 2

    def termTypes(tp: TermType): Int = tp match
      case _: TypeOrMethodic => 1
      case _: PackageRef     => 2

    def typeOrMethodic(tp: TypeOrMethodic): Int = tp match
      case _: Type         => 1
      case _: MethodicType => 2

    def methodicType(tp: MethodicType): Int = tp match
      case _: MethodType => 1
      case _: PolyType   => 2

    def typeOrWildcard(tp: TypeOrWildcard): Int = tp match
      case _: Type            => 1
      case _: WildcardTypeArg => 2

    def prefix(tp: Prefix): Int = tp match
      case NoPrefix          => 1
      case _: NonEmptyPrefix => 2

    def nonEmptyPrefix(tp: NonEmptyPrefix): Int = tp match
      case _: Type       => 1
      case _: PackageRef => 2

    // Nothing to do
    ()
  }

  testWithContext("apply-dependent") {
    val DependentMethodClass = ctx.findTopLevelClass("simple_trees.DependentMethod")
    val testVal = DependentMethodClass.findNonOverloadedDecl(name"test")
    val testDef = testVal.tree.get.asInstanceOf[ValDef]
    val applyTree = testDef.rhs.get.asInstanceOf[Apply]
    assert(clue(applyTree.tpe).isConstant(Constant("hello")))
  }

  testWithContext("apply-recursive") {
    val RecApplyClass = ctx.findTopLevelClass("simple_trees.RecApply")

    val gcdSym = RecApplyClass.findNonOverloadedDecl(name"gcd")
    val NumClass = RecApplyClass.findDecl(tname"Num").asClass

    val Some(gcdTree: DefDef) = gcdSym.tree: @unchecked

    var recCallCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case recCall @ Apply(gcdRef @ Select(_, SignedName(SimpleName("gcd"), _, _)), _) =>
          recCallCount += 1
          assert(gcdRef.tpe.isRef(gcdSym), clue(gcdRef))
          assert(recCall.tpe.isRef(NumClass), clue(recCall))
        case _ =>
          super.traverse(tree)
    }.traverse(gcdTree)

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

  def applyOverloadedTest(name: String)(
    callMethod: String,
    checkParamType: Context ?=> Type => Boolean,
    checkResultType: Context ?=> TermType => Boolean = _.isRef(defn.UnitClass)
  ): Unit =
    testWithContext(name) {
      val OverloadedApplyClass = ctx.findTopLevelClass("simple_trees.OverloadedApply")

      val callSym = OverloadedApplyClass.findDecl(termName(callMethod))

      val Some(callTree: DefDef) = callSym.tree: @unchecked

      var callCount = 0

      new TreeTraverser {
        override def traverse(tree: Tree): Unit = tree match
          case app @ Apply(fooRef @ Select(_, SignedName(SimpleName("foo"), _, _)), _) =>
            callCount += 1
            assert(checkResultType(app.tpe), clue(app))
            val fooSym = fooRef.tpe.asInstanceOf[TermRef].symbol
            val mt = fooSym.declaredType.asInstanceOf[MethodType]
            assert(checkResultType(clue(mt.resultType)))
            assert(checkParamType(clue(mt.paramTypes.head)))
          case _ =>
            super.traverse(tree)
      }.traverse(callTree)

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
  applyOverloadedTest("apply-overloaded-arrayObj")("callD", _.isArrayOf(_ => true))
  applyOverloadedTest("apply-overloaded-byName")(
    "callE",
    _.isByName(_.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Num")))
  )
  applyOverloadedTest("apply-overloaded-gen-target-name")(
    "callG",
    _.isApplied(
      _.isRef(ctx.findTopLevelClass("simple_trees.OverloadedApply").findDecl(tname"Box")),
      List(_.isRef(defn.IntClass))
    )
  )
  applyOverloadedTest("apply-overloaded-nothing")("callH", _.isRef(defn.StringClass), _.isType(_.isExactlyNothing))
  applyOverloadedTest("apply-overloaded-null")(
    "callI",
    _.isRef(ctx.findTopLevelClass("java.lang.CharSequence")),
    _.isRef(defn.NullClass)
  )

  testWithContext("apply-overloaded-not-method") {
    val OverloadedApplyClass = ctx.findTopLevelClass("simple_trees.OverloadedApply")
    val PredefString = ctx.findStaticType("scala.Predef.String")

    val callSym = OverloadedApplyClass.findNonOverloadedDecl(termName("callF"))

    val Some(callTree: DefDef) = callSym.tree: @unchecked

    var callCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case fooRef @ Select(_, SimpleName("foo")) =>
          callCount += 1
          val fooSym = fooRef.symbol.asTerm
          assert(clue(fooSym.declaredType).isRef(PredefString))
        case _ =>
          super.traverse(tree)
    }.traverse(callTree)

    assert(callCount == 1)
  }

  testWithContext("typeapply-recursive") {
    val RecApplyClass = ctx.findTopLevelClass("simple_trees.RecApply")

    val evalSym = RecApplyClass.findNonOverloadedDecl(name"eval")
    val ExprClass = RecApplyClass.findDecl(tname"Expr")
    val NumClass = RecApplyClass.findDecl(tname"Num")
    val BoolClass = RecApplyClass.findDecl(tname"Bool")

    val Some(evalTree: DefDef) = evalSym.tree: @unchecked

    var recCallCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
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

        case _ =>
          super.traverse(tree)
    }.traverse(evalTree)

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

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case tree @ Ident(`x`) =>
          xCount += 1
          assert(tree.tpe.isOfClass(defn.IntClass), clue(tree.tpe))
        case tree @ Ident(`y`) =>
          yCount += 1
          assert(tree.tpe.isOfClass(defn.IntClass), clue(tree.tpe))
        case _ =>
          super.traverse(tree)
    }.traverse(fTree)

    assert(xCount == 2, clue(xCount))
    assert(yCount == 1, clue(yCount))
  }

  testWithContext("term-ref") {
    val RepeatedPathClass = ctx.findTopLevelClass("simple_trees.Repeated")

    val fSym = RepeatedPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var bitSetIdentCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case tree @ Ident(SimpleName("BitSet")) =>
          bitSetIdentCount += 1
          val sym = tree.tpe.asInstanceOf[TermRef].symbol
          assert(sym.name == name"BitSet", clue(sym.name.toDebugString))
        case _ =>
          super.traverse(tree)
    }.traverse(fTree)

    assert(bitSetIdentCount == 1, clue(bitSetIdentCount))
  }

  testWithContext("wildcard-pattern") {
    val MatchPathClass = ctx.findTopLevelClass("simple_trees.Match")

    val fSym = MatchPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    val List(Left(List(xParamDef))) = fTree.paramLists: @unchecked

    assert(xParamDef.symbol.asTerm.declaredType.isRef(defn.IntClass))

    var wildcardPatternCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case tree @ WildcardPattern(tpe) =>
          wildcardPatternCount += 1
          assert(tpe.isRef(defn.IntClass), clue(tpe))
        case _ =>
          super.traverse(tree)
    }.traverse(fTree)

    assert(wildcardPatternCount == 2, clue(wildcardPatternCount))
  }

  testWithContext("match-bind-with-type-capture") {
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")
    val MatchTypeClass = ctx.findTopLevelClass("simple_trees.MatchType")

    val castMatchResultWithBindSym = MatchTypeClass.findNonOverloadedDecl(termName("castMatchResultWithBind"))
    val castMatchResultWithBindDef = castMatchResultWithBindSym.tree.get.asInstanceOf[DefDef]

    /* type param [X]
     * param x: X
     *
     * x match
     *   case is: List[t] => is.head
     *
     * `is` gets typed as `X & List[t]`.
     * `is.head` must resolve to having type `t`.
     */

    val List(Right(List(typeXDef)), _) = castMatchResultWithBindDef.paramLists: @unchecked
    val typeXSym = typeXDef.symbol

    val tTypeCaptureSym = findTree(castMatchResultWithBindDef) { case TypeTreeBind(SimpleTypeName("t"), _, sym) =>
      sym
    }

    val bind = findTree(castMatchResultWithBindDef) { case bind @ Bind(SimpleName("is"), _, _) =>
      bind
    }
    val isSym = bind.symbol

    assert(
      clue(isSym.declaredType)
        .isIntersectionOf(_.isRef(typeXSym), _.isApplied(_.isRef(ListClass), List(_.isRef(tTypeCaptureSym))))
    )

    val (typed, expr, qualifier) = findTree(castMatchResultWithBindDef) {
      case typed @ Typed(expr @ Select(qualifier, SimpleName("head")), _) => (typed, expr, qualifier)
    }
    assert(clue(qualifier.tpe).isRef(isSym))
    assert(clue(clue(expr.tpe).widenTermRef).isRef(tTypeCaptureSym))
    assert(typed.tpe.isRef(tTypeCaptureSym))
  }

  testWithContext("return") {
    val ReturnPathClass = ctx.findTopLevelClass("simple_trees.Return")

    val withReturnSym = ReturnPathClass.findNonOverloadedDecl(name"withReturn")
    val withReturnTree = withReturnSym.tree.get.asInstanceOf[DefDef]

    var returnCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case tree @ Return(expr, from) =>
          returnCount += 1
          assert(from == withReturnSym, clue(from))
          assert(tree.tpe.isNothing)
        case _ =>
          super.traverse(tree)
    }.traverse(withReturnTree)

    assert(returnCount == 1, clue(returnCount))
  }

  testWithContext("assign") {
    val AssignPathClass = ctx.findTopLevelClass("simple_trees.Assign")

    val fSym = AssignPathClass.findNonOverloadedDecl(name"f")
    val fTree = fSym.tree.get.asInstanceOf[DefDef]

    var assignCount = 0

    new TreeTraverser {
      override def traverse(tree: Tree): Unit = tree match
        case tree @ Assign(lhs, rhs) =>
          assignCount += 1
          assert(tree.tpe.isRef(defn.UnitClass), clue(tree.tpe))
        case _ =>
          super.traverse(tree)
    }.traverse(fTree)

    assert(assignCount == 1, clue(assignCount))
  }

  testWithContext("basic-scala2-types") {
    val RangeClass = ctx.findTopLevelClass("scala.collection.immutable.Range")
    val Function1Class = ctx.findTopLevelClass("scala.Function1")
    val IndexedSeqClass = ctx.findTopLevelClass("scala.collection.immutable.IndexedSeq")

    // val start: Int
    val startSym = RangeClass.findDecl(name"start")
    assert(startSym.declaredType.isRef(defn.IntClass), clue(startSym.declaredType))

    // val isEmpty: Boolean
    val isEmptySym = RangeClass.findDecl(name"isEmpty")
    assert(isEmptySym.declaredType.isRef(defn.BooleanClass), clue(isEmptySym.declaredType))

    // def isInclusive: Boolean
    val isInclusiveSym = RangeClass.findDecl(name"isInclusive")
    assert(isInclusiveSym.declaredType.isRef(defn.BooleanClass), clue(isInclusiveSym.declaredType))

    // def by(step: Int): Range
    locally {
      val bySym = RangeClass.findNonOverloadedDecl(name"by")
      val mt = bySym.declaredType.asInstanceOf[MethodType]
      assertEquals(List[TermName](name"step"), mt.paramNames, clue(mt.paramNames))
      assert(mt.paramTypes.sizeIs == 1)
      assert(mt.paramTypes.head.isRef(defn.IntClass), clue(mt.paramTypes.head))
      assert(mt.resultType.isRef(RangeClass), clue(mt.resultType))
    }

    // def map[B](f: Int => B): IndexedSeq[B]
    locally {
      val mapSym = RangeClass.findNonOverloadedDecl(name"map")
      val pt = mapSym.declaredType.asInstanceOf[PolyType]
      val mt = pt.resultType.asInstanceOf[MethodType]
      assertEquals(List[TypeName](typeName("B")), pt.paramNames, clue(pt.paramNames))
      assert(pt.paramTypeBounds.sizeIs == 1)
      assertEquals(List[TermName](termName("f")), mt.paramNames, clue(mt.paramNames))
      assert(mt.paramTypes.sizeIs == 1)
      assert(
        mt.paramTypes.head.isApplied(_.isRef(Function1Class), List(_.isRef(defn.IntClass), _ => true)),
        clue(mt.paramTypes.head)
      )
      assert(mt.resultType.isApplied(_.isRef(IndexedSeqClass), List(_ => true)), clue(mt.resultType))
    }
  }

  testWithContext("basic-java-class-dependency") {
    val BoxedJavaClass = ctx.findTopLevelClass("javacompat.BoxedJava")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val boxedSym = BoxedJavaClass.getDecl(name"boxed").get.asTerm

    val (javaDefinedRef: TypeRef) = boxedSym.declaredType: @unchecked

    assert(clue(javaDefinedRef.optSymbol) == Some(JavaDefinedClass))
  }

  testWithContext("package-private-class") {
    val javadefinedPackage = ctx.findPackage("javadefined")
    val PkgPrivateClass = ctx.findTopLevelClass("javadefined.PkgPrivate")
    val PkgPrivateModule = ctx.findTopLevelModuleClass("javadefined.PkgPrivate")
    val PkgPrivateModuleClass = ctx.findStaticTerm("javadefined.PkgPrivate")

    def assertPrivateWithin(sym: TermOrTypeSymbol, expected: DeclaringSymbol)(using munit.Location) =
      assert(!clue(sym.isPrivate) && clue(sym.visibility) == clue(Visibility.ScopedPrivate(expected)))

    assertPrivateWithin(PkgPrivateClass, javadefinedPackage)
    assertPrivateWithin(PkgPrivateModule, javadefinedPackage)
    assertPrivateWithin(PkgPrivateModuleClass, javadefinedPackage)
  }

  testWithContext("bag-of-java-definitions[static]") {
    val BagOfJavaDefinitionsClassMod = ctx.findTopLevelModuleClass("javadefined.BagOfJavaDefinitions")
    val javadefinedPackage = ctx.findPackage("javadefined")

    def testDef(name: UnsignedTermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfJavaDefinitionsClassMod.findNonOverloadedDecl(name))

    def assertJavaPublic(sym: TermOrTypeSymbol)(using munit.Location) =
      assert(!clue(sym.isPrivate) && clue(sym.visibility) == clue(Visibility.Public))

    def assertPrivateWithin(sym: TermOrTypeSymbol, expected: DeclaringSymbol)(using munit.Location) =
      assert(!clue(sym.isPrivate) && clue(sym.visibility) == clue(Visibility.ScopedPrivate(expected)))

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

    def assertJavaPublic(sym: TermOrTypeSymbol)(using munit.Location) =
      assert(!clue(sym.isPrivate) && clue(sym.visibility) == clue(Visibility.Public))

    def assertPrivateWithin(sym: TermOrTypeSymbol, expected: DeclaringSymbol)(using munit.Location) =
      assert(!clue(sym.isPrivate) && clue(sym.visibility) == clue(Visibility.ScopedPrivate(expected)))

    def testDef(name: UnsignedTermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfJavaDefinitionsClass.findNonOverloadedDecl(name))

    testDef(name"x") { x =>
      assertJavaPublic(x)
      assert(x.declaredType.isRef(defn.IntClass))
    }

    testDef(name"protectedY") { protectedY =>
      assert(!protectedY.isPrivate)
      assert(clue(protectedY.visibility) == Visibility.Protected)
      assert(protectedY.declaredType.isRef(defn.IntClass))
    }

    testDef(name"privateZ") { privateZ =>
      assert(privateZ.isPrivate)
      assert(clue(privateZ.visibility) == Visibility.Private)
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

    testDef(termName("multipleArguments")) { multipleArguments =>
      assertJavaPublic(multipleArguments)
      val tpe = multipleArguments.declaredType.asInstanceOf[MethodType]
      assert(clue(tpe.paramNames) == List(termName("foo"), termName("bar"), termName("foobar")))
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

    def testDef(name: UnsignedTermName)(op: munit.Location ?=> TermSymbol => Unit)(using munit.Location): Unit =
      op(BagOfGenJavaDefinitionsClass.findNonOverloadedDecl(name))

    extension (tpe: TypeMappable)
      def isGenJavaClassOf(arg: TypeOrWildcard => Boolean)(using Context): Boolean =
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
        tparamRefA.bounds.high.isIntersectionOf(_.isRef(JavaInterface1), _.isRef(JavaInterface2)),
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
      assert(gencontravarient.declaredType.isGenJavaClassOf(_.isBounded(_.isRef(JavaDefinedClass), _.isFromJavaObject)))
    }
  }

  testWithContext("generic-java-class-type-param-bounds") {
    val GenericJavaClass = ctx.findTopLevelClass("javadefined.GenericJavaClass")

    assert(clue(GenericJavaClass.typeParams).sizeIs == 1)
    val tparam = GenericJavaClass.typeParams.head

    assert(clue(tparam.declaredBounds.low).isNothing)
    assert(clue(tparam.declaredBounds.high).isFromJavaObject)
  }

  testWithContext("inferred-from-java-object") {
    val InferredFromJavaObjectClass = ctx.findTopLevelClass("javacompat.InferredFromJavaObject")

    val atTopLevel = InferredFromJavaObjectClass.findDecl(termName("atTopLevel"))
    assert(clue(atTopLevel.declaredType).isType(_.isFromJavaObject))

    val inArray = InferredFromJavaObjectClass.findDecl(termName("inArray"))
    assert(clue(inArray.declaredType).isArrayOf(_.isType(_.isFromJavaObject)))
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
  }

  testWithContext("parents-of-tuple-classes") {
    val SerializableClass = ctx.findTopLevelClass("java.io.Serializable")
    val MirrorSingletonClass = ctx.findStaticClass("scala.deriving.Mirror.Singleton")
    val TupleClass = ctx.findTopLevelClass("scala.Tuple")
    val NonEmptyTupleClass = ctx.findTopLevelClass("scala.NonEmptyTuple")
    val TConsClass = ctx.findTopLevelClass("scala.*:")
    val EmptyTupleClass = ctx.findStaticModuleClass("scala.Tuple$package.EmptyTuple")
    val Tuple2Class = ctx.findTopLevelClass("scala.Tuple2")
    val ProductClass = ctx.findTopLevelClass("scala.Product")
    val Product2Class = ctx.findTopLevelClass("scala.Product2")

    assert(clue(TupleClass.parentClasses) == List(defn.ObjectClass, ProductClass))
    assert(
      clue(EmptyTupleClass.parentClasses) == List(
        defn.ObjectClass,
        TupleClass,
        ProductClass,
        SerializableClass,
        MirrorSingletonClass
      )
    )
    assert(clue(NonEmptyTupleClass.parentClasses) == List(defn.ObjectClass, TupleClass))
    assert(clue(TConsClass.parentClasses) == List(defn.ObjectClass, NonEmptyTupleClass))
    assert(clue(Tuple2Class.parentClasses) == List(TConsClass, Product2Class, ProductClass, SerializableClass))
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

    val (getXRef: TermRef) = getXSelection.tpe: @unchecked

    assert(clue(getXRef.symbol) == getX)
  }

  testWithContext("select-field-from-java-class") {
    val BoxedJavaClass = ctx.findTopLevelClass("javacompat.BoxedJava")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val x = JavaDefinedClass.findDecl(name"x")
    val xFieldSym = BoxedJavaClass.findDecl(name"xField")

    val Some(DefDef(_, _, _, Some(xSelection), _)) = xFieldSym.tree: @unchecked

    val (xRef: TermRef) = xSelection.tpe: @unchecked

    assert(clue(xRef.symbol) == x)
  }

  testWithContext("basic-scala-2-stdlib-class-dependency") {
    val BoxedConsClass = ctx.findTopLevelClass("scala2compat.BoxedCons")
    val ConsClass = ctx.findTopLevelClass("scala.collection.immutable.::")
    val JavaDefinedClass = ctx.findTopLevelClass("javadefined.JavaDefined")

    val boxedSym = BoxedConsClass.findDecl(name"boxed")

    val app = boxedSym.declaredType.asInstanceOf[AppliedType]
    assert(clue(app.tycon).isRef(ConsClass))
    assert(clue(app.args).isListOf(_.isRef(JavaDefinedClass)))
  }

  testWithContext("select-method-from-scala-2-stdlib-class") {
    val BoxedConsClass = ctx.findTopLevelClass("scala2compat.BoxedCons")

    val fooSym = BoxedConsClass.findDecl(name"foo")

    val Some(DefDef(_, _, _, Some(Apply(canEqualSelection, _)), _)) = fooSym.tree: @unchecked

    val underlyingType = canEqualSelection.tpe match
      case termRef: TermRef => termRef.underlyingOrMethodic
      case tpe              => fail("expected TermRef", clues(tpe))

    val mt = underlyingType.asInstanceOf[MethodType]
    assertEquals(List[TermName](name"that"), mt.paramNames, clue(mt.paramNames))
    assert(mt.paramTypes.sizeIs == 1, clue(mt.paramTypes))
    assert(mt.paramTypes.head.isRef(defn.AnyClass), clue(mt.paramTypes.head))
    assert(mt.resultType.isRef(defn.BooleanClass), clue(mt.resultType))
  }

  testWithContext("unmangle-scala-2-names") {
    // `$extension` methods pickled by Scala 2 are not visible from a Scala 3 point of view
    val ArrayOpsModClass = ctx.findTopLevelModuleClass("scala.collection.ArrayOps")
    assert(clue(ArrayOpsModClass.getAllOverloadedDecls(termName("partition$extension"))).isEmpty)
    for decl <- ArrayOpsModClass.declarations do assert(!clue(decl.name).toString().endsWith("$extension"))

    // Consistency check: Scala 3 does not emit `$extension` methods either
    val ValueClassModClass = ctx.findTopLevelModuleClass("simple_trees.ValueClass")
    assert(clue(ValueClassModClass.getAllOverloadedDecls(termName("myLength$extension"))).isEmpty)
    for decl <- ValueClassModClass.declarations do assert(!clue(decl.name).toString().endsWith("$extension"))
  }

  testWithContext("scala-2-by-name-params") {
    val OptionClass = ctx.findTopLevelClass("scala.Option")

    val getOrElseSym = OptionClass.findNonOverloadedDecl(termName("getOrElse"))

    getOrElseSym.declaredType match
      case pt: PolyType =>
        assert(clue(pt.paramNames).sizeIs == 1)
        pt.resultType match
          case mt: MethodType =>
            assert(clue(mt.paramNames).sizeIs == 1)
            assert(clue(mt.paramTypes.head).isByName(_ eq pt.paramRefs.head))
          case _ =>
            throw AssertionError(s"unexpected type $pt")
      case tpe =>
        throw AssertionError(s"unexpected type $tpe")
  }

  testWithContext("default-params") {
    extension (sym: TermSymbol) def paramCount: Int = sym.declaredType.asInstanceOf[MethodType].paramNames.size

    val DefaultParamsClass = ctx.findTopLevelClass("simple_trees.DefaultParams")
    assert(clue(DefaultParamsClass.getNonOverloadedDecl(DefaultGetterName(termName("foo"), 0))).isEmpty)
    DefaultParamsClass.findNonOverloadedDecl(DefaultGetterName(termName("foo"), 1))
    DefaultParamsClass.findNonOverloadedDecl(DefaultGetterName(termName("foo"), 2))
    assert(clue(DefaultParamsClass.getNonOverloadedDecl(DefaultGetterName(termName("foo"), 3))).isEmpty)

    val fooOverloads = DefaultParamsClass.findAllOverloadedDecls(termName("foo"))

    val fooWithDefaults = fooOverloads.find(_.paramCount == 3).get
    assert(clue(fooWithDefaults.hasParamWithDefault) && !clue(fooWithDefaults.isParamWithDefault))
    val List(Left(fooWithDefaultsParams)) = fooWithDefaults.paramSymss: @unchecked
    assert(clue(fooWithDefaultsParams.map(_.isParamWithDefault)) == List(false, true, true))
    assert(clue(fooWithDefaultsParams.map(_.hasParamWithDefault)).forall(_ == false))

    for fooOverload <- fooOverloads if fooOverload ne fooWithDefaults do
      assert(!clue(fooOverload.hasParamWithDefault) && !clue(fooOverload.isParamWithDefault))
      val List(Left(params)) = fooOverload.paramSymss: @unchecked
      assert(clue(params.map(_.isParamWithDefault)).forall(_ == false))
      assert(clue(params.map(_.hasParamWithDefault)).forall(_ == false))
  }

  testWithContext("default-params-scala-2") {
    val IteratorClass = ctx.findTopLevelClass("scala.collection.Iterator")
    assert(clue(IteratorClass.getNonOverloadedDecl(DefaultGetterName(termName("indexWhere"), 0))).isEmpty)
    IteratorClass.findNonOverloadedDecl(DefaultGetterName(termName("indexWhere"), 1))
    assert(clue(IteratorClass.getNonOverloadedDecl(DefaultGetterName(termName("indexWhere"), 2))).isEmpty)

    locally {
      val indexWhere = IteratorClass.findNonOverloadedDecl(termName("indexWhere"))
      assert(clue(indexWhere.hasParamWithDefault) && !clue(indexWhere.isParamWithDefault))

      val List(Left(List(p, from))) = indexWhere.paramSymss: @unchecked
      assert(!clue(p.hasParamWithDefault) && !clue(p.isParamWithDefault))
      assert(!clue(from.hasParamWithDefault) && clue(from.isParamWithDefault))
    }

    val ArrayDequeModClass = ctx.findTopLevelModuleClass("scala.collection.mutable.ArrayDeque")
    ArrayDequeModClass.findNonOverloadedDecl(DefaultGetterName(nme.Constructor, 0))
    assert(clue(ArrayDequeModClass.getNonOverloadedDecl(DefaultGetterName(nme.Constructor, 1))).isEmpty)
  }

  testWithContext("select-field-from-tasty-in-other-package:dependency-from-class-file") {
    val BoxedConstantsClass = ctx.findTopLevelClass("crosspackagetasty.BoxedConstants")
    val ConstantsClass = ctx.findTopLevelClass("simple_trees.Constants")

    val unitVal = ConstantsClass.findDecl(name"unitVal")
    val boxedUnitValSym = BoxedConstantsClass.findDecl(name"boxedUnitVal")

    val Some(DefDef(_, _, _, Some(unitValSelection), _)) = boxedUnitValSym.tree: @unchecked

    val (unitValRef: TermRef) = unitValSelection.tpe: @unchecked

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

    val (getXRef: TermRef) = getXSelection.tpe: @unchecked

    assert(clue(getXRef.symbol) == getX)
  }

  testWithContext("select-field-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testField").tree: @unchecked

    val Select(qual, fieldName) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isRef(GenClass), List(_.isRef(defn.IntClass))))
    assertEquals(fieldName, name"field")
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("select-getter-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testGetter").tree: @unchecked

    val Select(qual, getterName) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isRef(GenClass), List(_.isRef(defn.IntClass))))
    assertEquals(getterName, name"getter")
    assert(clue(body.tpe).isOfClass(defn.IntClass))
  }

  testWithContext("select-and-apply-method-from-generic-class") {
    val GenClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) = PolySelect.findNonOverloadedDecl(name"testMethod").tree: @unchecked

    val Apply(fun @ Select(qual, methodName), List(arg)) = body: @unchecked

    assert(clue(qual.tpe).isApplied(_.isRef(GenClass), List(_.isRef(defn.IntClass))))
    (methodName: @unchecked) match {
      case SignedName(_, _, simpleName) => assertEquals(simpleName, name"method")
    }
    (fun.tpe.widenTermRef: @unchecked) match {
      case mt: MethodType =>
        assert(clue(mt.paramNames) == List(name"x"))
        assert(clue(mt.paramTypes.head).isRef(defn.IntClass))
        assert(clue(mt.resultType).isRef(defn.IntClass))
    }
    assert(clue(body.tpe).isRef(defn.IntClass))
  }

  testWithContext("select-and-apply-poly-method") {
    val GenMethod = ctx.findTopLevelClass("simple_trees.GenericMethod")
    val PolySelect = ctx.findTopLevelClass("simple_trees.PolySelect")

    val Some(DefDef(_, _, _, Some(body), _)) =
      PolySelect.findNonOverloadedDecl(name"testGenericMethod").tree: @unchecked

    val Apply(tapp @ TypeApply(fun @ Select(qual, methodName), List(targ)), List(arg)) = body: @unchecked

    assert(clue(qual.tpe).isOfClass(GenMethod))
    (methodName: @unchecked) match {
      case SignedName(_, _, simpleName) => assertEquals(simpleName, name"identity")
    }
    (tapp.tpe.widenTermRef: @unchecked) match {
      case mt: MethodType =>
        assert(clue(mt.paramNames) == List(name"x"))
        assert(clue(mt.paramTypes.head).isRef(defn.IntClass))
        assert(clue(mt.resultType).isRef(defn.IntClass))
    }
    assert(clue(body.tpe).isRef(defn.IntClass))
  }

  testWithContext("poly-new") {
    val GenericClass = ctx.findTopLevelClass("simple_trees.GenericClass")
    val GenericModuleClass = ctx.findTopLevelModuleClass("simple_trees.GenericClass")

    for testMethodName <- List("new1", "new2", "new3") do
      val DefDef(_, _, _, Some(body), _) =
        GenericModuleClass.findNonOverloadedDecl(termName(testMethodName)).tree.get: @unchecked

      val Apply(tapp @ TypeApply(fun @ Select(qual: New, ctorName), List(targ)), args) = body: @unchecked

      assert(clue(targ.toType).isRef(defn.IntClass), testMethodName)
      assert(clue(fun.symbol).name == nme.Constructor, testMethodName)
      assert(clue(args.map(_.tpe)).forall(_.isConstant(Constant(1))), testMethodName)
      assert(clue(tapp.tpe).isInstanceOf[MethodType], testMethodName)
      assert(clue(body.tpe).isApplied(_.isRef(GenericClass), List(_.isRef(defn.IntClass))), testMethodName)
    end for
  }

  testWithContext("sealed-children") {
    val SealedClass = ctx.findTopLevelClass("simple_trees.SealedClass")
    val ClassCaseClass = ctx.findStaticClass("simple_trees.SealedClass.ClassCase")
    val ObjectCaseTerm = ctx.findStaticTerm("simple_trees.SealedClass.ObjectCase")

    assert(SealedClass.openLevel == OpenLevel.Sealed)
    assert(!SealedClass.isEnum)
    assert(clue(SealedClass.sealedChildren) == List(ClassCaseClass, ObjectCaseTerm))

    val EquivClass = ctx.findTopLevelClass("scala.=:=")
    assert(clue(EquivClass.sealedChildren) == List(EquivClass))

    assert(clue(EquivClass.getDecl(tpnme.scala2LocalChild)).isEmpty)

    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")
    val ConsClass = ctx.findTopLevelClass("scala.collection.immutable.::")
    val NilModule = ctx.findStaticTerm("scala.collection.immutable.Nil")
    assert(clue(ListClass.sealedChildren).toSet == Set(ConsClass, NilModule))
  }

  testWithContext("enum-children") {
    val ScalaEnumClass = ctx.findTopLevelClass("simple_trees.ScalaEnum")
    val ClassCaseClass = ctx.findStaticClass("simple_trees.ScalaEnum.ClassCase")
    val ObjectCaseTerm = ctx.findStaticTerm("simple_trees.ScalaEnum.ObjectCase")

    assert(ScalaEnumClass.openLevel == OpenLevel.Sealed)
    assert(ScalaEnumClass.isEnum)
    assert(clue(ScalaEnumClass.sealedChildren) == List(ClassCaseClass, ObjectCaseTerm))
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
    val TypeMemberDefinition.TypeAlias(alias) = PredefString.asInstanceOf[TypeMemberSymbol].typeDef: @unchecked
    assert(clue(alias).isRef(defn.StringClass))
  }

  testWithContext("scala2-module-and-def-with-same-name") {
    val StringContext = ctx.findTopLevelClass("scala.StringContext")
    val sModuleClass = StringContext.findDecl(moduleClassName("s")).asClass

    val sDecls = StringContext.getAllOverloadedDecls(name"s")
    assert(clue(sDecls).sizeIs == 2)

    val (sModule, sDef) =
      if sDecls(0).kind == TermSymbolKind.Module then (sDecls(0), sDecls(1))
      else
        assert(sDecls(1).kind == TermSymbolKind.Module)
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

  testWithContext("lambdas") {
    val FunctionClass = ctx.findTopLevelClass("simple_trees.Function")
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")

    def getRhsOf(name: String): TermTree =
      FunctionClass.findNonOverloadedDecl(termName(name)).tree.get.asInstanceOf[ValDef].rhs.get

    def findLambdaOf(tree: TermTree): Lambda = tree match
      case tree: Lambda   => tree
      case Block(_, expr) => findLambdaOf(expr)
      case _              => fail("lambda expected", clues(tree))

    // val functionLambda = (x: Int) => x + 1
    val functionLambda = getRhsOf("functionLambda")
    assert(
      clue(functionLambda.tpe)
        .isApplied(_.isRef(defn.FunctionNClass(1)), List(_.isRef(defn.IntClass), _.isRef(defn.IntClass)))
    )
    assert(clue(findLambdaOf(functionLambda).samClassSymbol) == defn.FunctionNClass(1))

    // val samLambda: Runnable = () => ()
    val samLambda = getRhsOf("samLambda")
    assert(clue(samLambda.tpe).isRef(ctx.findTopLevelClass("java.lang.Runnable")))
    assert(clue(findLambdaOf(samLambda).samClassSymbol) == ctx.findTopLevelClass("java.lang.Runnable"))

    // val polyID: [T] => T => T = [T] => (x: T) => x
    val polyID = getRhsOf("polyID")
    polyID.tpe match
      case polyIDTpe: TermRefinement =>
        assert(clue(polyIDTpe.parent).isRef(ctx.findTopLevelClass("scala.PolyFunction")))
        assert(clue(polyIDTpe.refinedName) == nme.m_apply)
        polyIDTpe.refinedType match
          case pt: PolyType =>
            assert(clue(pt.paramNames.size) == 1)
            val tpRef = pt.paramRefs(0)
            pt.resultType match
              case mt: MethodType =>
                assert(clue(mt.paramNames.size) == 1)
                assert(clue(mt.paramTypes(0)) == clue(tpRef))
                assert(clue(mt.resultType) == clue(tpRef))
              case _ =>
                fail(s"unexpected polyID refined type: $pt")
          case pt =>
            fail(s"unexpected polyID refined type: $pt")
      case polyIDTpe =>
        fail(s"unexpected polyID type: $polyIDTpe")
    end match

    // val dependentID: (x: Any) => x.type = x => x
    val dependentID = getRhsOf("dependentID")
    dependentID.tpe match
      case dependentIDTpe: TermRefinement =>
        assert(clue(dependentIDTpe.parent).isApplied(_.isRef(defn.FunctionNClass(1)), List(_ => true, _ => true)))
        assert(clue(dependentIDTpe.refinedName) == nme.m_apply)
        dependentIDTpe.refinedType match
          case mt: MethodType =>
            assert(clue(mt.paramNames.size) == 1)
            val tpRef = mt.paramRefs(0)
            assert(clue(mt.paramTypes(0)).isAny)
            assert(clue(mt.resultType) == clue(tpRef))
          case mt =>
            fail(s"unexpected dependentID refined type: $mt")
      case dependentIDTpe =>
        fail(s"unexpected dependentID type: $dependentIDTpe")
    end match
    assert(clue(findLambdaOf(dependentID).samClassSymbol) == defn.FunctionNClass(1))
  }

  testWithContext("varargs") {
    val VarargFunctionClass = ctx.findTopLevelClass("simple_trees.VarargFunction")
    val scalaSeq = ctx.findStaticType("scala.package.Seq")

    def getDefOf(name: String): DefDef =
      VarargFunctionClass.findNonOverloadedDecl(termName(name)).tree.get.asInstanceOf[DefDef]

    def extractParamAndResultType(mt: TermType): (Type, TypeOrMethodic) = mt match
      case mt: MethodType if mt.paramNames.sizeIs == 1 =>
        (mt.paramTypes.head, mt.resultType)
      case _ =>
        fail(s"unexpected method type", clues(mt))
    end extractParamAndResultType

    def extractFormalTypedActualParamTypes(apply: TermTree): (Type, TermType, TermType) = apply match
      case Apply(fun, List(typed @ Typed(arg, _))) =>
        val (formal, _) = extractParamAndResultType(fun.tpe.widenTermRef)
        (formal, typed.tpe, arg.tpe)
      case _ =>
        fail("unexpected body", clues(apply))
    end extractFormalTypedActualParamTypes

    def assertSeqOfInt(tpe: TypeMappable): Unit =
      assert(clue(tpe).isApplied(t => t.isRef(defn.SeqClass) || t.isRef(scalaSeq), List(_.isRef(defn.IntClass))))

    def assertAnnotatedSeqOfInt(tpe: TypeMappable): Unit = tpe match
      case tpe: AnnotatedType =>
        assertSeqOfInt(tpe.typ)
        assert(clue(tpe.annotation.symbol) == defn.internalRepeatedAnnotClass.get)
      case _ =>
        fail("unexpected parameter type", clues(tpe))
    end assertAnnotatedSeqOfInt

    def assertRepeatedOfInt(tpe: TypeMappable): Unit =
      assert(clue(tpe).isRepeated(_.isRef(defn.IntClass)))

    locally {
      val dd = getDefOf("takesVarargs")
      val List(Left(List(paramValDef))) = dd.paramLists: @unchecked
      val (paramType, resultType) = extractParamAndResultType(dd.symbol.declaredType)

      assertAnnotatedSeqOfInt(paramValDef.symbol.declaredType)
      assertRepeatedOfInt(paramType)
    }

    val testMethodNames = List(
      "givesVarargs",
      "givesSeqLiteral",
      "givesSeqToJava",
      "givesSeqLiteralToJava",
      "givesSeqToScala2",
      "givesSeqLiteralToScala2"
    )
    for testMethodName <- testMethodNames do
      val dd = getDefOf(testMethodName)
      val (formal, typed, actual) = extractFormalTypedActualParamTypes(dd.rhs.get)

      assertRepeatedOfInt(formal)
      assertRepeatedOfInt(typed)
      assertSeqOfInt(actual.widenTermRef)
    end for
  }

  testWithContext("scala2-class-type-param-ref") {
    val RepeatedClass = ctx.findTopLevelClass("simple_trees.Repeated")
    val BitSetClass = ctx.findTopLevelClass("scala.collection.immutable.BitSet")
    val SpecificIterableFactoryClass = ctx.findTopLevelClass("scala.collection.SpecificIterableFactory")

    val fSym = RepeatedClass.findNonOverloadedDecl(termName("f"))
    val body = fSym.tree.get.asInstanceOf[DefDef].rhs.get

    val Apply(fun, args) = body: @unchecked

    val termRef = fun.tpe.asInstanceOf[TermRef]
    val sym = termRef.symbol
    assert(clue(sym).name == nme.m_apply)
    assert(clue(sym.owner) == SpecificIterableFactoryClass)

    sym.declaredType match
      case tpe: MethodType =>
        tpe.resultType match
          case resType: TypeRef =>
            assert(clue(resType.optSymbol).exists(_.isInstanceOf[ClassTypeParamSymbol]))
            resType.prefix match
              case thisType: ThisType =>
                assert(thisType.cls == SpecificIterableFactoryClass)
              case _ =>
                fail(s"prefix is not a ThisType for $sym", clues(resType))
          case resType =>
            fail(s"result type is not a TypeRef for $sym", clues(resType))
      case tpe =>
        fail(s"not a MethodType for $sym", clues(tpe))
    end match

    assert(clue(body.tpe.widenTermRef).isRef(BitSetClass))
  }

  testWithContext("baseType with higher-kinded type params instantiated to own subclass") {
    /* First, the fundamental reproduction: computing
     *
     *   baseType(List[Int], trait scala.collection.IterableOps)
     *
     * This used to crash with a StackOverflowError. It was caused because of
     * the self-higher-kinded application of CC in superclasses. The hierarchy
     * looks like the following:
     *
     * trait IterableOps[+A, +CC[_], +C]
     * class List[+A] extends StrictOptimizedSeqOps[A, List, List[A]]
     * trait StrictOptimizedSeqOps[+A, +CC[_], +C] extends ... (eventually) ... IterableOps[A, CC, C]
     */

    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")
    val IterableOpsClass = ctx.findTopLevelClass("scala.collection.IterableOps")

    val origType = ListClass.staticRef.appliedTo(defn.IntType)
    val optBaseType = origType.baseType(IterableOpsClass) // this used to cause an infinite recursion
    assert(optBaseType.isDefined)

    // sc.IterableOps[scala.Int, sci.List, sci.List[scala.Int]]
    assert(
      optBaseType.get.isApplied(
        _.isRef(IterableOpsClass),
        List(_.isRef(defn.IntClass), _.isRef(ListClass), _.isApplied(_.isRef(ListClass), List(_.isRef(defn.IntClass))))
      )
    )

    // Here is the original trigger: computing the type of the body of ForExpressions.test1
    locally {
      val ForExpressionsClass = ctx.findTopLevelClass("simple_trees.ForExpressions")

      val test1Sym = ForExpressionsClass.findNonOverloadedDecl(termName("test1"))
      val body = test1Sym.tree.get.asInstanceOf[DefDef].rhs.get

      val tpe = body.tpe // this used to cause an infinite recursion
      assert(clue(tpe).isRef(defn.UnitClass))
    }
  }

  testWithContext("baseType-can-substitute-wildcard-type-arg-for-type") {
    val IterableOpsClass = ctx.findTopLevelClass("scala.collection.IterableOps")
    val WithFilterClass = ctx.findStaticClass("scala.collection.MapOps.WithFilter")

    val ctorSym = WithFilterClass.findNonOverloadedDecl(nme.Constructor)
    val methodType = ctorSym.declaredType.asInstanceOf[PolyType].resultType.asInstanceOf[MethodType]
    val selfParamType = methodType.paramTypes.head

    val baseTypeOpt = selfParamType.baseType(IterableOpsClass) // used to crash with CCE
    assert(baseTypeOpt.isDefined, clues(selfParamType))

    // scala.collection.IterableOps[scala.Tuple2[K, V], (scala.collection.Iterable & IterableCC), ?]
    baseTypeOpt.get match
      case baseType: AppliedType =>
        baseType.tycon match
          case TypeRef.OfClass(cls) =>
            assert(clue(cls) == IterableOpsClass)
          case _ =>
            fail("unexpected baseType", clues(baseType))
        baseType.args match
          case List(tuple2: AppliedType, iterableAndIterableCC: AndType, wild: WildcardTypeArg) =>
            () // OK
          case _ =>
            fail("unexpected baseType", clues(baseType))
      case baseType =>
        fail("unexpected baseType", clues(baseType))
    end match
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

  testWithContext("constructor params normalization") {
    val prefix = "inheritance.CtorParamsNormalization"

    val SuperClassNoNormClass = ctx.findStaticClass(s"$prefix.SuperClassNoNorm")
    val SuperTraitNoNormClass = ctx.findStaticClass(s"$prefix.SuperTraitNoNorm")

    for cls <- List(SuperClassNoNormClass, SuperTraitNoNormClass) do
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      ctor.declaredType match
        case mt1: MethodType =>
          assert(clue(mt1).paramNames.isEmpty, cls)
          mt1.resultType match
            case mt2: MethodType =>
              assert(clue(mt2).paramNames.sizeIs == 1, cls)
            case mt2 =>
              fail("expected MethodType", clues(cls, mt1))
        case mt1 =>
          fail("expected MethodType", clues(cls, mt1))
    end for

    val SuperClassWithNormClass = ctx.findStaticClass(s"$prefix.SuperClassWithNorm")
    val SuperTraitWithNormClass = ctx.findStaticClass(s"$prefix.SuperTraitWithNorm")

    for cls <- List(SuperClassWithNormClass, SuperTraitWithNormClass) do
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      ctor.declaredType match
        case mt1: MethodType =>
          assert(clue(mt1).paramNames.sizeIs == 1, cls)
          mt1.resultType match
            case mt2: MethodType =>
              assert(clue(mt2).paramNames.isEmpty, cls)
            case mt2 =>
              fail("expected MethodType", clues(cls, mt1))
        case mt1 =>
          fail("expected MethodType", clues(cls, mt1))
    end for

    for n <- 1 to 4 do
      val SubNClass = ctx.findStaticClass(s"$prefix.Sub$n")
      val expectedParentClass = if n % 2 == 1 then SuperClassNoNormClass else SuperClassWithNormClass
      val expectedParentTrait = if n <= 2 then SuperTraitNoNormClass else SuperTraitWithNormClass
      val expectedParents = List(expectedParentClass, expectedParentTrait)
      assert(clue(clue(SubNClass).parentClasses) == clue(expectedParents))
    end for
  }

  testWithContext("poly constructor params normalization") {
    val prefix = "inheritance.CtorParamsNormalization"

    val PolySuperClassNoNormClass = ctx.findStaticClass(s"$prefix.PolySuperClassNoNorm")
    val PolySuperTraitNoNormClass = ctx.findStaticClass(s"$prefix.PolySuperTraitNoNorm")

    for cls <- List(PolySuperClassNoNormClass, PolySuperTraitNoNormClass) do
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      ctor.declaredType match
        case pt1: PolyType =>
          assert(clue(pt1).paramNames.sizeIs == 1, cls)
          pt1.resultType match
            case mt1: MethodType =>
              assert(clue(mt1).paramNames.isEmpty, cls)
              mt1.resultType match
                case mt2: MethodType =>
                  assert(clue(mt2).paramNames.sizeIs == 1, cls)
                case mt2 =>
                  fail("expected MethodType", clues(cls, pt1))
            case mt1 =>
              fail("expected MethodType", clues(cls, pt1))
        case pt1 =>
          fail("expected PolyType", clues(cls, pt1))
    end for

    val PolySuperClassWithNormClass = ctx.findStaticClass(s"$prefix.PolySuperClassWithNorm")
    val PolySuperTraitWithNormClass = ctx.findStaticClass(s"$prefix.PolySuperTraitWithNorm")

    for cls <- List(PolySuperClassWithNormClass, PolySuperTraitWithNormClass) do
      val ctor = cls.findNonOverloadedDecl(nme.Constructor)
      ctor.declaredType match
        case pt1: PolyType =>
          assert(clue(pt1).paramNames.sizeIs == 1, cls)
          pt1.resultType match
            case mt1: MethodType =>
              assert(clue(mt1).paramNames.sizeIs == 1, cls)
              mt1.resultType match
                case mt2: MethodType =>
                  assert(clue(mt2).paramNames.isEmpty, cls)
                case mt2 =>
                  fail("expected MethodType", clues(cls, mt1))
            case mt1 =>
              fail("expected MethodType", clues(cls, mt1))
        case pt1 =>
          fail("expected PolyType", clues(cls, pt1))
    end for

    for n <- 1 to 4 do
      val PolySubNClass = ctx.findStaticClass(s"$prefix.PolySub$n")
      val expectedParentClass = if n % 2 == 1 then PolySuperClassNoNormClass else PolySuperClassWithNormClass
      val expectedParentTrait = if n <= 2 then PolySuperTraitNoNormClass else PolySuperTraitWithNormClass
      val expectedParents = List(expectedParentClass, expectedParentTrait)
      assert(clue(clue(PolySubNClass).parentClasses) == clue(expectedParents))
    end for
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
      def firstParamTypeIsRef(cls: ClassSymbol): Boolean =
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

    val overloadedParensNoParensInSuper = SuperMonoClass.findNonOverloadedDecl(termName("overloadedParensNoParens"))
    val overloadedParensNoParensInChild = ChildMonoClass.findNonOverloadedDecl(termName("overloadedParensNoParens"))

    val overloadedNoParensParensInSuper = SuperMonoClass.findNonOverloadedDecl(termName("overloadedNoParensParens"))
    val overloadedNoParensParensInChild = ChildMonoClass.findNonOverloadedDecl(termName("overloadedNoParensParens"))

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

    // From overloadedParensNoParensInSuper

    assert(
      clue(overloadedParensNoParensInSuper.overriddenSymbol(SuperMonoClass)) == Some(overloadedParensNoParensInSuper)
    )
    assert(clue(overloadedParensNoParensInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(
      clue(overloadedParensNoParensInSuper.overridingSymbol(SuperMonoClass)) == Some(overloadedParensNoParensInSuper)
    )
    assert(clue(overloadedParensNoParensInSuper.overridingSymbol(ChildMonoClass)) == None)

    assert(
      clue(overloadedParensNoParensInSuper.matchingSymbol(SuperMonoClass, ChildMonoClass)) == Some(
        overloadedParensNoParensInSuper
      )
    )
    assert(clue(overloadedParensNoParensInSuper.matchingSymbol(ChildMonoClass, ChildMonoClass)) == None)

    // From overloadedParensNoParensInChild

    assert(clue(overloadedParensNoParensInChild.overriddenSymbol(SuperMonoClass)) == None)
    assert(
      clue(overloadedParensNoParensInChild.overriddenSymbol(ChildMonoClass)) == Some(overloadedParensNoParensInChild)
    )

    assert(clue(overloadedParensNoParensInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(
      clue(overloadedParensNoParensInChild.overridingSymbol(ChildMonoClass)) == Some(overloadedParensNoParensInChild)
    )

    assert(clue(overloadedParensNoParensInChild.matchingSymbol(SuperMonoClass, ChildMonoClass)) == None)
    assert(
      clue(overloadedParensNoParensInChild.matchingSymbol(ChildMonoClass, ChildMonoClass)) == Some(
        overloadedParensNoParensInChild
      )
    )

    // From overloadedNoParensParensInSuper

    assert(
      clue(overloadedNoParensParensInSuper.overriddenSymbol(SuperMonoClass)) == Some(overloadedNoParensParensInSuper)
    )
    assert(clue(overloadedNoParensParensInSuper.overriddenSymbol(ChildMonoClass)) == None)

    assert(
      clue(overloadedNoParensParensInSuper.overridingSymbol(SuperMonoClass)) == Some(overloadedNoParensParensInSuper)
    )
    assert(clue(overloadedNoParensParensInSuper.overridingSymbol(ChildMonoClass)) == None)

    assert(
      clue(overloadedNoParensParensInSuper.matchingSymbol(SuperMonoClass, ChildMonoClass)) == Some(
        overloadedNoParensParensInSuper
      )
    )
    assert(clue(overloadedNoParensParensInSuper.matchingSymbol(ChildMonoClass, ChildMonoClass)) == None)

    // From overloadedNoParensParensInChild

    assert(clue(overloadedNoParensParensInChild.overriddenSymbol(SuperMonoClass)) == None)
    assert(
      clue(overloadedNoParensParensInChild.overriddenSymbol(ChildMonoClass)) == Some(overloadedNoParensParensInChild)
    )

    assert(clue(overloadedNoParensParensInChild.overridingSymbol(SuperMonoClass)) == None)
    assert(
      clue(overloadedNoParensParensInChild.overridingSymbol(ChildMonoClass)) == Some(overloadedNoParensParensInChild)
    )

    assert(clue(overloadedNoParensParensInChild.matchingSymbol(SuperMonoClass, ChildMonoClass)) == None)
    assert(
      clue(overloadedNoParensParensInChild.matchingSymbol(ChildMonoClass, ChildMonoClass)) == Some(
        overloadedNoParensParensInChild
      )
    )
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
    val SecondSuperPolyClass = ctx.findStaticClass("inheritance.Overrides.SecondSuperPoly")
    val ThirdSuperClass = ctx.findStaticClass("inheritance.Overrides.ThirdSuper")
    val ChildPolyClass = ctx.findStaticClass("inheritance.Overrides.ChildPoly")

    val List(superPolyA, superPolyB) = SuperPolyClass.typeParams: @unchecked
    val List(secondSuperPolyX) = SecondSuperPolyClass.typeParams: @unchecked
    val List(childPolyX) = ChildPolyClass.typeParams: @unchecked

    val IntClass = defn.IntClass

    extension (meth: TermSymbol)
      def firstParamTypeIsRef(cls: TypeSymbol): Boolean =
        meth.declaredType.asInstanceOf[MethodType].paramTypes.head.isRef(cls)

    val fooInSuper = SuperPolyClass.findAllOverloadedDecls(name"foo")
    val fooAInSuper = fooInSuper.find(_.firstParamTypeIsRef(superPolyA)).get
    val fooBInSuper = fooInSuper.find(_.firstParamTypeIsRef(superPolyB)).get

    val fooInSecondSuper = SecondSuperPolyClass.findAllOverloadedDecls(name"foo")
    val fooXInSecondSuper = fooInSecondSuper.find(_.firstParamTypeIsRef(secondSuperPolyX)).get
    val fooIntInSecondSuper = fooInSecondSuper.find(_.firstParamTypeIsRef(IntClass)).get

    val fooInChild = ChildPolyClass.findAllOverloadedDecls(name"foo")
    val fooXInChild = fooInChild.find(_.firstParamTypeIsRef(childPolyX)).get
    val fooIntInChild = fooInChild.find(_.firstParamTypeIsRef(IntClass)).get

    // From fooAInSuper

    assert(clue(fooAInSuper.overriddenSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooAInSuper.overriddenSymbol(SecondSuperPolyClass)) == None)
    assert(clue(fooAInSuper.overriddenSymbol(ThirdSuperClass)) == None)
    assert(clue(fooAInSuper.overriddenSymbol(ChildPolyClass)) == None)

    assert(clue(fooAInSuper.overridingSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooAInSuper.overridingSymbol(SecondSuperPolyClass)) == None)
    assert(clue(fooAInSuper.overridingSymbol(ThirdSuperClass)) == None)
    assert(clue(fooAInSuper.overridingSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooAInSuper.matchingSymbol(SuperPolyClass, ChildPolyClass)) == Some(fooAInSuper))
    assert(clue(fooAInSuper.matchingSymbol(SecondSuperPolyClass, ChildPolyClass)) == Some(fooXInSecondSuper))
    assert(clue(fooAInSuper.matchingSymbol(ThirdSuperClass, ChildPolyClass)) == None)
    assert(clue(fooAInSuper.matchingSymbol(ChildPolyClass, ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooAInSuper.allOverriddenSymbols.toList) == Nil)
    assert(clue(fooAInSuper.nextOverriddenSymbol) == None)

    // From fooXInChild

    assert(clue(fooXInChild.overriddenSymbol(SuperPolyClass)) == Some(fooAInSuper))
    assert(clue(fooXInChild.overriddenSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooXInChild.overridingSymbol(SuperPolyClass)) == None)
    assert(clue(fooXInChild.overridingSymbol(ChildPolyClass)) == Some(fooXInChild))

    assert(clue(fooXInChild.allOverriddenSymbols.toList) == List(fooXInSecondSuper, fooAInSuper))
    assert(clue(fooXInChild.nextOverriddenSymbol) == Some(fooXInSecondSuper))

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

    assert(clue(fooIntInChild.allOverriddenSymbols.toList) == List(fooIntInSecondSuper, fooBInSuper))
    assert(clue(fooIntInChild.nextOverriddenSymbol) == Some(fooIntInSecondSuper))
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

    assert(!clue(wInParent.isParamAccessor) && !clue(wInParent.isPrivate))
    assert(clue(xInParent.isParamAccessor) && !clue(xInParent.isPrivate))
    assert(!clue(yInParent.isParamAccessor) && !clue(yInParent.isPrivate))

    assert(clue(ChildClass.getDecl(termName("w"))).isEmpty)
    val xInChild = ChildClass.findDecl(termName("x"))
    val yInChild = ChildClass.findDecl(termName("y"))
    val zInChild = ChildClass.findDecl(termName("z"))

    assert(clue(xInChild.isParamAccessor) && clue(xInChild.isPrivate))
    assert(clue(yInChild.isParamAccessor) && clue(yInChild.isPrivate))
    assert(clue(zInChild.isParamAccessor) && !clue(zInChild.isPrivate))

    assert(clue(InnerClass.getDecl(termName("w"))).isEmpty)
    assert(clue(InnerClass.getDecl(termName("x"))).isEmpty)
    val yInInner = InnerClass.findDecl(termName("y"))
    val zInInner = InnerClass.findDecl(termName("z"))

    assert(clue(yInInner.isParamAccessor) && clue(yInInner.isPrivate))
    assert(clue(zInInner.isParamAccessor) && clue(zInInner.isPrivate))

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
        assert(selectSym.isParamAccessor == clue(expectedParamAccessor), fStr)

        assert(!selectSym.isPrivate, fStr)
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

  testWithContext("findMember-refined-method-signature") {
    val RefinedTypeTreeClass = ctx.findTopLevelClass("simple_trees.RefinedTypeTree")

    val fooSym = RefinedTypeTreeClass.findNonOverloadedDecl(termName("foo"))
    val fooBody = fooSym.tree.get.asInstanceOf[DefDef].rhs.get
    val Apply(fun @ Select(qualifier, signedName @ SignedName(SimpleName("m"), _, _)), Nil) = fooBody: @unchecked

    assert(clue(qualifier.tpe).isInstanceOf[TermRef])
    assert(clue(qualifier.tpe.asInstanceOf[TermRef].underlying).isInstanceOf[TermRefinement])

    val optMember = qualifier.tpe.requireType.lookupMember(signedName)
    assert(optMember.isDefined)

    val AClass = RefinedTypeTreeClass.findMember(typeName("A")).asClass
    val AmSym = AClass.findNonOverloadedDecl(termName("m"))

    assert(clue(optMember.get.symbol) == AmSym)
    assert(clue(fooBody.tpe).isRef(defn.IntClass))
  }

  testWithContext("scala-enum-anon-class-signature-name") {
    val ScalaEnumClass = ctx.findTopLevelClass("simple_trees.ScalaEnum")
    val ScalaEnumModuleClass = ctx.findTopLevelModuleClass("simple_trees.ScalaEnum")

    val newMethod = ScalaEnumModuleClass.findNonOverloadedDecl(termName("$new"))
    val body = newMethod.tree.get.asInstanceOf[DefDef].rhs.get
    val Block(List(anonClassDef: ClassDef), expr) = body: @unchecked
    val Typed(app @ Apply(Select(New(_), ctorSignedName: SignedName), Nil), _) = expr: @unchecked

    val anonClassSym = anonClassDef.symbol
    assert(clue(anonClassSym.signatureName) == clue(ctorSignedName.sig.resSig))

    assert(clue(app.tpe).isRef(anonClassSym))
  }

  testWithContext("java-enum") {
    val JavaLangEnumClass = ctx.findTopLevelClass("java.lang.Enum")
    val JavaEnumClass = ctx.findTopLevelClass("simple_trees.JavaEnum")

    val tree = JavaEnumClass.tree.get

    findTree(tree.rhs.parents.head) { case apply: Apply =>
      assert(clue(apply.tpe).isApplied(_.isRef(JavaLangEnumClass), List(_.isRef(JavaEnumClass))))
    }
  }

  testWithContext("toplevel-module-class-with-opaque-type-alias-companion-signature-name") {
    val TopLevelOpaqueTypeAliasModule =
      ctx.findStaticTerm("crosspackagetasty.TopLevelOpaqueTypeAlias$package.TopLevelOpaqueTypeAlias")
    val TopLevelOpaqueTypeAliasModuleClass =
      ctx.findStaticModuleClass("crosspackagetasty.TopLevelOpaqueTypeAlias$package.TopLevelOpaqueTypeAlias")

    val moduleValRhs = TopLevelOpaqueTypeAliasModule.tree.get.asInstanceOf[ValDef].rhs.get
    val Apply(Select(New(_), ctorSignedName: SignedName), Nil) = moduleValRhs: @unchecked

    assert(clue(TopLevelOpaqueTypeAliasModuleClass.signatureName) == clue(ctorSignedName.sig.resSig))
    assert(clue(moduleValRhs.tpe).isRef(TopLevelOpaqueTypeAliasModuleClass))
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

  testWithContext("annotations-scala-2") {
    val SpecializableModuleClass = ctx.findTopLevelModuleClass("scala.Specializable")

    val deprecatedClass = ctx.findTopLevelClass("scala.deprecated")
    val specializedClass = ctx.findTopLevelClass("scala.specialized")

    locally {
      val BitSet1Class = ctx.findStaticClass("scala.collection.immutable.BitSet.BitSet1")
      val List(deprecatedAnnot) = BitSet1Class.annotations: @unchecked

      assert(clue(deprecatedAnnot.symbol) == deprecatedClass)
      assert(clue(deprecatedAnnot.argCount) == 2)
      assert(clue(deprecatedAnnot.argIfConstant(0)).isDefined)
      assert(clue(deprecatedAnnot.argIfConstant(1)) == Some(Constant("2.13.0")))

      intercept[UnsupportedOperationException](deprecatedAnnot.annotConstructor)
    }

    locally {
      val Function1Class = defn.FunctionNClass(1)
      val List(t1, r) = Function1Class.typeParams: @unchecked

      def testAnnotOf(typeParam: ClassTypeParamSymbol, expectedMemberOfSpecializableName: SimpleName): Unit =
        val List(specializedAnnot) = typeParam.annotations: @unchecked

        assert(clue(specializedAnnot.symbol) == specializedClass)
        assert(clue(specializedAnnot.argCount) == 1)
        assert(clue(specializedAnnot.argIfConstant(0)).isEmpty)

        specializedAnnot.arguments(0) match
          case select @ Select(ident @ Ident(SimpleName("Specializable")), `expectedMemberOfSpecializableName`) =>
            assert(clue(ident.symbol) == SpecializableModuleClass.moduleValue.get)
            assert(clue(select.symbol) == SpecializableModuleClass.findDecl(expectedMemberOfSpecializableName))
          case arg =>
            fail("unexpected shape of argument", clues(arg))
      end testAnnotOf

      testAnnotOf(t1, termName("Arg"))
      testAnnotOf(r, termName("Return"))
    }
  }

  testWithContext("annotations-java") {
    val JavaAnnotSingleValueClass = ctx.findTopLevelClass("javadefined.JavaAnnotSingleValue")
    val JavaAnnotWithDefaultClass = ctx.findTopLevelClass("javadefined.JavaAnnotWithDefault")
    val JavaAnnotMultiValuesClass = ctx.findTopLevelClass("javadefined.JavaAnnotMultiValues")
    val JavaAnnotArrayValueClass = ctx.findTopLevelClass("javadefined.JavaAnnotArrayValue")
    val JavaAnnotEnumValueClass = ctx.findTopLevelClass("javadefined.JavaAnnotEnumValue")
    val JavaAnnotClassValueClass = ctx.findTopLevelClass("javadefined.JavaAnnotClassValue")
    val JavaAnnotAnnotValueClass = ctx.findTopLevelClass("javadefined.JavaAnnotAnnotValue")
    val JavaAnnotClassRetentionClass = ctx.findTopLevelClass("javadefined.JavaAnnotClassRetention")

    val JavaAnnotationsClass = ctx.findTopLevelClass("javadefined.JavaAnnotations")

    val TimeUnitModuleClass = ctx.findTopLevelModuleClass("java.util.concurrent.TimeUnit")

    def ok: Unit = ()

    def checkAnnotArgs(sym: TermOrTypeSymbol, annotClass: ClassSymbol)(pf: PartialFunction[List[TermTree], Unit])(
      using munit.Location
    ): Unit =
      val annot = sym.getAnnotation(annotClass).getOrElse(fail(s"$sym does not have an annotation $annotClass"))
      pf.applyOrElse(annot.arguments, args => fail("unexpected annotation arguments", clues(sym, annotClass, args)))
    end checkAnnotArgs

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotSingleValueClass) { case List(Literal(Constant(5))) =>
      ok
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotWithDefaultClass) { case Nil =>
      ok
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotMultiValuesClass) {
      case List(Literal(Constant(5)), Literal(Constant(true))) => ok
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotArrayValueClass) {
      case List(SeqLiteral(List(Literal(Constant(2)), _, _, Literal(Constant(7))), _)) => ok
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotEnumValueClass) { case List(ident @ Ident(SimpleName("MINUTES"))) =>
      assert(clue(ident.tpe).isRef(TimeUnitModuleClass.findDecl(termName("MINUTES"))))
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotClassValueClass) {
      case List(Literal(const)) if const.tag == Constants.ClazzTag =>
        assert(clue(const.typeValue).isRef(defn.ShortClass))
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotAnnotValueClass) { case List(annotTree) =>
      val nestedAnnot = Annotation(annotTree)
      assert(clue(nestedAnnot.symbol) == JavaAnnotSingleValueClass)
      nestedAnnot.arguments match
        case List(Literal(Constant(42))) => ok
        case nestedArgs                  => fail("unexpected nested arguments", clues(nestedArgs))
    }

    checkAnnotArgs(JavaAnnotationsClass, JavaAnnotClassRetentionClass) { case Nil =>
      ok
    }

    val annotatedField = JavaAnnotationsClass.findDecl(termName("annotatedField"))

    checkAnnotArgs(annotatedField, JavaAnnotWithDefaultClass) { case List(Literal(Constant(false))) =>
      ok
    }

    checkAnnotArgs(annotatedField, JavaAnnotMultiValuesClass) {
      case List(Literal(Constant(true)), Literal(Constant(5))) => ok
    }

    checkAnnotArgs(annotatedField, JavaAnnotClassValueClass) {
      case List(Literal(const)) if const.tag == Constants.ClazzTag =>
        assert(clue(const.typeValue).isRef(ctx.findTopLevelClass("java.lang.CharSequence")))
    }

    checkAnnotArgs(annotatedField, JavaAnnotClassRetentionClass) { case Nil =>
      ok
    }

    val annotatedMethod = JavaAnnotationsClass.findNonOverloadedDecl(termName("annotatedMethod"))

    checkAnnotArgs(annotatedMethod, JavaAnnotClassValueClass) {
      case List(Literal(const)) if const.tag == Constants.ClazzTag =>
        assert(clue(const.typeValue).isRef(defn.UnitClass))
    }

    checkAnnotArgs(annotatedMethod, JavaAnnotClassRetentionClass) { case Nil =>
      ok
    }

    val otherAnnotatedMethod = JavaAnnotationsClass.findNonOverloadedDecl(termName("otherAnnotatedMethod"))

    checkAnnotArgs(otherAnnotatedMethod, JavaAnnotClassValueClass) {
      case List(Literal(const)) if const.tag == Constants.ClazzTag =>
        // Note that `isRef` only accepts a `TypeRef` of the given symbol; not an `AppliedType`
        assert(clue(const.typeValue).isRef(ctx.findTopLevelClass("java.util.List")))
    }

    val annotatedParams = JavaAnnotationsClass.findNonOverloadedDecl(termName("annotatedParams"))
    val List(Right(_), Left(paramSyms)) = annotatedParams.paramSymss: @unchecked

    assert(clue(paramSyms(0).annotations) == Nil)

    checkAnnotArgs(paramSyms(1), JavaAnnotSingleValueClass) { case List(Literal(Constant(123))) =>
      ok
    }

    checkAnnotArgs(paramSyms(2), JavaAnnotClassValueClass) {
      case List(Literal(const)) if const.tag == Constants.ClazzTag =>
        assert(clue(const.typeValue).isArrayOf(_.isRef(defn.StringClass)))
    }

    checkAnnotArgs(paramSyms(2), JavaAnnotClassRetentionClass) { case Nil =>
      ok
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

    def testApply(testMethodName: String, targetMethodName: SimpleName, expectedType: TermType => Boolean): Unit =
      val rhs @ Apply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    def testDirect(testMethodName: String, targetMethodName: SimpleName, expectedType: TermType => Boolean): Unit =
      val fun @ (_: Select) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(fun.tpe.widenTermRef)), testMethodName)

    def testTypeApply(testMethodName: String, targetMethodName: SimpleName, expectedType: TermType => Boolean): Unit =
      val rhs @ TypeApply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isAnyMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    def testApplyTypeApply(
      testMethodName: String,
      targetMethodName: SimpleName,
      expectedType: TermType => Boolean
    ): Unit =
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

    // FIXME #436: the type test should be _.widenTermRef.isRef(defn.IntClass)
    testTypeApply("testTypeCast", termName("$asInstanceOf$"), _.isInstanceOf[TermRef])

    testApplyTypeApply(
      "testGetClassAny",
      nme.m_getClass,
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isNothing, _.isRef(defn.AnyClass))))
    )
    testApplyTypeApply(
      "testGetClassProduct",
      nme.m_getClass,
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isNothing, _.isRef(ProductClass))))
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
      _.isApplied(_.isRef(ClassClass), List(_.isBounded(_.isNothing, _.isRef(defn.IntClass))))
    )
  }

  testWithContext("methods on String") {
    val StringMethodsClass = ctx.findTopLevelClass("simple_trees.StringMethods")
    val StringClass = defn.StringClass

    def rhsOf(methodName: String): TermTree =
      StringMethodsClass.findNonOverloadedDecl(termName(methodName)).tree.get.asInstanceOf[DefDef].rhs.get

    def isStringMethod(sym: Symbol, name: SimpleName): Boolean =
      sym.owner == StringClass && sym.name == name

    def testApply(testMethodName: String, targetMethodName: SimpleName, expectedType: TermType => Boolean): Unit =
      val rhs @ Apply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isStringMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)

    testApply("testPlusAny", nme.m_+, _.isRef(defn.StringClass))
  }

  testWithContext("methods on Object") {
    val ObjectMethodsClass = ctx.findTopLevelClass("simple_trees.ObjectMethods")

    def rhsOf(methodName: String): TermTree =
      ObjectMethodsClass.findNonOverloadedDecl(termName(methodName)).tree.get.asInstanceOf[DefDef].rhs.get

    def isObjectMethod(sym: Symbol, name: SimpleName): Boolean =
      sym.owner == defn.ObjectClass && sym.name == name

    def testApply(testMethodName: String, targetMethodName: SimpleName, expectedType: TermType => Boolean): TermSymbol =
      val rhs @ Apply(fun: Select, _) = rhsOf(testMethodName): @unchecked
      assert(isObjectMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)
      fun.symbol.asTerm
    end testApply

    def testApplyTypeApply(
      testMethodName: String,
      targetMethodName: SimpleName,
      expectedType: TermType => Boolean
    ): TermSymbol =
      val rhs @ Apply(TypeApply(fun: Select, _), _) = rhsOf(testMethodName): @unchecked
      assert(isObjectMethod(clue(fun.symbol), clue(targetMethodName)), testMethodName)
      assert(expectedType(clue(rhs.tpe)), testMethodName)
      fun.symbol.asTerm
    end testApplyTypeApply

    val eqSym = testApply("testEq", nme.m_eq, _.isRef(defn.BooleanClass))
    val neSym = testApply("testNe", nme.m_ne, _.isRef(defn.BooleanClass))

    val synchronizedSym = testApplyTypeApply("testSynchronized", nme.m_synchronized, _.isRef(defn.IntClass))

    testApply("testNotifyAll", termName("notifyAll"), _.isRef(defn.UnitClass))
    testApply("testWait", termName("wait"), _.isRef(defn.UnitClass))

    testApply("testClone", termName("clone"), _.isType(_.isFromJavaObject))

    /* Check that the symbols we found are also the ones of `defn.Object_x`.
     * Wheck do this *after* having performed the rest of the tests, because we want to
     * ensure that the methods exist regardless of if we access `defn.Object_x` or not.
     */
    assert(clue(eqSym) == clue(defn.Object_eq))
    assert(clue(neSym) == clue(defn.Object_ne))
    assert(clue(synchronizedSym) == clue(defn.Object_synchronized))
  }

  testWithContext("super calls") {
    val BaseClass = ctx.findTopLevelClass("simple_trees.Base")
    val BaseTraitClass = ctx.findTopLevelClass("simple_trees.BaseTrait")
    val ChildClass = ctx.findTopLevelClass("simple_trees.Super")

    def rhsOf(methodName: String): TermTree =
      ChildClass.findNonOverloadedDecl(termName(methodName)).tree.get.asInstanceOf[DefDef].rhs.get

    for strPrefix <- List("Class", "Trait", "Common") do
      val strPrefixL = strPrefix.toLowerCase().nn
      val fName = termName(strPrefixL + "F")
      val gName = termName(strPrefixL + "G")
      val fTestSuffix = strPrefix + "F"
      val gTestSuffix = strPrefix + "G"

      val expectedParent = if strPrefix == "Class" then BaseClass else BaseTraitClass

      val fInParent = expectedParent.findNonOverloadedDecl(fName)
      val fInChild = ChildClass.findNonOverloadedDecl(fName)

      locally {
        val Apply(select: Select, Nil) = rhsOf(s"callMy$fTestSuffix"): @unchecked
        assert(clue(select.symbol) == clue(fInChild))
      }

      locally {
        val Apply(select: Select, Nil) = rhsOf(s"callBareSuper$fTestSuffix"): @unchecked
        assert(clue(select.symbol) == clue(fInParent))
      }

      if strPrefix != "Common" then
        locally {
          val Apply(select: Select, Nil) = rhsOf(s"callQualifiedSuper$fTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(fInParent))
        }
      else
        locally {
          val fInBase = BaseClass.findNonOverloadedDecl(fName)
          val Apply(select: Select, Nil) = rhsOf(s"callQualifiedBaseSuper$fTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(fInBase))
        }

        locally {
          val fInBaseTrait = BaseTraitClass.findNonOverloadedDecl(fName)
          val Apply(select: Select, Nil) = rhsOf(s"callQualifiedBaseTraitSuper$fTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(fInBaseTrait))
        }
      end if

      val gInParent = expectedParent.findNonOverloadedDecl(gName)
      val gInChild = ChildClass.findNonOverloadedDecl(gName)

      locally {
        val select @ (_: Select) = rhsOf(s"callMy$gTestSuffix"): @unchecked
        assert(clue(select.symbol) == clue(gInChild))
      }

      locally {
        val select @ (_: Select) = rhsOf(s"callBareSuper$gTestSuffix"): @unchecked
        select.symbol
        assert(clue(select.symbol) == clue(gInParent))
      }

      if strPrefix != "Common" then
        locally {
          val select @ (_: Select) = rhsOf(s"callQualifiedSuper$gTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(gInParent))
        }
      else
        locally {
          val gInBase = BaseClass.findNonOverloadedDecl(gName)
          val select @ (_: Select) = rhsOf(s"callQualifiedBaseSuper$gTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(gInBase))
        }

        locally {
          val gInBaseTrait = BaseTraitClass.findNonOverloadedDecl(gName)
          val select @ (_: Select) = rhsOf(s"callQualifiedBaseTraitSuper$gTestSuffix"): @unchecked
          assert(clue(select.symbol) == clue(gInBaseTrait))
        }
      end if
    end for
  }

  testWithContext("appliedRefInsideThis") {
    val FooClass = ctx.findStaticClass("simple_trees.SelfTypes.Foo")
    val BarClass = ctx.findStaticClass("simple_trees.SelfTypes.Bar")
    val FooBarClass = ctx.findStaticClass("simple_trees.SelfTypes.FooBar")

    val fooTArg = FooClass.typeParams.head
    val List(barTArg1, barTArg2) = BarClass.typeParams: @unchecked

    assert(clue(FooClass.appliedRefInsideThis).isApplied(_.isRef(FooClass), List(_.isRef(fooTArg))))
    assert(clue(BarClass.appliedRefInsideThis).isApplied(_.isRef(BarClass), List(_.isRef(barTArg1), _.isRef(barTArg2))))
    assert(clue(FooBarClass.appliedRefInsideThis).isRef(FooBarClass))
  }

  testWithContext("self-types") {
    val FooClass = ctx.findStaticClass("simple_trees.SelfTypes.Foo")
    val BarClass = ctx.findStaticClass("simple_trees.SelfTypes.Bar")
    val FooBarClass = ctx.findStaticClass("simple_trees.SelfTypes.FooBar")

    val fooTArg = FooClass.typeParams.head
    val List(barTArg1, barTArg2) = BarClass.typeParams: @unchecked

    val expectedGivenSelfType: Type => Boolean =
      tpe => tpe.isApplied(_.isRef(BarClass), List(_.isRef(fooTArg), _.isRef(defn.IntClass)))

    assert(clue(FooClass.givenSelfType).exists(expectedGivenSelfType))
    assert(
      clue(FooClass.selfType).isIntersectionOf(
        expectedGivenSelfType,
        _.isApplied(_.isRef(FooClass), List(_.isRef(FooClass.typeParams.head)))
      )
    )

    assert(clue(BarClass.givenSelfType).isEmpty)
    assert(clue(BarClass.selfType).isApplied(_.isRef(BarClass), List(_.isRef(barTArg1), _.isRef(barTArg2))))

    assert(clue(FooBarClass.givenSelfType).isEmpty)
    assert(clue(FooBarClass.selfType).isRef(FooBarClass))
  }

  testWithContext("scala2-self-types") {
    val ClassManifestAlias = ctx.findStaticType("scala.reflect.package.ClassManifest")
    val ClassManifestDeprecatedApisClass = ctx.findTopLevelClass("scala.reflect.ClassManifestDeprecatedApis")

    val cmDeprecatedApisTArg = ClassManifestDeprecatedApisClass.typeParams.head

    val expectedGivenSelfType: Type => Boolean =
      tpe => tpe.isApplied(_.isRef(ClassManifestAlias), List(_.isRef(cmDeprecatedApisTArg)))

    assert(clue(ClassManifestDeprecatedApisClass.givenSelfType).exists(expectedGivenSelfType))
    assert(
      clue(ClassManifestDeprecatedApisClass.selfType).isIntersectionOf(
        expectedGivenSelfType,
        _.isApplied(_.isRef(ClassManifestDeprecatedApisClass), List(_.isRef(cmDeprecatedApisTArg)))
      )
    )
  }

  testWithContext("selections-with-self-types") {
    val FooClass = ctx.findStaticClass("simple_trees.SelfTypes.Foo")
    val BarClass = ctx.findStaticClass("simple_trees.SelfTypes.Bar")
    val PairClass = ctx.findStaticClass("simple_trees.SelfTypes.Pair")

    val fooTArg = FooClass.typeParams.head
    val List(barTArg1, barTArg2) = BarClass.typeParams: @unchecked

    val targetMethod = BarClass.findNonOverloadedDecl(termName("bar"))

    for testMethodName <- List("throughSelf", "throughThis", "bare") do
      val DefDef(_, _, _, Some(body), _) = FooClass.findNonOverloadedDecl(termName(testMethodName)).tree.get: @unchecked
      val Apply(sel @ Select(ths: This, SignedName(SimpleName("bar"), _, _)), Nil) = body: @unchecked

      assert(clue(ths.tpe).isInstanceOf[ThisType])
      assert(clue(ths.tpe.asInstanceOf[ThisType].cls) == FooClass)
      assert(clue(sel.tpe).isRef(targetMethod))

      assert(clue(body.tpe).isApplied(_.isRef(PairClass), List(_.isRef(fooTArg), _.isRef(defn.IntClass))))
    end for
  }

  testWithContext("opaque-type-aliases") {
    val TypeMemberClass = ctx.findTopLevelClass("simple_trees.TypeMember")

    val opaqueNoBounds = TypeMemberClass.findDecl(typeName("Opaque")).asInstanceOf[TypeMemberSymbol]
    assert(opaqueNoBounds.isOpaqueTypeAlias)
    opaqueNoBounds.typeDef match
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, alias) =>
        assert(clue(bounds.low).isNothing)
        assert(clue(bounds.high).isAny)
        assert(clue(alias).isRef(defn.IntClass))
      case typeDef =>
        fail("unexpected typeDef", clues(typeDef))

    val opaqueWithBounds = TypeMemberClass.findDecl(typeName("OpaqueWithBounds")).asInstanceOf[TypeMemberSymbol]
    assert(opaqueWithBounds.isOpaqueTypeAlias)
    opaqueWithBounds.typeDef match
      case TypeMemberDefinition.OpaqueTypeAlias(bounds, alias) =>
        assert(clue(bounds.low).isRef(defn.NullClass))
        assert(clue(bounds.high).isRef(ctx.findTopLevelClass("scala.Product")))
        assert(clue(alias).isRef(defn.NullClass))
      case typeDef =>
        fail("unexpected typeDef", clues(typeDef))
  }

  testWithContext("evil-class-names-1") {
    val EvilClassClass = ctx.findTopLevelClass("simple_trees.evil_$_class")
    assert(clue(EvilClassClass).name == typeName("evil_$_class"))

    val EvilTraitClass = ctx.findTopLevelClass("simple_trees.evil_$_trait")
    assert(clue(EvilTraitClass).name == typeName("evil_$_trait"))

    val EvilClassInnerClass = EvilClassClass.findDecl(typeName("evil_$_inner"))
    assert(clue(EvilClassInnerClass).name == typeName("evil_$_inner"))

    val EvilTraitInnerClass = EvilTraitClass.findDecl(typeName("evil_$_inner"))
    assert(clue(EvilTraitInnerClass).name == typeName("evil_$_inner"))
  }

  testWithContext("evil-class-names-2") {
    val SubEvilClassClass = ctx.findStaticClass("simple_trees.EvilClassNames.SubEvilClass")
    assert(clue(SubEvilClassClass.parentClasses.head).name == typeName("evil_$_class"))

    val SubEvilTraitClass = ctx.findStaticClass("simple_trees.EvilClassNames.SubEvilTrait")
    assert(clue(SubEvilTraitClass.parentClasses(1)).name == typeName("evil_$_trait"))
  }

  testWithContext("lookupMember") {
    val TypeMemberClass = ctx.findTopLevelClass("simple_trees.TypeMember")
    val prefix = TypeMemberClass.staticRef

    val TypeMemberRef = prefix.lookupMember(typeName("TypeMember")).get
    assert(TypeMemberRef.optSymbol == Some(TypeMemberClass.findDecl(typeName("TypeMember"))))

    assert(clue(prefix.lookupMember(typeName("NonExistentType"))).isEmpty)

    val termMemberName = termName("mTypeAlias")
    val termMemberSym = TypeMemberClass.findNonOverloadedDecl(termMemberName)
    val termMemberSignedName = termMemberSym.signedName

    val termMemberRef = prefix.lookupMember(termMemberSignedName).get
    assert(termMemberRef.symbol == termMemberSym)

    assert(clue(prefix.lookupMember(termName("nonExistentTerm"))).isEmpty)
  }

  testWithContext("scala-2-type-lambda-in-args") {
    val IsMapClass = ctx.findTopLevelClass("scala.collection.generic.IsMap")

    val IterableClass = ctx.findTopLevelClass("scala.collection.Iterable")
    val Tuple2Class = ctx.findTopLevelClass("scala.Tuple2")

    val applySym = IsMapClass.findNonOverloadedDecl(termName("apply"))
    applySym.declaredType match
      case mt: MethodType =>
        assert(clue(mt).paramNames.sizeIs == 1)
        mt.resultType match
          case resultApplied: AppliedType =>
            assert(resultApplied.args.sizeIs == 4, clues(mt))
            resultApplied.args(2) match
              case tl: TypeLambda =>
                assert(clue(tl).paramNames.sizeIs == 2)
                val refs = tl.paramRefs
                assert(
                  clue(tl).resultType.isApplied(
                    _.isRef(IterableClass),
                    List(_.isApplied(_.isRef(Tuple2Class), List(_ eq refs(0), _ eq refs(1))))
                  )
                )
              case _ =>
                fail("unexpected type for 'apply'", clues(mt))
          case _ =>
            fail("unexpected type for 'apply'", clues(mt))
      case mt =>
        fail("unexpected type for 'apply'", clues(mt))
  }

  testWithContext("no-scala-2-problematic-getClass") {
    val primitiveClasses = List(
      defn.UnitClass,
      defn.BooleanClass,
      defn.CharClass,
      defn.ByteClass,
      defn.ShortClass,
      defn.IntClass,
      defn.LongClass,
      defn.FloatClass,
      defn.DoubleClass
    )

    for primitiveClass <- primitiveClasses do
      assert(clue(clue(primitiveClass).getAllOverloadedDecls(nme.m_getClass)).isEmpty)
  }

  testWithContext("scala-2-refined-types") {
    val ScalaRunTimeClass = ctx.findTopLevelModuleClass("scala.runtime.ScalaRunTime")
    val dropSym = ScalaRunTimeClass.findNonOverloadedDecl(termName("drop"))
    dropSym.declaredType match
      case pt: PolyType if pt.paramNames.sizeIs == 1 =>
        val typeParamRef = pt.paramRefs.head
        pt.resultType match
          case mt1: MethodType if mt1.paramNames.sizeIs == 2 =>
            assert(clue(mt1.paramTypes(0)) eq clue(typeParamRef))
            mt1.resultType match
              case mt2: MethodType if mt2.paramNames.sizeIs == 1 =>
                mt2.paramTypes(0) match
                  case refinement: TypeRefinement =>
                    assert(clue(refinement).parent.isApplied(_ => true, List(_ eq typeParamRef)))
                    assert(clue(refinement).refinedName == typeName("C"))
                    assert(clue(refinement).refinedBounds.low.isNothing)
                    assert(clue(refinement).refinedBounds.high eq clue(typeParamRef))
                  case _ =>
                    fail("unexpected type", clues(pt))
              case _ =>
                fail("unexpected type", clues(pt))
          case _ =>
            fail("unexpected type", clues(pt))
      case pt =>
        fail("unexpected type", clues(pt))
  }

  testWithContext("scala-2-with-types") {
    val WrappedStringClass = ctx.findTopLevelClass("scala.collection.immutable.WrappedString")
    val StepperClass = ctx.findTopLevelClass("scala.collection.Stepper")
    val EfficientSplitClass = ctx.findStaticClass("scala.collection.Stepper.EfficientSplit")

    val stepperSym = WrappedStringClass.findNonOverloadedDecl(termName("stepper"))
    stepperSym.declaredType match
      case pt: PolyType if pt.paramNames.sizeIs == 1 =>
        val typeParamRef = pt.paramRefs.head
        pt.resultType match
          case mt: MethodType if mt.paramNames.sizeIs == 1 =>
            mt.resultType match
              case resultType: AndType =>
                assert(clue(resultType).first eq typeParamRef)
                assert(clue(resultType).second.isRef(EfficientSplitClass))
              case _ =>
                fail("unexpected type", clues(pt))
          case _ =>
            fail("unexpected type", clues(pt))
      case pt =>
        fail("unexpected type", clues(pt))
  }

  testWithContext("scala-2-class-constructor-types") {
    val SomeClass = ctx.findTopLevelClass("scala.Some")
    val ctor = SomeClass.findNonOverloadedDecl(nme.Constructor)
    ctor.declaredType match
      case pt: PolyType =>
        assert(clue(pt).paramNames == List(typeName("A")))
        val typeParamRef = pt.paramRefs.head
        pt.resultType match
          case mt: MethodType =>
            assert(clue(mt).paramNames == List(termName("value")))
            assert(clue(mt).paramTypes.head eq typeParamRef)
            assert(clue(mt).resultType.isRef(defn.UnitClass))
          case _ =>
            fail("unexpected type", clues(pt))
      case pt =>
        fail("unexpected type", clues(pt))
  }

  testWithContext("scala-2-trait-constructor-types") {
    val MapClass = ctx.findTopLevelClass("scala.collection.immutable.Map")
    val ctor = MapClass.findNonOverloadedDecl(nme.Constructor)
    ctor.declaredType match
      case pt: PolyType =>
        assert(clue(pt).paramNames == List(typeName("K"), typeName("V")))
        pt.resultType match
          case mt: MethodType =>
            assert(clue(mt).paramNames == Nil)
            assert(clue(mt).resultType.isRef(defn.UnitClass))
          case _ =>
            fail("unexpected type", clues(pt))
      case pt =>
        fail("unexpected type", clues(pt))
  }

  testWithContext("scala-2-higher-kinded-type-param") {
    val AccumulatorClass = ctx.findTopLevelClass("scala.jdk.Accumulator")
    val MutableSeqClass = ctx.findTopLevelClass("scala.collection.mutable.Seq")

    val typeParams = AccumulatorClass.typeParams
    assert(clue(typeParams).map(_.name) == List(typeName("A"), typeName("CC"), typeName("C")))

    val tpA = typeParams(0)
    assert(clue(tpA.declaredBounds).low.isNothing)
    assert(clue(tpA.declaredBounds).high.isAny)

    val tpCC = typeParams(1)
    assert(clue(tpCC.declaredBounds).low.isNothing)
    tpCC.declaredBounds.high match
      case tl: TypeLambda =>
        assert(clue(tl.paramNames) == List(typeName("X")))
        val paramRef = tl.paramRefs.head
        assert(clue(tl.resultType).isApplied(_.isRef(MutableSeqClass), List(_ eq paramRef)))
      case high =>
        fail("unexpected upper bound for CC", clues(high))

    val tpC = typeParams(2)
    assert(clue(tpC.declaredBounds).low.isNothing)
    clue(tpC.declaredBounds).high match
      case high: AppliedType =>
        assert(clue(high).tycon.isRef(MutableSeqClass))
        high.args.head match
          case typeArg: TypeRef =>
            assert(clue(typeArg.optSymbol) == Some(tpA))
            typeArg.prefix match
              case prefix: ThisType =>
                assert(clue(prefix).cls == AccumulatorClass)
              case _ =>
                fail("unexpected upper bound for C", clues(high))
          case high =>
            fail("unexpected upper bound for C", clues(high))
      case high =>
        fail("unexpected upper bound for C", clues(high))
  }

  testWithContext("scala-2-existentially-bound-syms-are-not-decls") {
    val DefaultSerializableClass = ctx.findTopLevelClass("scala.collection.generic.DefaultSerializable")

    assert(clue(DefaultSerializableClass.getDecl(typeName("_$1"))).isEmpty)

    assert(!clue(DefaultSerializableClass.declarations).exists { decl =>
      decl.name.toString().contains("$")
    })
  }

  testWithContext("method-type-modifiers") {
    val IterableOnceOpsClass = ctx.findTopLevelClass("scala.collection.IterableOnceOps")
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")
    val UsingGivenClass = ctx.findTopLevelClass("simple_trees.UsingGiven")

    def testMethod(cls: ClassSymbol, name: String, expectContextual: Boolean, expectImplicit: Boolean): Unit =
      val sym = cls.findNonOverloadedDecl(termName(name))
      val methodType = sym.declaredType match
        case pt: PolyType => pt.resultType.asInstanceOf[MethodType]
        case mt           => mt.asInstanceOf[MethodType]
      assert(clue(methodType).isContextual == clue(expectContextual), clues(name))
      assert(clue(methodType).isImplicit == clue(expectImplicit), clues(name))
      assert(clue(methodType).isImplicitOrContextual == clue(expectContextual || expectImplicit), clues(name))
    end testMethod

    // Scala 3 methods

    testMethod(UsingGivenClass, "useNormal", expectContextual = false, expectImplicit = false)
    testMethod(UsingGivenClass, "useGiven", expectContextual = true, expectImplicit = false)
    testMethod(UsingGivenClass, "useImplicit", expectContextual = false, expectImplicit = true)

    // Scala 2 methods

    testMethod(ListClass, "exists", expectContextual = false, expectImplicit = false)
    testMethod(IterableOnceOpsClass, "sum", expectContextual = false, expectImplicit = true)

    // Term refinements

    def testRefinement(cls: ClassSymbol, name: String, expectContextual: Boolean, expectImplicit: Boolean): Unit =
      val sym = cls.findDecl(termName(name))
      val methodType = sym.declaredType.asInstanceOf[TermRefinement].refinedType.asInstanceOf[MethodType]
      assert(clue(methodType).isContextual == clue(expectContextual), clues(name))
      assert(clue(methodType).isImplicit == clue(expectImplicit), clues(name))
      assert(clue(methodType).isImplicitOrContextual == clue(expectContextual || expectImplicit), clues(name))
    end testRefinement

    testRefinement(UsingGivenClass, "refinementWithNormal", expectContextual = false, expectImplicit = false)
    testRefinement(UsingGivenClass, "refinementWithUsing", expectContextual = true, expectImplicit = false)
    testRefinement(UsingGivenClass, "refinementWithImplicit", expectContextual = false, expectImplicit = true)
  }

  testWithContext("scala-2-recursive-refinements") {
    val IsMapClass = ctx.findTopLevelModuleClass("scala.collection.generic.IsMap")

    val mapOpsIsMapSym = IsMapClass.findNonOverloadedDecl(termName("mapOpsIsMap"))

    mapOpsIsMapSym.declaredType match
      case pt: PolyType =>
        assert(clue(pt.paramNames) == List(typeName("CC0"), typeName("K0"), typeName("V0")))
        val paramRefs = pt.paramRefs

        def failWrongResultType(): Nothing =
          fail(s"unexpected result type: ${pt.resultType}")

        // { α => (((scala.collection.generic.IsMap[CC0[K0, V0]] { type V = V0 }) { type C = CC0[α.K, α.V] }) { type K = K0 }) }
        pt.resultType match
          case rt: RecType =>
            rt.parent match
              case kRefinement: TypeRefinement =>
                kRefinement.parent match
                  case cRefinement: TypeRefinement =>
                    cRefinement.refinedBounds match
                      case TypeAlias(appliedCC0: AppliedType) =>
                        assert(clue(appliedCC0.tycon) eq paramRefs(0))
                        assert(clue(appliedCC0.args).sizeIs == 2)
                        appliedCC0.args(0) match
                          case alphaK: TypeRef =>
                            assert(clue(alphaK).name == typeName("K"))
                            assert(clue(alphaK).prefix eq rt.recThis)
                          case _ =>
                            failWrongResultType()
                      case _ =>
                        failWrongResultType()
                  case _ =>
                    failWrongResultType()
              case _ =>
                failWrongResultType()
          case _ =>
            failWrongResultType()
      case pt =>
        fail(s"not a PolyType: ${pt.showBasic}")
  }

  testWithContext("singleton-class-type") {
    val SingletonClassTypeClass = ctx.findTopLevelClass("simple_trees.SingletonClassType")

    val fooSym = SingletonClassTypeClass.findDecl(termName("foo"))
    assert(clue(fooSym.declaredType).isTypeRefOf(defn.SingletonClass))
  }

  testWithContext("join") {
    val UnionTypeJoinClass = ctx.findTopLevelModuleClass("simple_trees.UnionTypeJoin")

    val aClass = UnionTypeJoinClass.findDecl(typeName("A")).asClass
    val bClass = UnionTypeJoinClass.findDecl(typeName("B")).asClass
    val cClass = UnionTypeJoinClass.findDecl(typeName("C")).asClass
    val dClass = UnionTypeJoinClass.findDecl(typeName("D")).asClass
    val eClass = UnionTypeJoinClass.findDecl(typeName("E")).asClass

    // Spec says that join(A | B) = C[A | B] & D
    val orType = OrType(aClass.staticRef, bClass.staticRef)
    assert(
      clue(orType.join).isIntersectionOf(
        _.isApplied(_.isRef(cClass), List(_.isUnionOf(_.isRef(aClass), _.isRef(bClass)))),
        _.isRef(dClass)
      )
    )
  }

  testWithContext("signature-polymorphic-methods") {
    val MethodHandleClass = ctx.findTopLevelClass("java.lang.invoke.MethodHandle")

    val invokeExact = MethodHandleClass.findNonOverloadedDecl(termName("invokeExact"))
    assert(clue(invokeExact.isSignaturePolymorphicMethod))

    val invokeWithArgumentss = MethodHandleClass.findAllOverloadedDecls(termName("invokeWithArguments"))
    for invokeWithArguments <- invokeWithArgumentss do assert(!clue(invokeWithArguments.isSignaturePolymorphicMethod))

    // Try with VarHandle -- ignored on JDK 8
    ctx.findPackage("java.lang.invoke").getDecl(typeName("VarHandle")) match
      case Some(sym) =>
        val VarHandleClass = sym.asClass

        val get = VarHandleClass.findNonOverloadedDecl(termName("get"))
        assert(clue(get.isSignaturePolymorphicMethod))

        val toMethodHandle = VarHandleClass.findNonOverloadedDecl(termName("toMethodHandle"))
        assert(!clue(toMethodHandle.isSignaturePolymorphicMethod))

      case None =>
        // Ignore
        ()
    end match
  }

  testWithContext("call-signature-polymorphic-methods") {
    val ApplySigPolyClass = ctx.findTopLevelClass("simple_trees.ApplySigPoly")
    val FooClass = ctx.findStaticClass("simple_trees.ApplySigPoly.Foo")

    val DefDef(_, _, _, Some(testBody), _) =
      ApplySigPolyClass.findNonOverloadedDecl(termName("test")).tree.get: @unchecked

    def findCall(methodHandleVarName: String): Apply =
      findTree(testBody) {
        case app @ Apply(
              Select(Ident(SimpleName(`methodHandleVarName`)), SignedName(SimpleName("invokeExact"), _, _)),
              _
            ) =>
          app
      }

    def checkTypes(call: Apply, paramTypes0: List[Type], resultType: Type): Unit =
      val paramTypes = FooClass.staticRef :: paramTypes0
      val methodType = call.methodType
      assert(methodType.paramTypes.size == paramTypes.size)
      assert(call.args.size == paramTypes.size)
      for (expectedType, methodParamType, arg) <- paramTypes.lazyZip(methodType.paramTypes).lazyZip(call.args) do
        assert(clue(expectedType).isSameType(clue(methodParamType)))
        assert(clue(arg.tpe.requireType).isSubType(clue(expectedType)))
      assert(clue(methodType.resultType.requireType).isSameType(clue(resultType)))
    end checkTypes

    checkTypes(findCall("mhNeg"), List(defn.IntType), defn.IntType)
    checkTypes(findCall("mhRev"), List(defn.StringType), defn.StringType)
    checkTypes(findCall("mhOverL"), List(defn.LongType), defn.StringType)
    checkTypes(findCall("mhOverI"), List(defn.IntType), defn.StringType)
    checkTypes(findCall("mhUnit"), List(defn.StringType), defn.UnitType)
    checkTypes(findCall("mhObj"), List(defn.StringType), defn.AnyType)
  }

  testWithContext("java-shadowing-inner-class") {
    val JavaShadowingClassParentClass = ctx.findTopLevelClass("javadefined.JavaShadowingClassParent")
    val JavaShadowingClassChildClass = ctx.findTopLevelClass("javadefined.JavaShadowingClassChild")

    val ParentInnerClass = JavaShadowingClassParentClass.findDecl(typeName("InnerClass")).asClass
    val ChildInnerClass = JavaShadowingClassChildClass.findDecl(typeName("InnerClass")).asClass
    assert(clue(ParentInnerClass) != clue(ChildInnerClass))

    val JavaClassShadowingClass = ctx.findTopLevelClass("simple_trees.JavaClassShadowing")

    val testSym = JavaClassShadowingClass.findNonOverloadedDecl(termName("test"))
    val useParentInnerSym = JavaClassShadowingClass.findNonOverloadedDecl(termName("useParentInner"))
    val useChildInnerSym = JavaClassShadowingClass.findNonOverloadedDecl(termName("useChildInner"))

    val DefDef(_, _, _, Some(body), _) = testSym.tree.get: @unchecked

    val parentInnerSym = findTree(body) { case ValDef(SimpleName("parentInner"), _, _, sym) =>
      sym
    }
    assert(clue(parentInnerSym.localRef.underlying).isRef(ParentInnerClass))
    assert(!clue(parentInnerSym.localRef.underlying).isRef(ChildInnerClass))

    val childInnerSym = findTree(body) { case ValDef(SimpleName("childInner"), _, _, sym) =>
      sym
    }
    assert(!clue(childInnerSym.localRef.underlying).isRef(ParentInnerClass))
    assert(clue(childInnerSym.localRef.underlying).isRef(ChildInnerClass))
  }

  testWithContext("paramSymss-synthetic") {
    assert(clue(defn.Any_##.paramSymss) == Nil)

    locally {
      val List(Left(List(thatSym))) = defn.Any_==.paramSymss: @unchecked
      assert(clue(thatSym.name) == termName("that"))
      assert(clue(thatSym.declaredType).isRef(defn.AnyClass))
    }

    locally {
      val List(Right(List(aSym))) = defn.Any_asInstanceOf.paramSymss: @unchecked
      assert(clue(aSym.name) == typeName("A"))
      assert(clue(aSym.declaredBounds).isNothingAnyBounds)
    }
  }

  testWithContext("paramSymss-scala-3") {
    locally {
      val GenericMethodClass = ctx.findTopLevelClass("simple_trees.GenericMethod")
      val identity = GenericMethodClass.findNonOverloadedDecl(termName("identity"))
      val List(Right(List(t)), Left(List(x))) = identity.paramSymss: @unchecked

      assert(clue(t.name) == typeName("T"))
      assert(clue(t.declaredBounds).isNothingAnyBounds)

      assert(clue(x.name) == termName("x"))
      assert(clue(x.declaredType).isRef(t))
    }

    locally {
      val GenericMethodWithTypeParamDependenciesClass =
        ctx.findTopLevelClass("simple_trees.GenericMethodWithTypeParamDependencies")
      val foo = GenericMethodWithTypeParamDependenciesClass.findNonOverloadedDecl(termName("foo"))
      val List(Right(List(a, b, c, d)), Left(Nil)) = foo.paramSymss: @unchecked

      assert(clue(a.name) == typeName("A"))

      assert(clue(a.declaredBounds).isNothingAnyBounds)
      assert(clue(b.declaredBounds).isBounds(_.isRef(d), _.isRef(a)))
      assert(clue(c.declaredBounds).isBounds(_.isNothing, _.isRef(b)))
      assert(clue(d.declaredBounds).isNothingAnyBounds)
    }

    locally {
      val GenericClassWithTypeParamDependenciesClass =
        ctx.findTopLevelClass("simple_trees.GenericClassWithTypeParamDependencies")
      val ctor = GenericClassWithTypeParamDependenciesClass.findNonOverloadedDecl(nme.Constructor)
      val List(Right(List(a, b, c, d)), Left(Nil)) = ctor.paramSymss: @unchecked

      assert(clue(a.name) == typeName("A"))

      assert(clue(a.declaredBounds).isNothingAnyBounds)
      assert(clue(b.declaredBounds).isBounds(_.isRef(d), _.isRef(a)))
      assert(clue(c.declaredBounds).isBounds(_.isNothing, _.isRef(b)))
      assert(clue(d.declaredBounds).isNothingAnyBounds)
    }

    locally {
      val AnnotationsClass = ctx.findTopLevelClass("simple_trees.Annotations")
      val renamedParam = AnnotationsClass.findNonOverloadedDecl(termName("renamedParam"))
      val List(Left(List(newName))) = renamedParam.paramSymss: @unchecked

      assert(clue(newName.name) == termName("newName"))

      val annot = newName.getAnnotation(ctx.findTopLevelClass("scala.deprecatedName")).get
      assert(clue(annot.argCount) == 2)
      assert(clue(annot.argIfConstant(0)) == Some(Constant("oldName")))
      assert(clue(annot.argIfConstant(1)) == Some(Constant("forever")))
    }
  }

  testWithContext("paramSymss-scala-2") {
    val ArrayOpsClass = ctx.findTopLevelClass("scala.collection.ArrayOps")
    val CollSeqHeadTailClass = ctx.findStaticModuleClass("scala.collection.package.+:")
    val CollSeqClass = ctx.findTopLevelClass("scala.collection.Seq")
    val CollSeqOpsClass = ctx.findTopLevelClass("scala.collection.SeqOps")
    val ConsClass = ctx.findTopLevelClass("scala.collection.immutable.::")
    val ListClass = ctx.findTopLevelClass("scala.collection.immutable.List")

    val deprecatedNameClass = ctx.findTopLevelClass("scala.deprecatedName")
    val uncheckedVarianceClass = ctx.findTopLevelClass("scala.annotation.unchecked.uncheckedVariance")

    locally {
      val headTailUnapply = CollSeqHeadTailClass.findNonOverloadedDecl(termName("unapply"))
      val List(Right(List(a, cc, c)), Left(List(t))) = headTailUnapply.paramSymss: @unchecked

      assert(clue(a.name) == typeName("A"))
      assert(clue(t.name) == termName("t"))

      extension (tpe: Type)
        def isSeqOpsOf_A_CC_C: Boolean =
          tpe.isApplied(_.isRef(CollSeqOpsClass), List(_.isRef(a), _.isRef(cc), _.isRef(c)))

      assert(clue(a.declaredBounds).isNothingAnyBounds)
      assert(clue(c.declaredBounds).isBounds(_.isNothing, _.isSeqOpsOf_A_CC_C))
      assert(clue(cc.declaredBounds.low).isNothing)

      (cc.declaredBounds.high: @unchecked) match
        case tl: TypeLambda =>
          assert(clue(tl.paramNames.size) == 1)
          val paramRef = tl.paramRefs(0)
          assert(tl.resultType.isApplied(_.isRef(CollSeqClass), List(_.isWildcard)))

      assert(clue(t.declaredType).isIntersectionOf(_.isRef(c), _.isSeqOpsOf_A_CC_C))
    }

    locally {
      val ctor = ConsClass.findNonOverloadedDecl(nme.Constructor)
      val List(Right(List(a)), Left(List(head, next))) = ctor.paramSymss: @unchecked

      assert(clue(a.name) == typeName("A"))
      assert(clue(head.name) == termName("head"))

      assert(clue(a.declaredBounds).isNothingAnyBounds)
      assert(clue(head.declaredType).isRef(a))
      assert(
        clue(next.declaredType)
          .isApplied(_.isRef(ListClass), List(_.isAnnotated(_.isRef(a), _.symbol == uncheckedVarianceClass)))
      )
    }

    locally {
      val find = ArrayOpsClass.findNonOverloadedDecl(termName("find"))
      val List(Left(List(p))) = find.paramSymss: @unchecked

      assert(clue(p.name) == termName("p"))
      assert(
        clue(p.declaredType).isApplied(_.isRef(defn.FunctionNClass(1)), List(_ => true, _.isRef(defn.BooleanClass)))
      )

      val annot = p.getAnnotation(deprecatedNameClass).get
      assert(clue(annot.argIfConstant(0)) == Some(Constant("f")))
      assert(clue(annot.argIfConstant(1)) == Some(Constant("2.13.3")))
      intercept[UnsupportedOperationException](annot.annotConstructor)
    }
  }

  testWithContext("paramSymss-java") {
    val JArrayListClass = ctx.findTopLevelClass("java.util.ArrayList")
    val JCollectionClass = ctx.findTopLevelClass("java.util.Collection")
    val JCollectionsClass = ctx.findTopLevelModuleClass("java.util.Collections")
    val JComparableClass = ctx.findTopLevelClass("java.lang.Comparable")
    val JListClass = ctx.findTopLevelClass("java.util.List")

    // to disambiguate overloads
    def termParamCount(tpe: TypeOrMethodic): Int = tpe match
      case tpe: MethodType => tpe.paramNames.size + termParamCount(tpe.resultType)
      case tpe: PolyType   => termParamCount(tpe.resultType)
      case tpe: Type       => 0

    def firstTermParamType(tpe: TypeOrMethodic): Type = tpe match
      case tpe: MethodType => tpe.paramTypes.head
      case tpe: PolyType   => firstTermParamType(tpe.resultType)
      case tpe: Type       => throw MatchError(tpe)

    locally {
      // static <T> void fill(List<? super T> list, T obj)
      val fill = JCollectionsClass.findNonOverloadedDecl(termName("fill"))
      val List(Right(List(t)), Left(List(list, obj))) = fill.paramSymss: @unchecked

      assert(clue(t.declaredBounds).isJavaNothingAnyBounds)
      assert(clue(obj.declaredType).isRef(t))
      assert(clue(list.declaredType).isApplied(_.isRef(JListClass), List(_.isBounded(_.isRef(t), _.isFromJavaObject))))
    }

    locally {
      // static <T extends Comparable<? super T>> void sort(List<T> list)
      val sort = JCollectionsClass
        .findAllOverloadedDecls(termName("sort"))
        .find(sym => termParamCount(sym.declaredType) == 1)
        .get
      val List(Right(List(t)), Left(List(list))) = sort.paramSymss: @unchecked

      assert(
        clue(t.declaredBounds).isBounds(
          _.isNothing,
          _.isApplied(_.isRef(JComparableClass), List(_.isBounded(_.isRef(t), _.isFromJavaObject)))
        )
      )
      assert(clue(list.declaredType).isApplied(_.isRef(JListClass), List(_.isRef(t))))
    }

    locally {
      // public ArrayList()
      val ctor = JArrayListClass
        .findAllOverloadedDecls(nme.Constructor)
        .find(sym => termParamCount(sym.declaredType) == 0)
        .get
      val List(Right(List(e)), Left(Nil)) = ctor.paramSymss: @unchecked

      assert(clue(e.declaredBounds).isJavaNothingAnyBounds)
    }

    locally {
      // public ArrayList(Collection<? extends E> c)
      val ctor = JArrayListClass
        .findAllOverloadedDecls(nme.Constructor)
        .find(sym =>
          termParamCount(sym.declaredType) == 1 && !firstTermParamType(sym.declaredType).isRef(defn.IntClass)
        )
        .get
      val List(Right(List(e)), Left(List(c))) = ctor.paramSymss: @unchecked

      assert(clue(e.declaredBounds).isJavaNothingAnyBounds)
      assert(clue(c.declaredType).isApplied(_.isRef(JCollectionClass), List(_.isBounded(_.isNothing, _.isRef(e)))))
    }
  }

  testWithContext("recursive-match-types-bounds-as-seen-from-issue-401") {
    val RecursiveMatchTypeSym =
      ctx.findStaticType("simple_trees.RecursiveMatchType$package.RecursiveMatchType").asInstanceOf[TypeMemberSymbol]
    val staticRef = RecursiveMatchTypeSym.staticRef

    /* Here, we only make sure that calls below terminate.
     * More elaborate resolution is tested through `WholeClasspathSuite` over `RecursiveMatchTypeTest`.
     */
    RecursiveMatchTypeSym.boundsAsSeenFrom(staticRef.prefix)
    staticRef.underlying
  }

  testWithContext("sister-classes-with-names-that-look-like-inner-classes-issue-413") {
    // Can find a top-level class that looks like an inner class
    val JavaDefinedEvilClass = ctx.findTopLevelClass("javadefined.JavaDefined$Evil")
    assert(clue(JavaDefinedEvilClass.owner).isPackage)
    assert(clue(JavaDefinedEvilClass.name) == typeName("JavaDefined$Evil"))

    // Cannot confuse an inner class for a top-level class
    intercept[MemberNotFoundException](ctx.findTopLevelClass("javadefined.GenericJavaClass$MyInner"))

    // After that, can still find the real inner class (it wasn't thrown away)
    val GenericJavaClass = ctx.findTopLevelClass("javadefined.GenericJavaClass")
    assert(clue(GenericJavaClass.getDecl(typeName("MyInner"))).exists(_.isClass))
  }

  testWithContext("scala-2-macro-definition") {
    val MacrosClass = ctx.findTopLevelModuleClass("scalatwo.Macros")
    val macroImplAnnotClass = ctx.findTopLevelClass("scala.reflect.macros.internal.macroImpl")

    val foo = MacrosClass.findNonOverloadedDecl(termName("foo"))
    assert(foo.isMacro)

    val annotImplMacro = foo.getAnnotation(macroImplAnnotClass).get
    annotImplMacro.arguments.head match
      case TypeApply(Apply(macroIdent @ Ident(macroName), _), _) =>
        assert(clue(macroName) == nme.m_macro)
        assert(clue(macroIdent.symbol) == defn.scala2MacroInfoFakeMethod)
      case arg =>
        fail("unexpected argument to @macroImpl", clues(arg))
  }

  testWithContext("inlined-path-issue-424") {
    val InlinedPathClass = ctx.findTopLevelClass("simple_trees.InlinedPath")
    val FooClass = ctx.findStaticClass("simple_trees.InlinedPath.Foo")
    val InnerTypeMember = FooClass.findDecl(typeName("Inner"))

    val test = InlinedPathClass.findNonOverloadedDecl(termName("test"))
    val List(Left(List(x)), Left(List(inner))) = test.paramSymss: @unchecked

    assert(clue(x.name) == termName("x"))
    assert(clue(x).isGivenOrUsing)
    assert(clue(x.declaredType).isRef(FooClass))

    assert(clue(inner.name) == termName("inner"))
    inner.declaredType match
      case typeRef: TypeRef =>
        assert(clue(typeRef.prefix).isRef(x)) // through inlining the path
        assert(typeRef.isRef(InnerTypeMember))
      case tpe =>
        fail("unexpected type for inner", clues(tpe))
  }
}
