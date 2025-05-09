package tastyquery

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import tastyquery.TestUtils.*

class PrintersTest extends UnrestrictedUnpicklingSuite:
  testWithContext("TypeMappable.showBasic") {
    def testShowBasic(tp: TypeMappable, expected: String)(using munit.Location): Unit =
      assert(tp.showBasic == expected, clues(tp, tp.showBasic, expected))

    val ProductClass = ctx.findTopLevelClass("scala.Product")
    val Tuple2Class = ctx.findTopLevelClass("scala.Tuple2")

    val ProductType = ProductClass.staticRef

    val NullAnyRefBounds = AbstractTypeBounds(defn.NullType, defn.AnyRefType)

    testShowBasic(NoPrefix, "ε") // U+03F5 Greek Small Letter Epsilon")
    testShowBasic(ctx.findPackage("scala.collection").packageRef, "scala.collection")

    testShowBasic(defn.AnyKindType, "AnyKind")
    testShowBasic(defn.NothingType, "Nothing")
    testShowBasic(defn.SyntacticAnyKindType, "scala.AnyKind")
    testShowBasic(defn.SyntacticNothingType, "scala.Nothing")

    testShowBasic(ctx.findTopLevelClass("scala.Product").staticRef, "scala.Product")
    testShowBasic(ctx.findTopLevelModuleClass("scala.None").staticRef, "scala.None$")
    testShowBasic(ctx.findStaticTerm("scala.None").staticRef, "scala.None.type")
    testShowBasic(
      ctx.findStaticClass("scala.collection.MapOps.WithFilter").staticRef,
      "scala.collection.MapOps.WithFilter"
    )
    testShowBasic(
      ctx.findTopLevelClass("simple_trees.InnerClass").staticRef.select(typeName("Inner")),
      "simple_trees.InnerClass#Inner"
    )

    locally {
      val BlockClass = ctx.findTopLevelClass("simple_trees.Block")
      val xValDef = findLocalValDef(BlockClass.tree.get, termName("a"))
      testShowBasic(TermRef(NoPrefix, xValDef), "a.type")
    }

    testShowBasic(defn.SeqClass.thisType, "Seq.this.type")
    testShowBasic(
      ctx.findTopLevelClass("simple_trees.InnerClass").thisType.select(typeName("Inner")),
      "InnerClass.this.Inner"
    )

    testShowBasic(SuperType(defn.SeqClass.thisType, None), "Seq.super.type")
    testShowBasic(SuperType(defn.SeqClass.thisType, Some(defn.ObjectType)), "Seq.super[java.lang.Object].type")

    testShowBasic(ConstantType(Constant(())), "()")
    testShowBasic(ConstantType(Constant(true)), "true")
    testShowBasic(ConstantType(Constant(5.toByte)), "5b")
    testShowBasic(ConstantType(Constant(5.toShort)), "5s")
    testShowBasic(ConstantType(Constant('A')), "'A'")
    testShowBasic(ConstantType(Constant('\n')), "'\\n'")
    testShowBasic(ConstantType(Constant(5)), "5")
    testShowBasic(ConstantType(Constant(5L)), "5L")
    testShowBasic(ConstantType(Constant(5.5f)), "5.5f")
    testShowBasic(ConstantType(Constant(5.5)), "5.5")
    testShowBasic(ConstantType(Constant("foo")), "\"foo\"")
    testShowBasic(ConstantType(Constant("foo\nbar \"baz \u001f ε")), "\"foo\\nbar \\\"baz \\u001f \\u03b5\"")
    testShowBasic(ConstantType(Constant(null)), "null")
    testShowBasic(ConstantType(Constant(defn.IntType)), "classOf[scala.Int]")

    testShowBasic(defn.SeqTypeOf(defn.IntType), "scala.collection.immutable.Seq[scala.Int]")
    testShowBasic(ByNameType(defn.IntType), "=> scala.Int")
    testShowBasic(RepeatedType(defn.IntType), "scala.Int*")

    testShowBasic(
      TypeLambda(List(typeName("A"), typeName("B")))(
        _ => List(defn.NothingAnyBounds, NullAnyRefBounds),
        tl => AppliedType(Tuple2Class.staticRef, tl.paramRefs)
      ),
      "([A, B >: scala.Null <: scala.AnyRef] =>> scala.Tuple2[A, B])"
    )

    testShowBasic(TypeRefinement(ProductType, typeName("Foo"), defn.NothingAnyBounds), "(scala.Product { type Foo })")
    testShowBasic(
      TypeRefinement(ProductType, typeName("Foo"), NullAnyRefBounds),
      "(scala.Product { type Foo >: scala.Null <: scala.AnyRef })"
    )

    testShowBasic(
      TermRefinement(ProductType, isStable = true, termName("foo"), defn.IntType),
      "(scala.Product { val foo: scala.Int })"
    )
    testShowBasic(
      TermRefinement(ProductType, isStable = false, termName("foo"), defn.IntType),
      "(scala.Product { def foo: scala.Int })"
    )
    testShowBasic(
      TermRefinement(ProductType, isStable = false, termName("foo"), MethodType(Nil, Nil, defn.IntType)),
      "(scala.Product { def foo()scala.Int })"
    )
    testShowBasic(
      TermRefinement(
        ProductType,
        isStable = false,
        termName("foo"),
        MethodType(List(termName("x")), List(defn.IntType), defn.IntType)
      ),
      "(scala.Product { def foo(x: scala.Int)scala.Int })"
    )
    testShowBasic(
      TermRefinement(
        ProductType,
        isStable = false,
        termName("foo"),
        ImplicitMethodType(List(termName("x")), List(defn.IntType), defn.IntType)
      ),
      "(scala.Product { def foo(implicit x: scala.Int)scala.Int })"
    )
    testShowBasic(
      TermRefinement(
        ProductType,
        isStable = false,
        termName("foo"),
        ContextualMethodType(List(termName("x")), List(defn.IntType), defn.IntType)
      ),
      "(scala.Product { def foo(using x: scala.Int)scala.Int })"
    )

    testShowBasic(defn.ArrayTypeOf(WildcardTypeArg(defn.NothingAnyBounds)), "scala.Array[?]")
    testShowBasic(defn.ArrayTypeOf(WildcardTypeArg(NullAnyRefBounds)), "scala.Array[? >: scala.Null <: scala.AnyRef]")

    testShowBasic(
      PolyType(List(typeName("A")))(
        _ => List(NullAnyRefBounds),
        pt =>
          MethodType(List(termName("x"), termName("y")))(
            _ => List(defn.StringType, pt.paramRefs(0)),
            mt => mt.paramRefs(0)
          )
      ),
      "[A >: scala.Null <: scala.AnyRef](x: java.lang.String, y: A)x.type"
    )
  }

  testWithContext("tree printers") {
    def testShowBasic(tree: Tree, expected: String)(using munit.Location): Unit =
      assert(clue(tree.showBasic) == clue(expected))

    def testShowBasicMember(cls: ClassSymbol, memberName: Name, expected: String)(using munit.Location): Unit =
      val member = memberName match
        case memberName: UnsignedTermName => cls.findNonOverloadedDecl(memberName)
        case _                            => cls.findMember(memberName)
      testShowBasic(member.tree.get, expected)

    val ConstantsClass = ctx.findTopLevelClass("simple_trees.Constants")
    testShowBasicMember(ConstantsClass, termName("unitVal"), "val unitVal: scala.Unit = ()")
    testShowBasicMember(ConstantsClass, termName("falseVal"), "val falseVal: scala.Boolean = false")
    testShowBasicMember(ConstantsClass, termName("byteVal"), "val byteVal: Byte = 1b")
    testShowBasicMember(ConstantsClass, termName("shortVal"), "val shortVal: Short = 1s")
    testShowBasicMember(ConstantsClass, termName("charVal"), "val charVal: scala.Char = 'a'")
    testShowBasicMember(ConstantsClass, termName("intVal"), "val intVal: scala.Int = 1")
    testShowBasicMember(ConstantsClass, termName("longVal"), "val longVal: Long = 1L")
    testShowBasicMember(ConstantsClass, termName("floatVal"), "val floatVal: Float = 1.5f")
    testShowBasicMember(ConstantsClass, termName("doubleVal"), "val doubleVal: Double = 1.1")
    testShowBasicMember(ConstantsClass, termName("stringVal"), "val stringVal: java.lang.String = \"string\"")
    testShowBasicMember(ConstantsClass, termName("nullVal"), "val nullVal: scala.Null = null")

    val GenericClassWithNestedGenericClass = ctx.findTopLevelClass("simple_trees.GenericClassWithNestedGeneric")
    testShowBasic(
      GenericClassWithNestedGenericClass.tree.get,
      "class GenericClassWithNestedGeneric[T] extends java.lang.Object() {"
        + " def <init>[T](): scala.Unit; "
        + "class NestedGeneric[U] extends java.lang.Object() { def <init>[U](): scala.Unit } }"
    )

    val PatternMatchingOnCaseClassClass = ctx.findTopLevelClass("simple_trees.PatternMatchingOnCaseClass")
    testShowBasicMember(
      PatternMatchingOnCaseClassClass,
      termName("caseMatching"),
      "def caseMatching(c: AbstractForCaseClasses): Int = (c match { "
        + "case FirstCase(x @ _): simple_trees.FirstCase =>  { (x: scala.Int) }; "
        + "case SecondCase(y @ _): simple_trees.SecondCase =>  { (y: scala.Int) }; "
        + "case _ =>  { 0 } })"
    )

    val ClassWithSelfClass = ctx.findTopLevelClass("simple_trees.ClassWithSelf")
    testShowBasic(
      ClassWithSelfClass.tree.get,
      "class ClassWithSelf extends java.lang.Object() with TraitWithSelf { "
        + "self: simple_trees.ClassWithSelf =>; def <init>(): scala.Unit }"
    )

    val DoublePolyExtensionsClass = ctx.findTopLevelClass("simple_trees.DoublePolyExtensions")
    testShowBasicMember(
      DoublePolyExtensionsClass,
      termName("+++:"),
      "def +++:[A][B >: A](x: B)(list: List[A]): List[B] = list.::[B](x)"
    )

    val HigherKindedClass = ctx.findTopLevelClass("simple_trees.HigherKinded")
    testShowBasic(
      HigherKindedClass.tree.get,
      "trait HigherKinded[A <: ([_$1] =>> scala.Any)] extends java.lang.Object { "
        + "def <init>[A[_$1]](): scala.Unit; "
        + "def m[T](x: A[T]): A[T]; "
        + "def f[B[_$2], T](x: B[T]): B[T] }"
    )

    val MatchTypeClass = ctx.findTopLevelClass("simple_trees.MatchType")
    testShowBasicMember(
      MatchTypeClass,
      typeName("MT"),
      "type MT[X] <: scala.Predef.String = X match { case Int => String }"
    )
    testShowBasicMember(
      MatchTypeClass,
      typeName("MTWithBound"),
      "type MTWithBound[X] <: Product = X match { case Int => Some[Int] }"
    )
    testShowBasicMember(
      MatchTypeClass,
      typeName("MTWithWildcard"),
      "type MTWithWildcard[X] <: scala.Int = X match { case _ => Int }"
    )
    testShowBasicMember(
      MatchTypeClass,
      typeName("MTWithBind"),
      "type MTWithBind[X] = X match { case List[t] => t }"
    )
  }

  testWithContext("multiline tree printers") {
    def testShowMultiline(tree: Tree, expected: String)(using munit.Location): Unit =
      assert(clue(tree.showMultiline) == clue(expected))

    def testShowMultilineMember(cls: ClassSymbol, memberName: Name, expected: String)(using munit.Location): Unit =
      val member = memberName match
        case memberName: UnsignedTermName => cls.findNonOverloadedDecl(memberName)
        case _                            => cls.findMember(memberName)
      testShowMultiline(member.tree.get, expected)

    val GenericClassWithNestedGenericClass = ctx.findTopLevelClass("simple_trees.GenericClassWithNestedGeneric")
    testShowMultiline(
      GenericClassWithNestedGenericClass.tree.get,
      """class GenericClassWithNestedGeneric[T] extends java.lang.Object() {
        |  def <init>[T](): scala.Unit
        |  class NestedGeneric[U] extends java.lang.Object() {
        |    def <init>[U](): scala.Unit
        |  }
        |}""".stripMargin
    )

    val PatternMatchingOnCaseClassClass = ctx.findTopLevelClass("simple_trees.PatternMatchingOnCaseClass")
    testShowMultilineMember(
      PatternMatchingOnCaseClassClass,
      termName("caseMatching"),
      """def caseMatching(c: AbstractForCaseClasses): Int = (c match {
        |  case FirstCase(x @ _): simple_trees.FirstCase =>  {
        |    (x: scala.Int)
        |  }
        |  case SecondCase(y @ _): simple_trees.SecondCase =>  {
        |    (y: scala.Int)
        |  }
        |  case _ =>  {
        |    0
        |  }
        |})""".stripMargin
    )

    val ClassWithSelfClass = ctx.findTopLevelClass("simple_trees.ClassWithSelf")
    testShowMultiline(
      ClassWithSelfClass.tree.get,
      """class ClassWithSelf extends java.lang.Object() with TraitWithSelf {
        |  self: simple_trees.ClassWithSelf =>
        |  def <init>(): scala.Unit
        |}""".stripMargin
    )

    val HigherKindedClass = ctx.findTopLevelClass("simple_trees.HigherKinded")
    testShowMultiline(
      HigherKindedClass.tree.get,
      """trait HigherKinded[A <: ([_$1] =>> scala.Any)] extends java.lang.Object {
        |  def <init>[A[_$1]](): scala.Unit
        |  def m[T](x: A[T]): A[T]
        |  def f[B[_$2], T](x: B[T]): B[T]
        |}""".stripMargin
    )

    val MatchTypeClass = ctx.findTopLevelClass("simple_trees.MatchType")
    testShowMultilineMember(
      MatchTypeClass,
      typeName("MT"),
      """type MT[X] <: scala.Predef.String = X match {
        |  case Int => String
        |}""".stripMargin
    )
    testShowMultilineMember(
      MatchTypeClass,
      typeName("MTWithBound"),
      """type MTWithBound[X] <: Product = X match {
        |  case Int => Some[Int]
        |}""".stripMargin
    )
    testShowMultilineMember(
      MatchTypeClass,
      typeName("MTWithWildcard"),
      """type MTWithWildcard[X] <: scala.Int = X match {
        |  case _ => Int
        |}""".stripMargin
    )
    testShowMultilineMember(
      MatchTypeClass,
      typeName("MTWithBind"),
      """type MTWithBind[X] = X match {
        |  case List[t] => t
        |}""".stripMargin
    )
  }
end PrintersTest
