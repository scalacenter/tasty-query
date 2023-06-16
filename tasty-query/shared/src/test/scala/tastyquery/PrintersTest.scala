package tastyquery

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Flags.*
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

    val NullAnyRefBounds = RealTypeBounds(defn.NullType, defn.AnyRefType)

    testShowBasic(NoPrefix, "ε") // U+03F5 Greek Small Letter Epsilon")
    testShowBasic(ctx.findPackage("scala.collection").packageRef, "scala.collection")

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
      "(scala.Product { def foo: ()scala.Int })"
    )

    testShowBasic(defn.ArrayTypeOf(WildcardTypeBounds(defn.NothingAnyBounds)), "scala.Array[?]")
    testShowBasic(
      defn.ArrayTypeOf(WildcardTypeBounds(NullAnyRefBounds)),
      "scala.Array[? >: scala.Null <: scala.AnyRef]"
    )

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
end PrintersTest
