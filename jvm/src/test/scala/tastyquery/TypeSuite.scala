package tastyquery

import tastyquery.Contexts.BaseContext
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.*
import tastyquery.ast.Types.*

class TypeSuite extends BaseUnpicklingSuite(withClasses = true, withStdLib = true) {
  import BaseUnpicklingSuite.Decls.*

  def assertMissingDeclaration(path: DeclarationPath)(using BaseContext): Unit =
    absent(path)

  def forceAbsentSymbol(path: DeclarationPath)(action: BaseContext ?=> Symbol)(using BaseContext): Symbol = {
    assertMissingDeclaration(path)
    val found = action
    val didForce = resolve(path)
    assert(found eq didForce)
    found
  }

  test("basic-local-val") {
    val AssignPath = name"simple_trees" / tname"Assign"

    given BaseContext = getUnpicklingContext(AssignPath)

    val fSym = resolve(AssignPath / name"f")
    val fTree = fSym.tree.asInstanceOf[DefDef]

    val List(List(xParamDef: ValDef)) = fTree.params: @unchecked

    // HACK: Get scala.Int to load
    xParamDef.tpe.asInstanceOf[Symbolic].resolveToSymbol

    val IntClass = resolve(name"scala" / tname"Int")
    assert(xParamDef.tpe.isRef(IntClass))

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
    val fTree = fSym.tree.asInstanceOf[DefDef]

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
    val fTree = fSym.tree.asInstanceOf[DefDef]

    val List(List(xParamDef: ValDef)) = fTree.params: @unchecked

    // HACK: Get scala.Int to load
    xParamDef.tpe.asInstanceOf[Symbolic].resolveToSymbol

    val IntClass = resolve(name"scala" / tname"Int")
    assert(xParamDef.tpe.isRef(IntClass))

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

  test("return-ident") {
    val ReturnPath = name"simple_trees" / tname"Return"

    given BaseContext = getUnpicklingContext(ReturnPath)

    val withReturnSym = resolve(ReturnPath / name"withReturn")
    val withReturnTree = withReturnSym.tree.asInstanceOf[DefDef]

    var returnCount = 0

    withReturnTree.walkTree { tree =>
      tree match {
        case Return(expr, from: Ident) =>
          returnCount += 1
          assert(from.tpe.isRef(withReturnSym), clue(from.tpe))
        case _ =>
          ()
      }
    }

    assert(returnCount == 1, clue(returnCount))
  }

  test("basic-java-class-dependency") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val JavaDefined = name"javadefined" / tname"JavaDefined"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val boxedSym = resolve(BoxedJava / name"boxed")

    val (JavaDefinedRef @ _: Symbolic) = boxedSym.tree.tpe: @unchecked

    forceAbsentSymbol(JavaDefined)(JavaDefinedRef.resolveToSymbol)
  }

  test("select-method-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val getX = name"javadefined" / tname"JavaDefined" / name"getX"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xMethodSym = resolve(BoxedJava / name"xMethod")

    val DefDef(_, _, _, Apply(getXSelection, _), _) = xMethodSym.tree: @unchecked

    val (getXRef @ _: Symbolic) = getXSelection.tpe: @unchecked

    forceAbsentSymbol(getX)(getXRef.resolveToSymbol)
  }

  test("select-field-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val x = name"javadefined" / tname"JavaDefined" / name"x"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xFieldSym = resolve(BoxedJava / name"xField")

    val DefDef(_, _, _, xSelection, _) = xFieldSym.tree: @unchecked

    val (xRef @ _: Symbolic) = xSelection.tpe: @unchecked

    forceAbsentSymbol(x)(xRef.resolveToSymbol)
  }

  test("basic-scala-2-stdlib-class-dependency") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val :: = name"scala" / name"collection" / name"immutable" / tname"::"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val boxedSym = resolve(BoxedCons / name"boxed")

    val (AppliedType(ConsRef @ _: Symbolic, _)) = boxedSym.tree.tpe: @unchecked

    forceAbsentSymbol(::)(ConsRef.resolveToSymbol)
  }

  test("select-method-from-scala-2-stdlib-class") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val canEqual = name"scala" / name"collection" / tname"Seq" / name"canEqual"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val fooSym = resolve(BoxedCons / name"foo")

    val DefDef(_, _, _, Apply(canEqualSelection, _), _) = fooSym.tree: @unchecked

    val (canEqualRef @ _: Symbolic) = canEqualSelection.tpe: @unchecked

    forceAbsentSymbol(canEqual)(canEqualRef.resolveToSymbol)
  }

  test("select-field-from-tasty-in-other-package:dependency-from-class-file") {
    val BoxedConstants = name"crosspackagetasty" / tname"BoxedConstants"
    val unitVal = name"simple_trees" / tname"Constants" / name"unitVal"

    given BaseContext = getUnpicklingContext(BoxedConstants)

    val boxedUnitValSym = resolve(BoxedConstants / name"boxedUnitVal")

    val DefDef(_, _, _, unitValSelection, _) = boxedUnitValSym.tree: @unchecked

    val (unitValRef @ _: Symbolic) = unitValSelection.tpe: @unchecked

    forceAbsentSymbol(unitVal)(unitValRef.resolveToSymbol)
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

    val DefDef(_, _, _, Apply(getXSelection, _), _) = xMethodSym.tree: @unchecked

    val (getXRef @ _: Symbolic) = getXSelection.tpe: @unchecked

    forceAbsentSymbol(getX)(getXRef.resolveToSymbol)
  }

}
