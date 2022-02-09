import tastyquery.ast.Types.Symbolic
import tastyquery.Contexts.BaseContext
import tastyquery.ast.Symbols.Symbol
import tastyquery.ast.Trees.DefDef
import tastyquery.ast.Trees.Apply
import tastyquery.ast.Types.AppliedType

class TypeSuite extends BaseUnpicklingSuite(withClasses = true, withStdLib = true) {
  import BaseUnpicklingSuite.Decls.*

  def getUnpicklingContext(path: TopLevelDeclPath): BaseContext =
    unpickleCtx(path)

  def assertMissingDeclaration(path: DeclarationPath)(using BaseContext): Unit =
    absent(path)

  def forceAbsentSymbol(path: DeclarationPath)(action: BaseContext ?=> Symbol)(using BaseContext): Symbol = {
    assertMissingDeclaration(path)
    val found = action
    val didForce = resolve(path)
    assert(found eq didForce)
    found
  }

  test("basic-java-class-dependency") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val JavaDefined = name"javadefined" / tname"JavaDefined"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val boxedSym = resolve(BoxedJava / name"boxed")

    val (JavaDefinedRef @ _: Symbolic) = boxedSym.tree.tpe

    forceAbsentSymbol(JavaDefined)(JavaDefinedRef.resolveToSymbol)
  }

  test("select-method-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val getX = name"javadefined" / tname"JavaDefined" / name"getX"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xMethodSym = resolve(BoxedJava / name"xMethod")

    val DefDef(_, _, _, Apply(getXSelection, _), _) = xMethodSym.tree

    val (getXRef @ _: Symbolic) = getXSelection.tpe

    forceAbsentSymbol(getX)(getXRef.resolveToSymbol)
  }

  test("select-field-from-java-class") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val x = name"javadefined" / tname"JavaDefined" / name"x"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val xFieldSym = resolve(BoxedJava / name"xField")

    val DefDef(_, _, _, xSelection, _) = xFieldSym.tree

    val (xRef @ _: Symbolic) = xSelection.tpe

    forceAbsentSymbol(x)(xRef.resolveToSymbol)
  }

  test("basic-scala-2-stdlib-class-dependency") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val :: = name"scala" / name"collection" / name"immutable" / tname"::"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val boxedSym = resolve(BoxedCons / name"boxed")

    val (AppliedType(ConsRef @ _: Symbolic, _)) = boxedSym.tree.tpe

    forceAbsentSymbol(::)(ConsRef.resolveToSymbol)
  }

  test("select-method-from-scala-2-stdlib-class") {
    val BoxedCons = name"scala2compat" / tname"BoxedCons"
    val canEqual = name"scala" / name"collection" / tname"Seq" / name"canEqual"

    given BaseContext = getUnpicklingContext(BoxedCons)

    val fooSym = resolve(BoxedCons / name"foo")

    val DefDef(_, _, _, Apply(canEqualSelection, _), _) = fooSym.tree

    val (canEqualRef @ _: Symbolic) = canEqualSelection.tpe

    forceAbsentSymbol(canEqual)(canEqualRef.resolveToSymbol)
  }

}
