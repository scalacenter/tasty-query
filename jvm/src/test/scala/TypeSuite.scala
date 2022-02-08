import tastyquery.ast.Types.Symbolic
import tastyquery.Contexts.BaseContext
import tastyquery.ast.Symbols.Symbol
import tastyquery.ast.Trees.DefDef
import tastyquery.ast.Trees.Apply

class TypeSuite extends BaseUnpicklingSuite(includeClasses = true) {
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

}
