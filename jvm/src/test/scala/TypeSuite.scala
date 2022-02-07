import tastyquery.ast.Types.Symbolic
import tastyquery.Contexts.BaseContext
import tastyquery.ast.Symbols.Symbol

class TypeSuite extends BaseUnpicklingSuite(includeClasses = true) {
  import BaseUnpicklingSuite.Decls.*

  def getUnpicklingContext(path: TopLevelDeclPath): BaseContext =
    unpickleCtx(path)

  def assertMissingDeclaration(path: DeclarationPath)(using BaseContext): Unit =
    absent(path)

  def forceAbsentSymbol(path: DeclarationPath)(action: BaseContext ?=> Symbol)(using BaseContext): Symbol =
    assertMissingDeclaration(path)
    val found = action
    val didForce = resolve(path)
    assert(found eq didForce)
    found

  test("basic-java-class-dependency") {
    val BoxedJava = name"javacompat" / tname"BoxedJava"
    val JavaDefined = name"javadefined" / tname"JavaDefined"

    given BaseContext = getUnpicklingContext(BoxedJava)

    val boxedSym = resolve(BoxedJava / name"boxed")

    val (JavaDefinedRef @ _: Symbolic) = boxedSym.tree.tpe

    forceAbsentSymbol(JavaDefined)(JavaDefinedRef.resolveToSymbol)
  }

}
