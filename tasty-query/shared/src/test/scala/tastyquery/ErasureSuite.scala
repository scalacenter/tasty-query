package tastyquery

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

class ErasureSuite extends UnrestrictedUnpicklingSuite:
  import ErasedTypeRef.*

  private def assertErasure(tpe: Type, sourceLangage: SourceLanguage, expected: ErasedTypeRef)(
    using Context,
    munit.Location
  ): Unit =
    assert(clue(ErasedTypeRef.erase(tpe, sourceLangage)) == clue(expected), clues(tpe.showBasic, sourceLangage))
  end assertErasure

  testWithContext("array-intersection") {
    val ArrayOfStringType = defn.ArrayTypeOf(defn.StringType)
    val ArrayOfStringRef = ArrayTypeRef(ClassRef(defn.StringClass), 1)

    for language <- SourceLanguage.values do
      assertErasure(
        AndType(AndType(ArrayOfStringType, ArrayOfStringType), ArrayOfStringType),
        language,
        ArrayOfStringRef
      )
      assertErasure(
        AndType(ArrayOfStringType, AndType(ArrayOfStringType, ArrayOfStringType)),
        language,
        ArrayOfStringRef
      )
  }
end ErasureSuite
