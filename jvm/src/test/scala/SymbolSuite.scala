import tastyquery.Contexts
import tastyquery.Contexts.Context

class SymbolSuite extends BaseUnpicklingSuite {
  def getUnpicklingContext(filename: String): Context = {
    val ctx = Contexts.empty
    unpickle(filename) (using ctx)
    ctx
  }
}
