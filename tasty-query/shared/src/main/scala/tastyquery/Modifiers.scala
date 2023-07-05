package tastyquery

import tastyquery.Symbols.*

object Modifiers:
  enum OpenLevel:
    case Open, Closed, Sealed, Final

  enum Visibility:
    case PrivateThis
    case Private
    case ScopedPrivate(scope: DeclaringSymbol)
    case ProtectedThis
    case Protected
    case ScopedProtected(scope: DeclaringSymbol)
    case Public

  enum TermSymbolKind:
    case Module, Val, LazyVal, Var, Def
end Modifiers
