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

  enum Variance(private[tastyquery] val sign: Int):
    case Invariant extends Variance(0)
    case Covariant extends Variance(1)
    case Contravariant extends Variance(-1)

    private[tastyquery] def *(that: Variance): Variance =
      (this.sign * that.sign) match
        case 0  => Invariant
        case 1  => Covariant
        case -1 => Contravariant
    end *
  end Variance
end Modifiers
