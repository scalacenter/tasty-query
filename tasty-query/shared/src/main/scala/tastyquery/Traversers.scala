package tastyquery

import scala.annotation.tailrec

import tastyquery.Trees.*

object Traversers:
  abstract class TreeTraverser:
    @tailrec
    final def traverse(trees: List[Tree]): Unit =
      trees match
        case head :: tail =>
          traverse(head)
          traverse(tail)
        case Nil =>
          ()
    end traverse

    final def traverse(optTree: Option[Tree]): Unit =
      optTree match
        case Some(tree) => traverse(tree)
        case None       => ()
    end traverse

    def traverse(tree: Tree): Unit = tree match
      // Regular-ish trees
      case PackageDef(pid, stats) =>
        traverse(stats)
      case ImportSelector(imported, renamed, bound) =>
        traverse(imported)
        traverse(renamed)
        traverse(bound)
      case Import(expr, selectors) =>
        traverse(expr)
        traverse(selectors)
      case Export(expr, selectors) =>
        traverse(expr)
        traverse(selectors)
      case ClassDef(name, rhs, symbol) =>
        traverse(rhs)
      case TypeMember(name, rhs, symbol) =>
        traverse(rhs)
      case TypeParam(name, bounds, symbol) =>
        traverse(bounds)
      case Template(constr, parents, self, body) =>
        traverse(constr)
        traverse(parents)
        traverse(self)
        traverse(body)
      case ValDef(name, tpt, rhs, symbol) =>
        traverse(tpt)
        traverse(rhs)
      case SelfDef(name, tpt) =>
        traverse(tpt)
      case DefDef(name, params, tpt, rhs, symbol) =>
        for param <- params do traverse(param.merge)
        traverse(tpt)
        traverse(rhs)
      case Select(qualifier, name) =>
        traverse(qualifier)
      case SelectOuter(qualifier, levels) =>
        traverse(qualifier)
      case Super(qual, mix) =>
        traverse(qual)
      case Apply(fun, args) =>
        traverse(fun)
        traverse(args)
      case TypeApply(fun, args) =>
        traverse(fun)
        traverse(args)
      case New(tpt) =>
        traverse(tpt)
      case Typed(expr, tpt) =>
        traverse(expr)
        traverse(tpt)
      case Assign(lhs, rhs) =>
        traverse(lhs)
        traverse(rhs)
      case NamedArg(name, arg) =>
        traverse(arg)
      case Block(stats, expr) =>
        traverse(stats)
        traverse(expr)
      case If(cond, thenPart, elsePart) =>
        traverse(cond)
        traverse(thenPart)
        traverse(elsePart)
      case InlineIf(cond, thenPart, elsePart) =>
        traverse(cond)
        traverse(thenPart)
        traverse(elsePart)
      case Lambda(meth, tpt) =>
        traverse(meth)
        traverse(tpt)
      case Match(selector, cases) =>
        traverse(selector)
        traverse(cases)
      case CaseDef(pattern, guard, body) =>
        traverse(pattern)
        traverse(guard)
        traverse(body)
      case InlineMatch(selector, cases) =>
        traverse(selector)
        traverse(cases)
      case SeqLiteral(elems, elemtpt) =>
        traverse(elems)
        traverse(elemtpt)
      case While(cond, body) =>
        traverse(cond)
        traverse(body)
      case Throw(expr) =>
        traverse(expr)
      case Try(expr, cases, finalizer) =>
        traverse(expr)
        traverse(cases)
        traverse(finalizer)
      case Return(expr, from) =>
        traverse(expr)
      case Inlined(expr, caller, bindings) =>
        traverse(expr)
        traverse(caller)
        traverse(bindings)
      case Quote(body, bodyType) =>
        traverse(body)
      case Splice(expr, spliceType) =>
        traverse(expr)
      case SplicePattern(pattern, targs, args, spliceType) =>
        traverse(pattern)
        traverse(targs)
        traverse(args)
      case _: ImportIdent | _: Ident | _: This | _: Literal =>
        ()

      // Pattern trees
      case TypeTest(body, tpt) =>
        traverse(body)
        traverse(tpt)
      case Bind(name, body, symbol) =>
        traverse(body)
      case Alternative(trees) =>
        traverse(trees)
      case Unapply(fun, implicits, patterns) =>
        traverse(fun)
        traverse(implicits)
        traverse(patterns)
      case ExprPattern(expr) =>
        traverse(expr)
      case WildcardPattern(tpe) =>
        ()
      case QuotePattern(bindings, body, quotes, patternType) =>
        traverse(bindings)
        body.fold(traverse(_), traverse(_))
        traverse(quotes)

      // TypeTree-ish
      case TypeIdent(tpe) =>
        ()
      case SingletonTypeTree(term) =>
        traverse(term)
      case RefinedTypeTree(parent, refinements, classSym) =>
        traverse(parent)
        traverse(refinements)
      case ByNameTypeTree(result) =>
        traverse(result)
      case AppliedTypeTree(tycon, args) =>
        traverse(tycon)
        traverse(args)
      case TypeWrapper(tp) =>
        ()
      case SelectTypeTree(qualifier, name) =>
        traverse(qualifier)
      case TermRefTypeTree(qualifier, name) =>
        traverse(qualifier)
      case AnnotatedTypeTree(tpt, annotation) =>
        traverse(tpt)
        traverse(annotation)
      case MatchTypeTree(bound, selector, cases) =>
        traverse(bound)
        traverse(selector)
        traverse(cases)
      case TypeCaseDef(pattern, body) =>
        traverse(pattern)
        traverse(body)
      case TypeTreeBind(name, body, symbol) =>
        traverse(body)
      case WildcardTypeArgTree(bounds) =>
        traverse(bounds)
      case TypeLambdaTree(tparams, body) =>
        traverse(tparams)
        traverse(body)
      case TypeBindingsTree(bindings, body) =>
        traverse(bindings)
        traverse(body)
      case InlinedTypeTree(caller, expansion) =>
        traverse(caller)
        traverse(expansion)

      // TypeDefinitionTree's
      case InferredTypeBoundsTree(bounds) =>
        ()
      case ExplicitTypeBoundsTree(low, high) =>
        traverse(low)
        traverse(high)
      case TypeAliasDefinitionTree(alias) =>
        traverse(alias)
      case OpaqueTypeAliasDefinitionTree(bounds, alias) =>
        traverse(bounds)
        traverse(alias)
      case PolyTypeDefinitionTree(tparams, body) =>
        traverse(tparams)
        traverse(body)
      case NamedTypeBoundsTree(name, bounds) =>
        ()
    end traverse
  end TreeTraverser
end Traversers
