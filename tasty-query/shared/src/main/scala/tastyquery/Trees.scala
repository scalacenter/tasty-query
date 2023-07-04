package tastyquery

import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Spans.*
import tastyquery.Symbols.*
import tastyquery.Types.*

object Trees {

  sealed abstract class Tree(val span: Span) {
    def withSpan(span: Span): Tree

    private def subtrees: List[Tree] = this match {
      case PackageDef(pid, stats)                   => stats
      case ImportSelector(imported, renamed, bound) => imported :: renamed.toList ::: bound.toList
      case Import(expr, selectors)                  => expr :: selectors
      case Export(expr, selectors)                  => expr :: selectors
      case ClassDef(name, rhs, symbol)              => rhs :: Nil
      case TypeMember(name, rhs, symbol)            => rhs :: Nil
      case TypeParam(name, bounds, symbol)          => bounds :: Nil
      case Template(constr, parents, self, body)    => constr :: parents ::: self.toList ::: body
      case ValDef(name, tpt, rhs, symbol)           => tpt :: rhs.toList
      case SelfDef(name, tpt)                       => tpt :: Nil
      case DefDef(name, params, tpt, rhs, symbol)   => params.flatMap(_.merge) ::: tpt :: rhs.toList
      case Select(qualifier, name)                  => qualifier :: Nil
      case SelectOuter(qualifier, levels)           => qualifier :: Nil
      case Super(qual, mix)                         => qual :: Nil
      case Apply(fun, args)                         => fun :: args
      case TypeApply(fun, args)                     => fun :: args
      case New(tpt)                                 => tpt :: Nil
      case Typed(expr, tpt)                         => expr :: tpt :: Nil
      case Assign(lhs, rhs)                         => lhs :: rhs :: Nil
      case NamedArg(name, arg)                      => arg :: Nil
      case Block(stats, expr)                       => stats :+ expr
      case If(cond, thenPart, elsePart)             => cond :: thenPart :: elsePart :: Nil
      case InlineIf(cond, thenPart, elsePart)       => cond :: thenPart :: elsePart :: Nil
      case Lambda(meth, tpt)                        => meth :: tpt.toList
      case Match(selector, cases)                   => selector :: cases
      case InlineMatch(selector, cases)             => selector.toList ::: cases
      case CaseDef(pattern, guard, body)            => pattern :: guard.toList ::: body :: Nil
      case TypeTest(body, tpt)                      => body :: tpt :: Nil
      case Bind(name, body, symbol)                 => body :: Nil
      case Alternative(trees)                       => trees
      case Unapply(fun, implicits, patterns)        => fun :: implicits ++ patterns
      case ExprPattern(expr)                        => expr :: Nil
      case SeqLiteral(elems, elemtpt)               => elems ::: elemtpt :: Nil
      case While(cond, body)                        => cond :: body :: Nil
      case Throw(expr)                              => expr :: Nil
      case Try(expr, cases, finalizer)              => (expr :: cases) ::: finalizer.toList
      case Return(expr, from)                       => expr.toList
      case Inlined(expr, caller, bindings)          => expr :: bindings

      case SingletonTypeTree(term)                        => term :: Nil
      case RefinedTypeTree(parent, refinements, classSym) => parent :: refinements
      case ByNameTypeTree(result)                         => result :: Nil
      case AppliedTypeTree(tycon, args)                   => tycon :: args
      case TypeWrapper(tp)                                => Nil
      case SelectTypeTree(qualifier, name)                => qualifier :: Nil
      case TermRefTypeTree(qualifier, name)               => qualifier :: Nil
      case AnnotatedTypeTree(tpt, annotation)             => tpt :: annotation :: Nil
      case MatchTypeTree(bound, selector, cases)          => bound.toList ::: selector :: cases
      case TypeCaseDef(pattern, body)                     => pattern :: body :: Nil
      case TypeTreeBind(name, body, symbol)               => body :: Nil
      case WildcardTypeArgTree(bounds)                    => bounds :: Nil
      case TypeLambdaTree(tparams, body)                  => tparams ::: body :: Nil
      case TypeBindingsTree(bindings, body)               => bindings ::: body :: Nil

      case InferredTypeBoundsTree(bounds)               => Nil
      case ExplicitTypeBoundsTree(low, high)            => low :: high :: Nil
      case TypeAliasDefinitionTree(alias)               => alias :: Nil
      case OpaqueTypeAliasDefinitionTree(bounds, alias) => bounds :: alias :: Nil
      case PolyTypeDefinitionTree(tparams, body)        => tparams ::: body :: Nil
      case NamedTypeBoundsTree(name, bounds)            => Nil

      case _: ImportIdent | _: Ident | _: This | _: Literal | _: WildcardPattern | _: TypeIdent => Nil
    }

    def walkTree[R](op: Tree => R)(reduce: (R, R) => R, default: => R): R = {
      // Apply the operation to the tree itself and all its sutbrees. Reduce the result with the given @reduce function
      def rec(t: Tree): R = reduce(op(t), t.subtrees.map(rec).foldLeft(default)(reduce))
      rec(this)
    }

    /* If the operation does not produce a result, simply apply it to all subtrees of the tree */
    def walkTree(op: Tree => Unit): Unit = walkTree[Unit](op)((_, _) => (), ())
  }

  sealed abstract class TopLevelTree(span: Span) extends Tree(span):
    def withSpan(span: Span): TopLevelTree
  end TopLevelTree

  sealed abstract class StatementTree(span: Span) extends TopLevelTree(span):
    def withSpan(span: Span): StatementTree
  end StatementTree

  sealed abstract class TermTree(span: Span) extends StatementTree(span):
    private var myType: TermType | Null = null

    def withSpan(span: Span): TermTree

    /** Compute the actual term of this tree. */
    protected def calculateType(using Context): TermType

    /** The term type of this tree. */
    final def tpe(using Context): TermType = {
      val local = myType
      if local != null then local
      else
        val computed = calculateType
        myType = computed
        computed
    }
  end TermTree

  sealed trait DefTree extends Tree:
    val symbol: Symbol
  end DefTree

  final case class PackageDef(pid: PackageSymbol, stats: List[TopLevelTree])(span: Span) extends TopLevelTree(span) {
    override final def withSpan(span: Span): PackageDef = PackageDef(pid, stats)(span)
  }

  /** An identifier appearing in an `import` clause; it has no type. */
  final case class ImportIdent(name: TermName)(span: Span) extends Tree(span) {
    override final def withSpan(span: Span): ImportIdent = ImportIdent(name)(span)
  }

  final case class ImportSelector(imported: ImportIdent, renamed: Option[ImportIdent], bound: Option[TypeTree])(
    span: Span
  ) extends Tree(span) {

    /** It's a `given` selector */
    val isGiven: Boolean = imported.name.isEmpty

    /** It's a `given` or `_` selector */
    val isWildcard: Boolean = isGiven || imported.name == nme.Wildcard

    /** The imported name, EmptyTermName if it's a given selector */
    val name: TermName = imported.name

    /** The renamed part (which might be `_`), if present, or `name`, if missing */
    val rename: TermName = renamed match {
      case Some(ImportIdent(rename)) => rename
      case None                      => name
    }

    override final def withSpan(span: Span): ImportSelector = ImportSelector(imported, renamed, bound)(span)
  }

  final case class Import(expr: TermTree, selectors: List[ImportSelector])(span: Span) extends StatementTree(span) {
    override final def withSpan(span: Span): Import = Import(expr, selectors)(span)
  }

  /** import expr.selectors */
  final case class Export(expr: TermTree, selectors: List[ImportSelector])(span: Span) extends StatementTree(span) {
    override final def withSpan(span: Span): Export = Export(expr, selectors)(span)
  }

  /** mods class name template     or
    *  mods trait name template     or
    *  mods type name = rhs   or
    *  mods type name >: lo <: hi,          if rhs = TypeBoundsTree(lo, hi)      or
    *  mods type name >: lo <: hi = rhs     if rhs = TypeBoundsTree(lo, hi, alias) and opaque in mods
    */
  sealed abstract class TypeDef(name: TypeName)(span: Span) extends StatementTree(span) with DefTree:
    val symbol: TypeSymbol
  end TypeDef

  final case class ClassDef(name: TypeName, rhs: Template, symbol: ClassSymbol)(span: Span)
      extends TypeDef(name)(span) {
    override final def withSpan(span: Span): ClassDef = ClassDef(name, rhs, symbol)(span)
  }

  /** A type member has a type tree rhs if the member is defined by the user, or typebounds if it's synthetic */
  final case class TypeMember(name: TypeName, rhs: TypeDefinitionTree, symbol: TypeMemberSymbol)(span: Span)
      extends TypeDef(name)(span) {
    override final def withSpan(span: Span): TypeMember = TypeMember(name, rhs, symbol)(span)
  }

  /** The bounds are a type tree if the method is defined by the user and bounds-only if it's synthetic */
  final case class TypeParam(name: TypeName, bounds: TypeDefinitionTree, symbol: TypeParamSymbol)(span: Span)
      extends TypeDef(name)(span) {
    override final def withSpan(span: Span): TypeParam = TypeParam(name, bounds, symbol)(span)
  }

  /** `constr extends parents { self => body }`
    *
    * holder for details of a Class definition
    *
    * @param classParent -- the parent whose constructor is called.
    *                       If the template defines a class, this is its only class parent.
    * @param parents        trait parents of the template and the class parent if the template defines a trait.
    */
  final case class Template(
    constr: DefDef,
    parents: List[Apply | Block | TypeTree],
    self: Option[SelfDef],
    body: List[StatementTree]
  )(span: Span)
      extends Tree(span) {
    override final def withSpan(span: Span): Template = Template(constr, parents, self, body)(span)
  }

  sealed abstract class ValOrDefDef()(span: Span) extends StatementTree(span) with DefTree:
    val name: TermName

    val symbol: TermSymbol

    def withSpan(span: Span): ValOrDefDef
  end ValOrDefDef

  /** mods val name: tpt = rhs */
  final case class ValDef(name: TermName, tpt: TypeTree, rhs: Option[TermTree], symbol: TermSymbol)(span: Span)
      extends ValOrDefDef()(span) {
    override final def withSpan(span: Span): ValDef = ValDef(name, tpt, rhs, symbol)(span)
  }

  /** Self type definition `name: tpt =>`. */
  final case class SelfDef(name: TermName, tpt: TypeTree)(span: Span) extends Tree(span):
    override def withSpan(span: Span): SelfDef = SelfDef(name, tpt)(span)
  end SelfDef

  type ParamsClause = Either[List[ValDef], List[TypeParam]]

  private[tastyquery] object ParamsClause:
    def makeDefDefType(paramLists: List[ParamsClause], resultTpt: TypeTree)(using Context): TypeOrMethodic =
      def rec(paramLists: List[ParamsClause]): TypeOrMethodic =
        paramLists match
          case Left(params) :: rest =>
            val paramSymbols = params.map(_.symbol)
            MethodType.fromSymbols(paramSymbols, rec(rest))
          case Right(tparams) :: rest =>
            PolyType.fromParams(tparams, rec(rest))
          case Nil =>
            resultTpt.toType

      rec(paramLists)
    end makeDefDefType
  end ParamsClause

  /** mods def name[tparams](vparams_1)...(vparams_n): tpt = rhs */
  final case class DefDef(
    name: TermName,
    paramLists: List[ParamsClause],
    resultTpt: TypeTree,
    rhs: Option[TermTree],
    symbol: TermSymbol
  )(span: Span)
      extends ValOrDefDef()(span) {
    override final def withSpan(span: Span): DefDef = DefDef(name, paramLists, resultTpt, rhs, symbol)(span)
  }

  // --- TermTrees and PatternTrees -------------------------------------------

  /** name */
  final case class Ident(name: TermName)(tpe: TermRef | PackageRef)(span: Span) extends TermTree(span):
    protected final def calculateType(using Context): TermType = tpe

    def symbol(using Context): TermSymbol | PackageSymbol = tpe match
      case termRef: TermRef =>
        termRef.optSymbol.getOrElse {
          throw InvalidProgramStructureException(s"$this with type $tpe does not have a symbol")
        }
      case packageRef: PackageRef => packageRef.symbol
    end symbol

    override final def withSpan(span: Span): Ident = Ident(name)(tpe)(span)
  end Ident

  /** qualifier.termName */
  final case class Select(qualifier: TermTree, name: TermName)(selectOwner: Option[TypeRef])(span: Span)
      extends TermTree(span):
    require(
      selectOwner.isEmpty || name.isInstanceOf[SignedName],
      s"illegal section of unsigned name '$name' in owner ${selectOwner.get}"
    )

    protected final def calculateType(using Context): TermRef | PackageRef =
      val prefix = qualifier.tpe match
        case prefix: NonEmptyPrefix => prefix
        case qualType =>
          throw InvalidProgramStructureException(s"Invalid selection from $qualifier with type $qualType")
      selectOwner match
        case Some(selOwner) => TermRef(prefix, LookupIn(selOwner, name.asInstanceOf[SignedName]))
        case None           => NamedType.possibleSelFromPackage(prefix, name)

    def symbol(using Context): TermSymbol | PackageSymbol = tpe match
      case termRef: TermRef =>
        termRef.optSymbol.getOrElse {
          throw InvalidProgramStructureException(s"$this with type $tpe does not have a symbol")
        }
      case packageRef: PackageRef => packageRef.symbol
      case tpe                    => throw AssertionError(s"unexpected type $tpe in Select node")
    end symbol

    override def withSpan(span: Span): Select = Select(qualifier, name)(selectOwner)(span)
  end Select

  /** Synthetic outer selection */
  final case class SelectOuter(qualifier: TermTree, levels: Int)(tpe: Type)(span: Span) extends TermTree(span):
    protected final def calculateType(using Context): TermType = tpe

    override def withSpan(span: Span): SelectOuter = SelectOuter(qualifier, levels)(tpe)(span)
  end SelectOuter

  /** `qual.this` */
  final case class This(qualifier: TypeIdent)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      qualifier.toPrefix match
        case pkg: PackageRef => pkg
        case tref: TypeRef   => ThisType(tref)
        case qualTpe =>
          throw InvalidProgramStructureException(s"Unexpected type for This qualifier $qualifier: $qualTpe")
    end calculateType

    override final def withSpan(span: Span): This = This(qualifier)(span)
  }

  /** C.super[mix], where qual = C.this */
  final case class Super(qual: TermTree, mix: Option[TypeIdent])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      val thistpe = qual.tpe match
        case qualTpe: ThisType =>
          qualTpe.cls.thisType // is this ever different than `qualTpe`?
        case qualTpe =>
          throw InvalidProgramStructureException(s"Unexpected type for Super qualifier $qual: $qualTpe")
      val supertpe = mix.map(_.toType)
      SuperType(thistpe, supertpe)
    end calculateType

    override final def withSpan(span: Span): Super = Super(qual, mix)(span)
  }

  /** fun(args) */
  final case class Apply(fun: TermTree, args: List[TermTree])(span: Span) extends TermTree(span):
    import Apply.*

    private def resolveMethodType(funTpe: TermType, args: List[TermType])(using Context): TermType =
      funTpe.widen match
        case funTpe: MethodType =>
          for arg <- args do
            if !arg.isInstanceOf[Type] then
              throw InvalidProgramStructureException(s"application of non-type $arg to $funTpe")
          funTpe.instantiate(args.asInstanceOf[List[Type]])
        case tpe =>
          throw NonMethodReferenceException(s"application of args ${args.mkString} to $tpe")

    protected final def calculateType(using Context): TermType =
      val original = resolveMethodType(fun.tpe, args.map(_.tpe))
      // If the resolved method type is not methodic, then it is the final result type.
      // in this case, check the method part to see if it is a constructor selection.
      // if it is, then the result type is the type of new.
      original match
        case partial: MethodicType => partial // Nothing to do here, it is partially applied.
        case _                     => computeAppliedNewType(fun).getOrElse(original)
    end calculateType

    override final def withSpan(span: Span): Apply = Apply(fun, args)(span)
  end Apply

  object Apply:
    /** Compute the type of a fully-applied `New` node, if it is indeed one.
      *
      * When the receiver of a constructor application is a `New` node, the
      * result type must be the (applied) class type of the `New` node, instead
      * of the result type of the constructor method (which is `Unit`).
      *
      * In addition, when computing the `parents` of a class symbol, we must
      * find the parents but we want to avoid actually resolving constructor
      * references, since that is expensive (and, when faced with incorrect
      * TASTy, breaking everything).
      *
      * We would like to say that we should always use the `tpe` of the `New`
      * node. However, that is not always the case. In *some* situations,
      * (apparently when type arguments are inferred, but not always), the
      * `New` node has the unapplied, polymorphic type! (Sometimes it is even
      * embedded in an eta-expansion `TypeLambda`, but that's fine.)
      *
      * Therefore, we need to find the `New` node, collecting type arguments in
      * the process. If we do find one, we apply the type arguments (if any) to
      * its `tpe` as long as the latter is polymorphic.
      *
      * If we do not find a `New` node, we return the `original` type that was
      * computed by `resolveMethodType` above.
      *
      * Sometimes, wrapped applications are enclosed in a block with only
      * ValDefs as statements. That happens because of named arguments, e.g.
      *   <init>(b = foo, a = bar)
      * is transformed to
      *   { val x$1 = foo
      *     val x$2 = bar
      *     <init>(x$2, x$1)
      *   }
      */
    private[tastyquery] def computeAppliedNewType(tree: TermTree)(using Context): Option[Type] =
      computeAppliedNewType(tree, Nil)

    @tailrec
    private def computeAppliedNewType(tree: TermTree, targssTail: List[List[TypeTree]])(using Context): Option[Type] =
      tree match
        case Apply(fn, _)         => computeAppliedNewType(fn, targssTail)
        case TypeApply(fn, targs) => computeAppliedNewType(fn, targs :: targssTail)
        case Block(stats, expr)   => computeAppliedNewType(expr, targssTail)

        case Select(New(tpt), SignedName(nme.Constructor, _, _)) =>
          val result = targssTail.foldLeft(tpt.toType) { (newTpe, targs) =>
            if targs.nonEmpty && newTpe.typeParams.nonEmpty then newTpe.appliedTo(targs.map(_.toType))
            else newTpe
          }
          Some(result)

        case _ =>
          None
    end computeAppliedNewType

  end Apply

  /** fun[args] */
  final case class TypeApply(fun: TermTree, args: List[TypeTree])(span: Span) extends TermTree(span) {

    private def resolvePolyType(funTpe: TermType, args: List[TypeOrWildcard])(using Context): TermType =
      funTpe.widen match
        case funTpe: PolyType =>
          funTpe.instantiate(args)
        case tpe =>
          throw NonMethodReferenceException(s"type application of args ${args.mkString} to $tpe")

    protected final def calculateType(using Context): TermType =
      resolvePolyType(fun.tpe, args.map(_.toType))

    override final def withSpan(span: Span): TypeApply = TypeApply(fun, args)(span)
  }

  /** new tpt, but no constructor call */
  final case class New(tpt: TypeTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      tpt.toType

    override final def withSpan(span: Span): New = New(tpt)(span)
  }

  /** expr : tpt */
  final case class Typed(expr: TermTree, tpt: TypeTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      tpt.toType

    override final def withSpan(span: Span): Typed = Typed(expr, tpt)(span)
  }

  /** name = arg, outside a parameter list */
  final case class Assign(lhs: TermTree, rhs: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      defn.UnitType

    override final def withSpan(span: Span): Assign = Assign(lhs, rhs)(span)
  }

  /** name = arg, in a parameter list */
  final case class NamedArg(name: Name, arg: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      arg.tpe

    override final def withSpan(span: Span): NamedArg = NamedArg(name, arg)(span)
  }

  /** { stats; expr } */
  final case class Block(stats: List[StatementTree], expr: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      expr.tpe

    override final def withSpan(span: Span): Block = Block(stats, expr)(span)
  }

  /** if cond then thenp else elsep */
  final case class If(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      OrType(thenPart.tpe.requireType, elsePart.tpe.requireType)

    override final def withSpan(span: Span): If = If(cond, thenPart, elsePart)(span)
  }

  final case class InlineIf(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      OrType(thenPart.tpe.requireType, elsePart.tpe.requireType)

    override final def withSpan(span: Span): InlineIf = InlineIf(cond, thenPart, elsePart)(span)
  }

  /**  @param meth   A reference to the method.
    *  @param tpt    Defined only if the lambda's type is a SAMtype rather than a function type.
    */
  final case class Lambda(meth: TermTree, tpt: Option[TypeTree])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType = tpt match
      case Some(tpt) =>
        tpt.toType

      case None =>
        val methodType = meth.tpe.widen match
          case mt: MethodType if !mt.resultType.isInstanceOf[MethodicType] =>
            mt
          case mt =>
            throw InvalidProgramStructureException(s"Unexpected type for the `meth` part of a Lambda: $mt")

        val paramCount = methodType.paramNames.size
        val functionNTypeRef = defn.FunctionNClass(paramCount).staticRef

        if methodType.isResultDependent then
          val parent = functionNTypeRef.appliedTo(List.fill(paramCount + 1)(defn.AnyType))
          TermRefinement(parent, isStable = false, nme.m_apply, methodType)
        else functionNTypeRef.appliedTo(methodType.paramTypes :+ methodType.resultType.asInstanceOf[Type])
    end calculateType

    override final def withSpan(span: Span): Lambda = Lambda(meth, tpt)(span)
  }

  /** selector match { cases } */
  final case class Match(selector: TermTree, cases: List[CaseDef])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      cases.map(_.body.tpe.requireType).reduce[Type](OrType(_, _))

    override final def withSpan(span: Span): Match = Match(selector, cases)(span)
  }

  final case class InlineMatch(selector: Option[TermTree], cases: List[CaseDef])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      cases.map(_.body.tpe.requireType).reduce[Type](OrType(_, _))

    override final def withSpan(span: Span): InlineMatch = InlineMatch(selector, cases)(span)
  }

  /** case pattern if guard => body; only appears as child of a Match and Try */
  final case class CaseDef(pattern: PatternTree, guard: Option[TermTree], body: TermTree)(span: Span)
      extends Tree(span) {
    override final def withSpan(span: Span): CaseDef = CaseDef(pattern, guard, body)(span)
  }

  sealed abstract class PatternTree(span: Span) extends Tree(span):
    def withSpan(span: Span): PatternTree
  end PatternTree

  /** Wildcard pattern `_`. */
  final case class WildcardPattern(tpe: Type)(span: Span) extends PatternTree(span):
    override def withSpan(span: Span): WildcardPattern = WildcardPattern(tpe)(span)
  end WildcardPattern

  /** Type-test pattern `pat: T`. */
  final case class TypeTest(body: PatternTree, tpt: TypeTree)(span: Span) extends PatternTree(span):
    override final def withSpan(span: Span): TypeTest = TypeTest(body, tpt)(span)
  end TypeTest

  /** pattern in {@link Unapply} */
  final case class Bind(name: Name, body: PatternTree, symbol: TermSymbol)(span: Span)
      extends PatternTree(span)
      with DefTree {
    override final def withSpan(span: Span): Bind = Bind(name, body, symbol)(span)
  }

  /** tree_1 | ... | tree_n */
  final case class Alternative(trees: List[PatternTree])(span: Span) extends PatternTree(span) {
    override final def withSpan(span: Span): Alternative = Alternative(trees)(span)
  }

  /** `extractor(patterns)` in a pattern:
    *  @param fun       is `extractor.unapply` (or, for backwards compatibility, `extractor.unapplySeq`)
    *                   possibly with type parameters
    *  @param implicits Any implicit parameters passed to the unapply after the selector
    *  @param patterns  The argument patterns in the pattern match.
    *
    *  It is typed with same type as first `fun` argument
    *  Given a match selector `sel` a pattern UnApply(fun, implicits, patterns) is roughly translated as follows
    *
    *    val result = fun(sel)(implicits)
    *    if (result.isDefined) "match patterns against result"
    */
  final case class Unapply(fun: TermTree, implicits: List[TermTree], patterns: List[PatternTree])(span: Span)
      extends PatternTree(span) {
    override final def withSpan(span: Span): Unapply = Unapply(fun, implicits, patterns)(span)
  }

  final case class ExprPattern(expr: TermTree)(span: Span) extends PatternTree(span):
    override final def withSpan(span: Span): ExprPattern = ExprPattern(expr)(span)
  end ExprPattern

  /** Seq(elems)
    *  @param  tpt  The element type of the sequence.
    */
  final case class SeqLiteral(elems: List[TermTree], elemtpt: TypeTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      defn.SeqTypeOf(elemtpt.toType)

    override final def withSpan(span: Span): SeqLiteral = SeqLiteral(elems, elemtpt)(span)
  }

  /** while (cond) { body } */
  final case class While(cond: TermTree, body: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      defn.UnitType

    override final def withSpan(span: Span): While = While(cond, body)(span)
  }

  /** throw expr */
  final case class Throw(expr: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      defn.NothingType

    override final def withSpan(span: Span): Throw = Throw(expr)(span)
  }

  /** try block catch cases finally finalizer */
  final case class Try(expr: TermTree, cases: List[CaseDef], finalizer: Option[TermTree])(span: Span)
      extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      cases.foldLeft(expr.tpe.requireType)((prev, caze) => OrType(prev, caze.body.tpe.requireType))

    override final def withSpan(span: Span): Try = Try(expr, cases, finalizer)(span)
  }

  final case class Literal(constant: Constant)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      ConstantType(constant)

    override final def withSpan(span: Span): Literal = Literal(constant)(span)
  }

  final case class Return(expr: Option[TermTree], from: TermSymbol)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      defn.NothingType

    override final def withSpan(span: Span): Return = Return(expr, from)(span)
  }

  /** A tree representing inlined code.
    *
    * @param expr
    *   The inlined tree, minus bindings.
    * @param caller
    *   The toplevel class from which the call was inlined.
    * @param bindings
    *   Bindings for proxies to be used in the inlined code
    *
    * The full inlined code is equivalent to
    *
    * { bindings; expr }
    */
  final case class Inlined(expr: TermTree, caller: Option[TypeIdent | SelectTypeTree], bindings: List[ValOrDefDef])(
    span: Span
  ) extends TermTree(span) {
    protected final def calculateType(using Context): TermType =
      // TODO? Do we need to do type avoidance on expr using the bindings, like dotc does?
      expr.tpe

    override final def withSpan(span: Span): Inlined = Inlined(expr, caller, bindings)(span)
  }

  // --- TypeTrees ------------------------------------------------------------

  sealed abstract class TypeArgTree(span: Span) extends Tree(span):
    def withSpan(span: Span): TypeArgTree

    def toTypeOrWildcard(using Context): TypeOrWildcard
  end TypeArgTree

  sealed abstract class TypeTree(span: Span) extends TypeArgTree(span) {
    private var myType: NonEmptyPrefix | Null = null

    protected def calculateType(using Context): NonEmptyPrefix

    def withSpan(span: Span): TypeTree

    final def toPrefix(using Context): NonEmptyPrefix =
      val local = myType
      if local == null then
        val computed = calculateType
        myType = calculateType
        computed
      else local
    end toPrefix

    final def toType(using Context): Type = toPrefix.requireType

    final def toTypeOrWildcard(using Context): Type = toType
  }

  final case class TypeIdent(name: TypeName)(tpe: NonEmptyPrefix)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): NonEmptyPrefix =
      tpe

    override final def withSpan(span: Span): TypeIdent = TypeIdent(name)(tpe)(span)
  }

  final case class TypeWrapper(tp: NonEmptyPrefix)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): NonEmptyPrefix = tp

    override final def withSpan(span: Span): TypeWrapper = TypeWrapper(tp)(span)
  }

  /** ref.type */
  final case class SingletonTypeTree(ref: TermTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): NonEmptyPrefix =
      ref.tpe match
        case refTpe: NonEmptyPrefix =>
          refTpe
        case refTpe: MethodicType =>
          throw InvalidProgramStructureException(s"Invalid singleton type $ref.type with type $refTpe")
    end calculateType

    override final def withSpan(span: Span): SingletonTypeTree = SingletonTypeTree(ref)(span)
  }

  type RefinementMemberDef = TypeMember | ValOrDefDef

  final case class RefinedTypeTree(
    underlying: TypeTree,
    refinements: List[RefinementMemberDef],
    refinedCls: ClassSymbol
  )(span: Span)
      extends TypeTree(span) {

    override protected def calculateType(using Context): Type =
      val base = underlying.toType
      val refined = refinements.foldLeft(base) { (parent, refinement) =>
        refinement match
          case TypeMember(name, rhs, _) =>
            TypeRefinement(parent, name, makeRefinedBounds(name, rhs))

          case ValDef(name, tpt, _, _) =>
            TermRefinement(parent, isStable = true, name, tpt.toType)

          case DefDef(name, paramClauses, resultType, _, _) =>
            TermRefinement(parent, isStable = false, name, ParamsClause.makeDefDefType(paramClauses, resultType))
      }

      if refined eq base then base
      else RecType.fromRefinedClassDecls(refined, refinedCls)
    end calculateType

    private def makeRefinedBounds(name: TypeName, rhs: TypeDefinitionTree)(using Context): TypeBounds =
      rhs match
        case TypeAliasDefinitionTree(tpt) =>
          TypeAlias(tpt.toType)
        case rhs: TypeBoundsTree =>
          rhs.toTypeBounds
        case rhs @ PolyTypeDefinitionTree(_, body) =>
          makeRefinedBounds(name, body).mapBounds(rhs.integrateInto(_))
        case _ =>
          throw InvalidProgramStructureException(s"Unexpected rhs for type refinement '$name': $rhs")
    end makeRefinedBounds

    override final def withSpan(span: Span): RefinedTypeTree =
      RefinedTypeTree(underlying, refinements, refinedCls)(span)
  }

  /** => T */
  final case class ByNameTypeTree(result: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      ByNameType(result.toType)

    override final def withSpan(span: Span): ByNameTypeTree = ByNameTypeTree(result)(span)
  }

  /** tpt[args]
    * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
    */
  final case class AppliedTypeTree(tycon: TypeTree, args: List[TypeArgTree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      AppliedType(tycon.toType, args.map(_.toTypeOrWildcard))

    override final def withSpan(span: Span): AppliedTypeTree = AppliedTypeTree(tycon, args)(span)
  }

  /** qualifier#name */
  final case class SelectTypeTree(qualifier: TypeTree, name: TypeName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeRef(qualifier.toPrefix, name)

    override final def withSpan(span: Span): SelectTypeTree = SelectTypeTree(qualifier, name)(span)
  }

  /** qualifier.name */
  final case class TermRefTypeTree(qualifier: TermTree, name: TermName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): NonEmptyPrefix =
      qualifier.tpe match
        case prefix: NonEmptyPrefix =>
          NamedType.possibleSelFromPackage(prefix, name)
        case qualType =>
          throw InvalidProgramStructureException(s"Invalid selection from $qualifier with type $qualType")

    override final def withSpan(span: Span): TermRefTypeTree = TermRefTypeTree(qualifier, name)(span)
  }

  /** arg @annot */
  final case class AnnotatedTypeTree(tpt: TypeTree, annotation: TermTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      AnnotatedType(tpt.toType, Annotation(annotation))

    override final def withSpan(span: Span): AnnotatedTypeTree = AnnotatedTypeTree(tpt, annotation)(span)
  }

  /** [bound] selector match { cases } */
  final case class MatchTypeTree(bound: Option[TypeTree], selector: TypeTree, cases: List[TypeCaseDef])(span: Span)
      extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      MatchType(bound.fold(defn.AnyType)(_.toType), selector.toType, cases.map(_.toMatchTypeCase))

    override final def withSpan(span: Span): MatchTypeTree = MatchTypeTree(bound, selector, cases)(span)
  }

  final case class TypeCaseDef(pattern: TypeTree, body: TypeTree)(span: Span) extends Tree(span):
    def withSpan(span: Span): TypeCaseDef = TypeCaseDef(pattern, body)(span)

    private[Trees] def toMatchTypeCase(using Context): MatchTypeCase =
      val bindsBuffer = mutable.ListBuffer.empty[LocalTypeParamSymbol]
      collectBinds(pattern, bindsBuffer)
      val binds = bindsBuffer.toList

      val patternType = pattern.toType
      val resultType = body.toType

      MatchTypeCase.fromParams(binds, patternType, resultType)
    end toMatchTypeCase

    private def collectBinds(tpt: TypeArgTree, buffer: mutable.ListBuffer[LocalTypeParamSymbol]): Unit = tpt match
      case TypeTreeBind(_, _, sym) =>
        buffer += sym
      case AppliedTypeTree(tycon, targs) =>
        for targ <- targs do collectBinds(targ, buffer)
      case _ =>
        ()
    end collectBinds
  end TypeCaseDef

  final case class TypeTreeBind(name: TypeName, body: TypeDefinitionTree, symbol: LocalTypeParamSymbol)(span: Span)
      extends TypeTree(span)
      with DefTree {
    override protected def calculateType(using Context): Type =
      TypeRef(NoPrefix, symbol)

    override final def withSpan(span: Span): TypeTreeBind = TypeTreeBind(name, body, symbol)(span)
  }

  final case class WildcardTypeArgTree(bounds: TypeBoundsTree)(span: Span) extends TypeArgTree(span) {
    private var myTypeOrWildcard: WildcardTypeArg | Null = null

    def toTypeOrWildcard(using Context): TypeOrWildcard =
      val local = myTypeOrWildcard
      if local != null then local
      else
        val computed = WildcardTypeArg(bounds.toTypeBounds)
        myTypeOrWildcard = computed
        computed
    end toTypeOrWildcard

    override final def withSpan(span: Span): WildcardTypeArgTree =
      WildcardTypeArgTree(bounds)(span)
  }

  final case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), body.toType))

    override final def withSpan(span: Span): TypeLambdaTree = TypeLambdaTree(tparams, body)(span)
  }

  final case class TypeBindingsTree(bindings: List[TypeMember], body: TypeTree)(span: Span) extends TypeTree(span):
    override protected def calculateType(using Context): Type = body.toType

    override def withSpan(span: Span): TypeBindingsTree = TypeBindingsTree(bindings, body)(span)
  end TypeBindingsTree

  // --- TypeDefinitionTrees and TypeBoundsTrees ------------------------------

  sealed abstract class TypeDefinitionTree(span: Span) extends Tree(span):
    def withSpan(span: Span): TypeDefinitionTree
  end TypeDefinitionTree

  sealed abstract class TypeBoundsTree(span: Span) extends TypeDefinitionTree(span):
    def withSpan(span: Span): TypeBoundsTree

    def toTypeBounds(using Context): TypeBounds
  end TypeBoundsTree

  final case class InferredTypeBoundsTree(bounds: TypeBounds)(span: Span) extends TypeBoundsTree(span):
    def withSpan(span: Span): InferredTypeBoundsTree =
      InferredTypeBoundsTree(bounds)(span)

    def toTypeBounds(using Context): TypeBounds = bounds
  end InferredTypeBoundsTree

  final case class ExplicitTypeBoundsTree(low: TypeTree, high: TypeTree)(span: Span) extends TypeBoundsTree(span):
    def withSpan(span: Span): ExplicitTypeBoundsTree =
      ExplicitTypeBoundsTree(low, high)(span)

    def toTypeBounds(using Context): TypeBounds =
      RealTypeBounds(low.toType, high.toType)
  end ExplicitTypeBoundsTree

  final case class TypeAliasDefinitionTree(alias: TypeTree)(span: Span) extends TypeDefinitionTree(span):
    def withSpan(span: Span): TypeAliasDefinitionTree =
      TypeAliasDefinitionTree(alias)(span)
  end TypeAliasDefinitionTree

  final case class OpaqueTypeAliasDefinitionTree(bounds: TypeBoundsTree, alias: TypeTree)(span: Span)
      extends TypeDefinitionTree(span):
    def withSpan(span: Span): OpaqueTypeAliasDefinitionTree =
      OpaqueTypeAliasDefinitionTree(bounds, alias)(span)
  end OpaqueTypeAliasDefinitionTree

  final case class PolyTypeDefinitionTree(tparams: List[TypeParam], body: TypeDefinitionTree)(span: Span)
      extends TypeDefinitionTree(span):
    def withSpan(span: Span): PolyTypeDefinitionTree =
      PolyTypeDefinitionTree(tparams, body)(span)

    private[tastyquery] def integrateInto(resultType: Type)(using Context): Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), resultType))
  end PolyTypeDefinitionTree

  final case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds)(span: Span) extends TypeDefinitionTree(span):
    override final def withSpan(span: Span): NamedTypeBoundsTree =
      NamedTypeBoundsTree(name, bounds)(span)
  end NamedTypeBoundsTree

}
