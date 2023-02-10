package tastyquery

import scala.annotation.tailrec

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
      case TypeMember(_, rhs, _) =>
        rhs match
          case rhs: TypeTree => rhs :: Nil
          case _: TypeBounds => Nil
      case Template(constr, parents, self, body)  => constr :: parents ::: self.toList ::: body
      case ValDef(name, tpt, rhs, symbol)         => tpt :: rhs.toList
      case DefDef(name, params, tpt, rhs, symbol) => params.flatMap(_.merge) ::: tpt :: rhs.toList
      case Select(qualifier, name)                => qualifier :: Nil
      case Super(qual, mix)                       => qual :: Nil
      case Apply(fun, args)                       => fun :: args
      case TypeApply(fun, args)                   => fun :: args
      case New(tpt)                               => tpt :: Nil
      case Typed(expr, tpt)                       => expr :: tpt :: Nil
      case Assign(lhs, rhs)                       => lhs :: rhs :: Nil
      case NamedArg(name, arg)                    => arg :: Nil
      case Block(stats, expr)                     => stats :+ expr
      case If(cond, thenPart, elsePart)           => cond :: thenPart :: elsePart :: Nil
      case InlineIf(cond, thenPart, elsePart)     => cond :: thenPart :: elsePart :: Nil
      case Lambda(meth, tpt)                      => meth :: tpt.toList
      case Match(selector, cases)                 => selector :: cases
      case InlineMatch(selector, cases)           => selector.toList ::: cases
      case CaseDef(pattern, guard, body)          => pattern :: guard.toList ::: body :: Nil
      case TypeTest(body, tpt)                    => body :: tpt :: Nil
      case Bind(name, body, symbol)               => body :: Nil
      case Alternative(trees)                     => trees
      case Unapply(fun, implicits, patterns)      => fun :: implicits ++ patterns
      case ExprPattern(expr)                      => expr :: Nil
      case SeqLiteral(elems, elemtpt)             => elems ::: elemtpt :: Nil
      case While(cond, body)                      => cond :: body :: Nil
      case Throw(expr)                            => expr :: Nil
      case Try(expr, cases, finalizer)            => (expr :: cases) ::: finalizer.toList
      case Return(expr, from)                     => expr.toList
      case Inlined(expr, caller, bindings)        => expr :: bindings

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
      case TypeBoundsTree(low, high)                      => low :: high :: Nil
      case BoundedTypeTree(bounds, alias)                 => bounds :: alias.toList
      case NamedTypeBoundsTree(name, bounds)              => Nil
      case WildcardTypeBoundsTree(bounds)                 => bounds :: Nil
      case TypeLambdaTree(tparams, body)                  => tparams ::: body :: Nil

      case _: ImportIdent | _: TypeMember | _: TypeParam | _: Ident | _: This | _: New | _: Literal | _: SelfDef |
          _: WildcardPattern | _: TypeIdent =>
        Nil
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
    private var myType: Type | Null = null

    def withSpan(span: Span): TermTree

    /** Compute the actual term of this tree. */
    protected def calculateType(using Context): Type

    /** The term type of this tree. */
    final def tpe(using Context): Type = {
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
  final case class TypeMember(name: TypeName, rhs: TypeTree | TypeBounds, symbol: TypeMemberSymbol)(span: Span)
      extends TypeDef(name)(span) {
    override final def withSpan(span: Span): TypeMember = TypeMember(name, rhs, symbol)(span)
  }

  /** The bounds are a type tree if the method is defined by the user and bounds-only if it's synthetic */
  final case class TypeParam(
    name: TypeName,
    bounds: TypeBoundsTree | TypeBounds | TypeLambdaTree,
    symbol: TypeParamSymbol
  )(span: Span)
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

  /** name */
  final case class Ident(name: TermName)(tpe: TermRef | PackageRef)(span: Span) extends TermTree(span):
    protected final def calculateType(using Context): Type = tpe

    def symbol(using Context): TermSymbol | PackageSymbol = tpe match
      case termRef: TermRef       => termRef.symbol
      case packageRef: PackageRef => packageRef.symbol

    override final def withSpan(span: Span): Ident = Ident(name)(tpe)(span)
  end Ident

  /** qualifier.termName */
  final case class Select(qualifier: TermTree, name: TermName)(selectOwner: Option[TypeRef])(span: Span)
      extends TermTree(span):
    require(
      selectOwner.isEmpty || name.isInstanceOf[SignedName],
      s"illegal section of unsigned name '$name' in owner ${selectOwner.get}"
    )

    protected final def calculateType(using Context): TermRef | PackageRef = selectOwner match
      case Some(selOwner) => TermRef(qualifier.tpe, LookupIn(selOwner, name.asInstanceOf[SignedName]))
      case None           => NamedType.possibleSelFromPackage(qualifier.tpe, name)

    def symbol(using Context): TermSymbol | PackageSymbol = tpe match
      case termRef: TermRef       => termRef.symbol
      case packageRef: PackageRef => packageRef.symbol
      case tpe                    => throw AssertionError(s"unexpected type $tpe in Select node")

    override def withSpan(span: Span): Select = Select(qualifier, name)(selectOwner)(span)
  end Select

  /** `qual.this` */
  final case class This(qualifier: TypeIdent)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      qualifier.toType match
        case pkg: PackageRef => pkg
        case tref: TypeRef   => ThisType(tref)
        case qualTpe =>
          throw InvalidProgramStructureException(s"Unexpected type for This qualifier $qualifier: $qualTpe")
    end calculateType

    override final def withSpan(span: Span): This = This(qualifier)(span)
  }

  /** C.super[mix], where qual = C.this */
  final case class Super(qual: TermTree, mix: Option[TypeIdent])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
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

    private def resolveMethodType(funTpe: Type, args: List[Type])(using Context): Type =
      funTpe.widenOverloads match
        case funTpe: MethodType =>
          funTpe.instantiate(args)
        case tpe =>
          throw NonMethodReferenceException(s"application of args ${args.mkString} to $tpe")

    protected final def calculateType(using Context): Type =
      val original = resolveMethodType(fun.tpe, args.map(_.tpe))
      // If the resolved method type is not methodic, then it is the final result type.
      // in this case, check the method part to see if it is a constructor selection.
      // if it is, then the result type is the type of new.
      original match
        case partial: MethodicType => partial // Nothing to do here, it is partially applied.
        case _                     => patchNewType(fun, Nil, original)
    end calculateType

    /** Possibly patch the type of a fully-applied `New` node.
      *
      * When the receiver of a constructor application is a `New` node, the
      * result type must be the (applied) class type of the `New` node, instead
      * of the result type of the constructor method (which is `Unit`).
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
    @tailrec
    private def patchNewType(tree: TermTree, targssTail: List[List[TypeTree]], original: Type)(using Context): Type =
      tree match
        case Apply(fn, _)         => patchNewType(fn, targssTail, original)
        case TypeApply(fn, targs) => patchNewType(fn, targs :: targssTail, original)
        case Block(stats, expr)   => patchNewType(expr, targssTail, original)

        case Select(newObj @ New(_), SignedName(nme.Constructor, _, _)) =>
          targssTail.foldLeft(newObj.tpe) { (newTpe, targs) =>
            if targs.nonEmpty && newTpe.typeParams.nonEmpty then newTpe.appliedTo(targs.map(_.toType))
            else newTpe
          }

        case _ => original
    end patchNewType

    override final def withSpan(span: Span): Apply = Apply(fun, args)(span)

  /** fun[args] */
  final case class TypeApply(fun: TermTree, args: List[TypeTree])(span: Span) extends TermTree(span) {

    private def resolvePolyType(funTpe: Type, args: List[Type])(using Context): Type =
      funTpe.widenOverloads match
        case funTpe: PolyType =>
          funTpe.instantiate(args)
        case tpe =>
          throw NonMethodReferenceException(s"type application of args ${args.mkString} to $tpe")

    protected final def calculateType(using Context): Type =
      resolvePolyType(fun.tpe, args.map(_.toType))

    override final def withSpan(span: Span): TypeApply = TypeApply(fun, args)(span)
  }

  /** new tpt, but no constructor call */
  final case class New(tpt: TypeTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      tpt.toType

    override final def withSpan(span: Span): New = New(tpt)(span)
  }

  /** expr : tpt */
  final case class Typed(expr: TermTree, tpt: TypeTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      tpt.toType

    override final def withSpan(span: Span): Typed = Typed(expr, tpt)(span)
  }

  /** name = arg, outside a parameter list */
  final case class Assign(lhs: TermTree, rhs: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      defn.UnitType

    override final def withSpan(span: Span): Assign = Assign(lhs, rhs)(span)
  }

  /** name = arg, in a parameter list */
  final case class NamedArg(name: Name, arg: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      arg.tpe

    override final def withSpan(span: Span): NamedArg = NamedArg(name, arg)(span)
  }

  /** { stats; expr } */
  final case class Block(stats: List[StatementTree], expr: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      expr.tpe

    override final def withSpan(span: Span): Block = Block(stats, expr)(span)
  }

  /** if cond then thenp else elsep */
  final case class If(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      OrType(thenPart.tpe, elsePart.tpe)

    override final def withSpan(span: Span): If = If(cond, thenPart, elsePart)(span)
  }

  final case class InlineIf(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      OrType(thenPart.tpe, elsePart.tpe)

    override final def withSpan(span: Span): InlineIf = InlineIf(cond, thenPart, elsePart)(span)
  }

  /**  @param meth   A reference to the method.
    *  @param tpt    Defined only if the lambda's type is a SAMtype rather than a function type.
    */
  final case class Lambda(meth: TermTree, tpt: Option[TypeTree])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type = tpt match
      case Some(tpt) =>
        tpt.toType
      case None =>
        ??? // TODO Resolve the method's type to construct the appropriate scala.FunctionN type

    override final def withSpan(span: Span): Lambda = Lambda(meth, tpt)(span)
  }

  /** selector match { cases } */
  final case class Match(selector: TermTree, cases: List[CaseDef])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      cases.map(_.body.tpe).reduce(OrType(_, _))

    override final def withSpan(span: Span): Match = Match(selector, cases)(span)
  }

  final case class InlineMatch(selector: Option[TermTree], cases: List[CaseDef])(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      cases.map(_.body.tpe).reduce(OrType(_, _))

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
    protected final def calculateType(using Context): Type =
      defn.SeqTypeOf(elemtpt.toType)

    override final def withSpan(span: Span): SeqLiteral = SeqLiteral(elems, elemtpt)(span)
  }

  /** while (cond) { body } */
  final case class While(cond: TermTree, body: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      defn.UnitType

    override final def withSpan(span: Span): While = While(cond, body)(span)
  }

  /** throw expr */
  final case class Throw(expr: TermTree)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      defn.NothingType

    override final def withSpan(span: Span): Throw = Throw(expr)(span)
  }

  /** try block catch cases finally finalizer */
  final case class Try(expr: TermTree, cases: List[CaseDef], finalizer: Option[TermTree])(span: Span)
      extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      cases.foldLeft(expr.tpe)((prev, caze) => OrType(prev, caze.body.tpe))

    override final def withSpan(span: Span): Try = Try(expr, cases, finalizer)(span)
  }

  final case class Literal(constant: Constant)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      ConstantType(constant)

    override final def withSpan(span: Span): Literal = Literal(constant)(span)
  }

  final case class Return(expr: Option[TermTree], from: TermSymbol)(span: Span) extends TermTree(span) {
    protected final def calculateType(using Context): Type =
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
  final case class Inlined(expr: TermTree, caller: Option[TypeIdent], bindings: List[ValOrDefDef])(span: Span)
      extends TermTree(span) {
    protected final def calculateType(using Context): Type =
      // TODO? Do we need to do type avoidance on expr using the bindings, like dotc does?
      expr.tpe

    override final def withSpan(span: Span): Inlined = Inlined(expr, caller, bindings)(span)
  }

  sealed abstract class TypeTree(span: Span) extends Tree(span) {
    private var myType: Type | Null = null

    protected def calculateType(using Context): Type

    def withSpan(span: Span): TypeTree

    final def toType(using Context): Type = {
      val local = myType
      if local == null then
        val computed = calculateType
        myType = calculateType
        computed
      else local
    }
  }

  final case class TypeIdent(name: TypeName)(tpe: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      tpe

    override final def withSpan(span: Span): TypeIdent = TypeIdent(name)(tpe)(span)
  }

  final case class TypeWrapper(tp: Type)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type = tp

    override final def withSpan(span: Span): TypeWrapper = TypeWrapper(tp)(span)
  }

  /** ref.type */
  final case class SingletonTypeTree(ref: TermTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      ref.tpe

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
      underlying.toType // TODO Actually take the refinements into account

    override final def withSpan(span: Span): RefinedTypeTree =
      RefinedTypeTree(underlying, refinements, refinedCls)(span)
  }

  /** => T */
  final case class ByNameTypeTree(result: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      ExprType(result.toType)

    override final def withSpan(span: Span): ByNameTypeTree = ByNameTypeTree(result)(span)
  }

  /** tpt[args]
    * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
    */
  final case class AppliedTypeTree(tycon: TypeTree, args: List[TypeTree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      AppliedType(tycon.toType, args.map(_.toType))

    override final def withSpan(span: Span): AppliedTypeTree = AppliedTypeTree(tycon, args)(span)
  }

  /** qualifier#name */
  final case class SelectTypeTree(qualifier: TypeTree, name: TypeName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeRef(qualifier.toType, name)

    override final def withSpan(span: Span): SelectTypeTree = SelectTypeTree(qualifier, name)(span)
  }

  /** qualifier.name */
  final case class TermRefTypeTree(qualifier: TermTree, name: TermName)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      NamedType.possibleSelFromPackage(qualifier.tpe, name)

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
      defn.NothingType // TODO

    override final def withSpan(span: Span): MatchTypeTree = MatchTypeTree(bound, selector, cases)(span)
  }

  final case class TypeCaseDef(pattern: TypeTree, body: TypeTree)(span: Span) extends Tree(span):
    def withSpan(span: Span): TypeCaseDef = TypeCaseDef(pattern, body)(span)
  end TypeCaseDef

  final case class TypeTreeBind(name: TypeName, body: TypeTree, symbol: LocalTypeParamSymbol)(span: Span)
      extends TypeTree(span)
      with DefTree {
    override protected def calculateType(using Context): Type =
      TypeRef(NoPrefix, symbol)

    override final def withSpan(span: Span): TypeTreeBind = TypeTreeBind(name, body, symbol)(span)
  }

  final case class TypeBoundsTree(low: TypeTree, high: TypeTree)(span: Span) extends Tree(span) {
    def withSpan(span: Span): TypeBoundsTree = TypeBoundsTree(low, high)(span)

    def toTypeBounds(using Context): TypeBounds =
      RealTypeBounds(low.toType, high.toType)
  }

  /** >: lo <: hi
    *  >: lo <: hi = alias  for RHS of bounded opaque type
    */
  final case class BoundedTypeTree(bounds: TypeBoundsTree, alias: Option[TypeTree])(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      BoundedType(bounds.toTypeBounds, alias.map(_.toType))

    override final def withSpan(span: Span): BoundedTypeTree = BoundedTypeTree(bounds, alias)(span)
  }

  final case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      NamedTypeBounds(name, bounds)

    override final def withSpan(span: Span): NamedTypeBoundsTree = NamedTypeBoundsTree(name, bounds)(span)
  }

  final case class WildcardTypeBoundsTree(bounds: TypeBoundsTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      WildcardTypeBounds(bounds.toTypeBounds)

    override final def withSpan(span: Span): WildcardTypeBoundsTree =
      WildcardTypeBoundsTree(bounds)(span)
  }

  final case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree)(span: Span) extends TypeTree(span) {
    override protected def calculateType(using Context): Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), body.toType))

    override final def withSpan(span: Span): TypeLambdaTree = TypeLambdaTree(tparams, body)(span)
  }

}
