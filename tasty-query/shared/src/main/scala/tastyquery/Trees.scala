package tastyquery

import scala.annotation.constructorOnly
import scala.annotation.tailrec

import scala.collection.mutable

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Spans.*
import tastyquery.Symbols.*
import tastyquery.Traversers.*
import tastyquery.Types.*
import tastyquery.Utils.*

object Trees {

  sealed abstract class Tree(@constructorOnly posInit: SourcePosition) extends Product {
    val pos: SourcePosition =
      if posInit.isAuto then (this: @unchecked).computeAutoPos(posInit.sourceFile)
      else posInit

    private def computeAutoPos(source: SourceFile): SourcePosition = this match
      case Inlined(call, _, _) =>
        call.pos

      case _ =>
        def rec(span: Span, item: Any): Span = item.asInstanceOf[Matchable] match
          case item: Tree =>
            if item.pos.sourceFile == source then span.union(item.pos.span)
            else span
          case x :: xs =>
            rec(rec(span, x), xs)
          case Left(x) =>
            rec(span, x)
          case Right(x) =>
            rec(span, x)
          case _ =>
            span
        end rec

        var span = NoSpan
        val len = productArity
        var i = 0
        while i != len do
          span = rec(span, productElement(i))
          i += 1

        SourcePosition(source, span)
    end computeAutoPos

    def withPos(pos: SourcePosition): Tree

    final def showBasic: String =
      Printers.withWriterToString(writer => new Printers.Printer(writer).printAnyTree(this))

    final def showMultiline: String =
      Printers.withWriterToString(writer => new Printers.MultilinePrinter(writer).printAnyTree(this))
  }

  sealed abstract class TopLevelTree(pos: SourcePosition) extends Tree(pos):
    def withPos(pos: SourcePosition): TopLevelTree
  end TopLevelTree

  sealed abstract class StatementTree(pos: SourcePosition) extends TopLevelTree(pos):
    def withPos(pos: SourcePosition): StatementTree
  end StatementTree

  sealed abstract class TermTree(pos: SourcePosition) extends StatementTree(pos):
    private val myType: Memo[TermType] = uninitializedMemo

    def withPos(pos: SourcePosition): TermTree

    /** Compute the prefix represented by this tree.
      *
      * The default implementation throws an `InvalidProgramStructureException`
      * to indicate that this term tree is not a valid type prefix.
      */
    protected def computeAsTypePrefix: NonEmptyPrefix =
      throw InvalidProgramStructureException(s"$this is not a valid type prefix")

    /** Converts this term tree to a type prefix.
      *
      * @throws Exceptions.InvalidProgramStructureException
      *   if this term tree does not represent a valid type prefix
      */
    private[Trees] final def toTypePrefix: NonEmptyPrefix =
      computeAsTypePrefix

    /** Compute the actual term type of this tree. */
    protected def calculateType(using Context): TermType

    /** The term type of this tree. */
    final def tpe(using Context): TermType = memoized(myType) {
      calculateType
    }
  end TermTree

  sealed trait DefTree extends Tree:
    val symbol: Symbol
  end DefTree

  final case class PackageDef(pid: PackageSymbol, stats: List[TopLevelTree])(pos: SourcePosition)
      extends TopLevelTree(pos) {
    override final def withPos(pos: SourcePosition): PackageDef = PackageDef(pid, stats)(pos)
  }

  /** An identifier appearing in an `import` clause; it has no type. */
  final case class ImportIdent(name: UnsignedTermName)(pos: SourcePosition) extends Tree(pos) {
    override final def withPos(pos: SourcePosition): ImportIdent = ImportIdent(name)(pos)
  }

  final case class ImportSelector(imported: ImportIdent, renamed: Option[ImportIdent], bound: Option[TypeTree])(
    pos: SourcePosition
  ) extends Tree(pos) {

    /** It's a `given` selector */
    val isGiven: Boolean = imported.name == nme.EmptyTermName

    /** It's a `given` or `_` selector */
    val isWildcard: Boolean = isGiven || imported.name == nme.Wildcard

    /** The imported name, EmptyTermName if it's a given selector */
    val name: UnsignedTermName = imported.name

    /** The renamed part (which might be `_`), if present, or `name`, if missing */
    val rename: UnsignedTermName = renamed match {
      case Some(ImportIdent(rename)) => rename
      case None                      => name
    }

    override final def withPos(pos: SourcePosition): ImportSelector = ImportSelector(imported, renamed, bound)(pos)
  }

  final case class Import(expr: TermTree, selectors: List[ImportSelector])(pos: SourcePosition)
      extends StatementTree(pos) {
    override final def withPos(pos: SourcePosition): Import = Import(expr, selectors)(pos)
  }

  /** import expr.selectors */
  final case class Export(expr: TermTree, selectors: List[ImportSelector])(pos: SourcePosition)
      extends StatementTree(pos) {
    override final def withPos(pos: SourcePosition): Export = Export(expr, selectors)(pos)
  }

  /** mods class name template     or
    *  mods trait name template     or
    *  mods type name = rhs   or
    *  mods type name >: lo <: hi,          if rhs = TypeBoundsTree(lo, hi)      or
    *  mods type name >: lo <: hi = rhs     if rhs = TypeBoundsTree(lo, hi, alias) and opaque in mods
    */
  sealed abstract class TypeDef(name: TypeName)(pos: SourcePosition) extends StatementTree(pos) with DefTree:
    val symbol: TypeSymbol
  end TypeDef

  final case class ClassDef(name: TypeName, rhs: Template, symbol: ClassSymbol)(pos: SourcePosition)
      extends TypeDef(name)(pos) {
    override final def withPos(pos: SourcePosition): ClassDef = ClassDef(name, rhs, symbol)(pos)
  }

  /** A type member has a type tree rhs if the member is defined by the user, or typebounds if it's synthetic */
  final case class TypeMember(name: TypeName, rhs: TypeDefinitionTree, symbol: TypeMemberSymbol)(pos: SourcePosition)
      extends TypeDef(name)(pos) {
    override final def withPos(pos: SourcePosition): TypeMember = TypeMember(name, rhs, symbol)(pos)
  }

  /** The bounds are a type tree if the method is defined by the user and bounds-only if it's synthetic */
  final case class TypeParam(name: TypeName, bounds: TypeDefinitionTree, symbol: TypeParamSymbol)(pos: SourcePosition)
      extends TypeDef(name)(pos) {
    override final def withPos(pos: SourcePosition): TypeParam = TypeParam(name, bounds, symbol)(pos)
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
  )(pos: SourcePosition)
      extends Tree(pos) {
    override final def withPos(pos: SourcePosition): Template = Template(constr, parents, self, body)(pos)
  }

  sealed abstract class ValOrDefDef()(pos: SourcePosition) extends StatementTree(pos) with DefTree:
    val name: UnsignedTermName

    val symbol: TermSymbol

    def withPos(pos: SourcePosition): ValOrDefDef
  end ValOrDefDef

  /** mods val name: tpt = rhs */
  final case class ValDef(name: UnsignedTermName, tpt: TypeTree, rhs: Option[TermTree], symbol: TermSymbol)(
    pos: SourcePosition
  ) extends ValOrDefDef()(pos) {
    override final def withPos(pos: SourcePosition): ValDef = ValDef(name, tpt, rhs, symbol)(pos)
  }

  /** Self type definition `name: tpt =>`. */
  final case class SelfDef(name: UnsignedTermName, tpt: TypeTree)(pos: SourcePosition) extends Tree(pos):
    override def withPos(pos: SourcePosition): SelfDef = SelfDef(name, tpt)(pos)
  end SelfDef

  type ParamsClause = Either[List[ValDef], List[TypeParam]]

  private[tastyquery] object ParamsClause:
    def makeDefDefType(paramLists: List[ParamsClause], resultTpt: TypeTree): TypeOrMethodic =
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
    name: UnsignedTermName,
    paramLists: List[ParamsClause],
    resultTpt: TypeTree,
    rhs: Option[TermTree],
    symbol: TermSymbol
  )(pos: SourcePosition)
      extends ValOrDefDef()(pos) {
    override final def withPos(pos: SourcePosition): DefDef = DefDef(name, paramLists, resultTpt, rhs, symbol)(pos)
  }

  // --- TermTrees and PatternTrees -------------------------------------------

  /** An `Ident` or a `Select`. */
  sealed abstract class TermReferenceTree(pos: SourcePosition) extends TermTree(pos):
    final def referenceType(using Context): TermReferenceType =
      tpe.asInstanceOf[TermReferenceType]

    // Refine the result type to make sure that `tpe` is always a `TermReferenceType`.
    protected def calculateType(using Context): TermReferenceType

    final def symbol(using Context): TermSymbol | PackageSymbol = referenceType match
      case termRef: TermRef       => termRef.symbol
      case packageRef: PackageRef => packageRef.symbol

    def withPos(pos: SourcePosition): TermReferenceTree
  end TermReferenceTree

  /** name */
  final case class Ident(name: UnsignedTermName)(tpe: TermReferenceType)(pos: SourcePosition)
      extends TermReferenceTree(pos):
    override protected def computeAsTypePrefix: NonEmptyPrefix = tpe

    protected final def calculateType(using Context): TermReferenceType = tpe

    override final def withPos(pos: SourcePosition): Ident = Ident(name)(tpe)(pos)
  end Ident

  /** qualifier.termName */
  final case class Select(qualifier: TermTree, name: TermName)(selectOwner: Option[TypeRef])(pos: SourcePosition)
      extends TermReferenceTree(pos):
    require(
      selectOwner.isEmpty || name.isInstanceOf[SignedName],
      s"illegal section of unsigned name '$name' in owner ${selectOwner.get}"
    )

    override protected def computeAsTypePrefix: NonEmptyPrefix =
      makeSelection(qualifier.toTypePrefix)

    protected final def calculateType(using Context): TermReferenceType =
      qualifier.tpe match
        case prefix: NonEmptyPrefix =>
          makeSelection(prefix)
        case qualType: MethodicType =>
          throw InvalidProgramStructureException(s"Invalid selection from $qualifier with type $qualType")
    end calculateType

    private def makeSelection(qualifierType: NonEmptyPrefix): TermReferenceType =
      selectOwner match
        case Some(selOwner) => TermRef(qualifierType, LookupIn(selOwner, name.asInstanceOf[SignedName]))
        case None           => NamedType.possibleSelFromPackage(qualifierType, name)
    end makeSelection

    override def withPos(pos: SourcePosition): Select = Select(qualifier, name)(selectOwner)(pos)
  end Select

  /** Synthetic outer selection */
  final case class SelectOuter(qualifier: TermTree, levels: Int)(tpe: Type)(pos: SourcePosition) extends TermTree(pos):
    protected final def calculateType(using Context): TermType = tpe

    override def withPos(pos: SourcePosition): SelectOuter = SelectOuter(qualifier, levels)(tpe)(pos)
  end SelectOuter

  /** `qual.this` */
  final case class This(qualifier: TypeIdent)(pos: SourcePosition) extends TermTree(pos) {
    override protected def computeAsTypePrefix: NonEmptyPrefix =
      qualifier.toPrefix match
        case pkg: PackageRef => pkg
        case tref: TypeRef   => ThisType(tref)
        case qualTpe =>
          throw InvalidProgramStructureException(s"Unexpected type for This qualifier $qualifier: $qualTpe")
    end computeAsTypePrefix

    protected final def calculateType(using Context): TermType =
      toTypePrefix.asInstanceOf[TermType]

    override final def withPos(pos: SourcePosition): This = This(qualifier)(pos)
  }

  /** C.super[mix], where qual = C.this */
  final case class Super(qual: TermTree, mix: Option[TypeIdent])(pos: SourcePosition) extends TermTree(pos) {
    override protected def computeAsTypePrefix: NonEmptyPrefix =
      val thistpe = qual.toTypePrefix match
        case qualTpe: ThisType =>
          qualTpe
        case qualTpe =>
          throw InvalidProgramStructureException(s"Unexpected type for Super qualifier $qual: $qualTpe")
      val supertpe = mix.map(_.toType)
      SuperType(thistpe, supertpe)
    end computeAsTypePrefix

    protected final def calculateType(using Context): TermType =
      toTypePrefix.asInstanceOf[SuperType]

    override final def withPos(pos: SourcePosition): Super = Super(qual, mix)(pos)
  }

  /** fun(args) */
  final case class Apply(fun: TermTree, args: List[TermTree])(pos: SourcePosition) extends TermTree(pos):
    import Apply.*

    private val myMethodType: Memo[MethodType] = uninitializedMemo

    protected[tastyquery] def this(
      fun: TermTree,
      args: List[TermTree]
    )(methodType: MethodType | Null, pos: SourcePosition) =
      this(fun, args)(pos)
      if methodType != null then initializeMemo(myMethodType, methodType)

    def methodType(using Context): MethodType = memoized(myMethodType) {
      fun.tpe.widenTermRef match
        case funTpe: MethodType => funTpe
        case funTpe             => throw NonMethodReferenceException(s"application to $funTpe")
    }

    private def instantiateMethodType(args: List[TermType])(using Context): TermType =
      for arg <- args do
        if !arg.isInstanceOf[Type] then
          throw InvalidProgramStructureException(s"application of non-type $arg to $methodType")
      methodType.instantiate(args.asInstanceOf[List[Type]])
    end instantiateMethodType

    protected final def calculateType(using Context): TermType =
      val original = instantiateMethodType(args.map(_.tpe))
      // If the resolved method type is not methodic, then it is the final result type.
      // in this case, check the method part to see if it is a constructor selection.
      // if it is, then the result type is the type of new.
      original match
        case partial: MethodicType => partial // Nothing to do here, it is partially applied.
        case _                     => computeAppliedNewType(fun).getOrElse(original)
    end calculateType

    override final def withPos(pos: SourcePosition): Apply = Apply(fun, args)(pos)

    // for binary compatibility
    protected[tastyquery] def copy(fun: TermTree, args: List[TermTree])(pos: SourcePosition): Apply =
      new Apply(fun, args)(pos)
  end Apply

  object Apply:
    def apply(fun: TermTree, args: List[TermTree])(pos: SourcePosition): Apply =
      new Apply(fun, args)(pos)

    def forSignaturePolymorphic(fun: TermTree, methodType: MethodType, args: List[TermTree])(
      pos: SourcePosition
    ): Apply =
      new Apply(fun, args)(methodType, pos)

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
  final case class TypeApply(fun: TermTree, args: List[TypeTree])(pos: SourcePosition) extends TermTree(pos) {

    private def resolvePolyType(funTpe: TermType, args: List[TypeOrWildcard])(using Context): TermType =
      funTpe.widenTermRef match
        case funTpe: PolyType =>
          funTpe.instantiate(args)
        case tpe =>
          throw NonMethodReferenceException(s"type application of args ${args.mkString} to $tpe")

    protected final def calculateType(using Context): TermType =
      resolvePolyType(fun.tpe, args.map(_.toType))

    override final def withPos(pos: SourcePosition): TypeApply = TypeApply(fun, args)(pos)
  }

  /** new tpt, but no constructor call */
  final case class New(tpt: TypeTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      tpt.toType

    override final def withPos(pos: SourcePosition): New = New(tpt)(pos)
  }

  /** expr : tpt */
  final case class Typed(expr: TermTree, tpt: TypeTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      tpt.toType

    override final def withPos(pos: SourcePosition): Typed = Typed(expr, tpt)(pos)
  }

  /** name = arg, outside a parameter list */
  final case class Assign(lhs: TermTree, rhs: TermTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      defn.UnitType

    override final def withPos(pos: SourcePosition): Assign = Assign(lhs, rhs)(pos)
  }

  /** name = arg, in a parameter list */
  final case class NamedArg(name: UnsignedTermName, arg: TermTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      arg.tpe

    override final def withPos(pos: SourcePosition): NamedArg = NamedArg(name, arg)(pos)
  }

  /** { stats; expr } */
  final case class Block(stats: List[StatementTree], expr: TermTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      expr.tpe

    override final def withPos(pos: SourcePosition): Block = Block(stats, expr)(pos)
  }

  /** if cond then thenp else elsep */
  final case class If(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(pos: SourcePosition)
      extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      OrType(thenPart.tpe.requireType, elsePart.tpe.requireType)

    override final def withPos(pos: SourcePosition): If = If(cond, thenPart, elsePart)(pos)
  }

  final case class InlineIf(cond: TermTree, thenPart: TermTree, elsePart: TermTree)(pos: SourcePosition)
      extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      OrType(thenPart.tpe.requireType, elsePart.tpe.requireType)

    override final def withPos(pos: SourcePosition): InlineIf = InlineIf(cond, thenPart, elsePart)(pos)
  }

  /**  @param meth   A reference to the method.
    *  @param tpt    Defined only if the lambda's type is a SAMtype rather than a function type.
    */
  final case class Lambda(meth: TermReferenceTree, tpt: Option[TypeTree])(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): Type = tpt match
      case Some(tpt) =>
        tpt.toType

      case None =>
        convertMethodTypeToFunctionType(meth.tpe.widenTermRef)
    end calculateType

    private def convertMethodTypeToFunctionType(tpe: TermType)(using Context): Type =
      tpe match
        case tpe: MethodType if tpe.resultType.isInstanceOf[Type] =>
          val paramCount = tpe.paramNames.size
          val functionNTypeRef = defn.FunctionNClass(paramCount).staticRef

          if tpe.isResultDependent then
            val parent = functionNTypeRef.appliedTo(List.fill(paramCount + 1)(defn.AnyType))
            TermRefinement(parent, isStable = false, nme.m_apply, tpe)
          else functionNTypeRef.appliedTo(tpe.paramTypes :+ tpe.resultType.asInstanceOf[Type])

        case tpe: PolyType if tpe.resultType.isInstanceOf[MethodType] =>
          val polyFunctionClass = defn.PolyFunctionClass.getOrElse {
            throw InvalidProgramStructureException(
              s"Found a polymorphic Lambda but PolyFunction is not on the classpath"
            )
          }
          TermRefinement(polyFunctionClass.staticRef, isStable = false, nme.m_apply, tpe)

        case _ =>
          throw InvalidProgramStructureException(s"Unexpected type for the `meth` part of a Lambda: ${tpe.showBasic}")
    end convertMethodTypeToFunctionType

    /** The class symbol of the SAM type of this lambda.
      *
      * A `Lambda` can be considered as an anonymous class of the form `new tpt { ... }`.
      * Given that observation, `samClassSymbol` represents the `parentClasses.head` of that
      * hypothetical anonymous class.
      *
      * When `tpt` is `None`, `samClassSymbol` will be one of the `scala.FunctionN` classes.
      */
    def samClassSymbol(using Context): ClassSymbol =
      tpe.requireType.classSymbol.getOrElse {
        throw InvalidProgramStructureException(s"Non-class type $tpe for SAM type of $this")
      }

    override final def withPos(pos: SourcePosition): Lambda = Lambda(meth, tpt)(pos)
  }

  /** selector match { cases } */
  final case class Match(selector: TermTree, cases: List[CaseDef])(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      cases.map(_.body.tpe.requireType).reduce[Type](OrType(_, _))

    override final def withPos(pos: SourcePosition): Match = Match(selector, cases)(pos)
  }

  final case class InlineMatch(selector: Option[TermTree], cases: List[CaseDef])(pos: SourcePosition)
      extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      cases.map(_.body.tpe.requireType).reduce[Type](OrType(_, _))

    override final def withPos(pos: SourcePosition): InlineMatch = InlineMatch(selector, cases)(pos)
  }

  /** case pattern if guard => body; only appears as child of a Match and Try */
  final case class CaseDef(pattern: PatternTree, guard: Option[TermTree], body: TermTree)(pos: SourcePosition)
      extends Tree(pos) {
    override final def withPos(pos: SourcePosition): CaseDef = CaseDef(pattern, guard, body)(pos)
  }

  sealed abstract class PatternTree(pos: SourcePosition) extends Tree(pos):
    def withPos(pos: SourcePosition): PatternTree
  end PatternTree

  /** Wildcard pattern `_`. */
  final case class WildcardPattern(tpe: Type)(pos: SourcePosition) extends PatternTree(pos):
    override def withPos(pos: SourcePosition): WildcardPattern = WildcardPattern(tpe)(pos)
  end WildcardPattern

  /** Type-test pattern `pat: T`. */
  final case class TypeTest(body: PatternTree, tpt: TypeTree)(pos: SourcePosition) extends PatternTree(pos):
    override final def withPos(pos: SourcePosition): TypeTest = TypeTest(body, tpt)(pos)
  end TypeTest

  /** pattern in {@link Unapply} */
  final case class Bind(name: UnsignedTermName, body: PatternTree, symbol: TermSymbol)(pos: SourcePosition)
      extends PatternTree(pos)
      with DefTree {
    override final def withPos(pos: SourcePosition): Bind = Bind(name, body, symbol)(pos)
  }

  /** tree_1 | ... | tree_n */
  final case class Alternative(trees: List[PatternTree])(pos: SourcePosition) extends PatternTree(pos) {
    override final def withPos(pos: SourcePosition): Alternative = Alternative(trees)(pos)
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
  final case class Unapply(fun: TermTree, implicits: List[TermTree], patterns: List[PatternTree])(pos: SourcePosition)
      extends PatternTree(pos) {
    override final def withPos(pos: SourcePosition): Unapply = Unapply(fun, implicits, patterns)(pos)
  }

  final case class ExprPattern(expr: TermTree)(pos: SourcePosition) extends PatternTree(pos):
    override final def withPos(pos: SourcePosition): ExprPattern = ExprPattern(expr)(pos)
  end ExprPattern

  /** A tree representing a quote pattern `'{ type binding1; ...; body }` or `'[ type binding1; ...; body ]`.
    *
    * The `bindings` contain the list of quote pattern type variable definitions (`TypeTreeBind`s)
    * in the order in which they are defined in the source.
    *
    * @param bindings
    *   Type variable definitions
    * @param body
    *   Quoted pattern (without type variable definitions):
    *   `Left(termTree)` for a term quote pattern `'{ ... }` or
    *   `Right(typeTree)` for a type quote pattern `'[ ... ]`
    * @param quotes
    *   A reference to the given `Quotes` instance in scope
    * @param patternType
    *   The type of the pattern
    */
  final case class QuotePattern(
    bindings: List[TypeTreeBind],
    body: Either[TermTree, TypeTree],
    quotes: TermTree,
    patternType: Type
  )(pos: SourcePosition)
      extends PatternTree(pos) {
    override def withPos(pos: SourcePosition): QuotePattern =
      QuotePattern(bindings, body, quotes, patternType)(pos)
  }

  /** Seq(elems)
    *  @param  tpt  The element type of the sequence.
    */
  final case class SeqLiteral(elems: List[TermTree], elemtpt: TypeTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      defn.SeqTypeOf(elemtpt.toType)

    override final def withPos(pos: SourcePosition): SeqLiteral = SeqLiteral(elems, elemtpt)(pos)
  }

  /** while (cond) { body } */
  final case class While(cond: TermTree, body: TermTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      defn.UnitType

    override final def withPos(pos: SourcePosition): While = While(cond, body)(pos)
  }

  /** throw expr */
  final case class Throw(expr: TermTree)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      defn.NothingType

    override final def withPos(pos: SourcePosition): Throw = Throw(expr)(pos)
  }

  /** try block catch cases finally finalizer */
  final case class Try(expr: TermTree, cases: List[CaseDef], finalizer: Option[TermTree])(pos: SourcePosition)
      extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      cases.foldLeft(expr.tpe.requireType)((prev, caze) => OrType(prev, caze.body.tpe.requireType))

    override final def withPos(pos: SourcePosition): Try = Try(expr, cases, finalizer)(pos)
  }

  final case class Literal(constant: Constant)(pos: SourcePosition) extends TermTree(pos) {
    override protected def computeAsTypePrefix: NonEmptyPrefix =
      ConstantType(constant)

    protected final def calculateType(using Context): TermType =
      ConstantType(constant)

    override final def withPos(pos: SourcePosition): Literal = Literal(constant)(pos)
  }

  final case class Return(expr: Option[TermTree], from: TermSymbol)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      defn.NothingType

    override final def withPos(pos: SourcePosition): Return = Return(expr, from)(pos)
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
    pos: SourcePosition
  ) extends TermTree(pos) {
    override protected def computeAsTypePrefix: NonEmptyPrefix =
      if bindings.nonEmpty then super.computeAsTypePrefix
      else expr.toTypePrefix

    protected final def calculateType(using Context): TermType =
      // TODO? Do we need to do type avoidance on expr using the bindings, like dotc does?
      expr.tpe

    override final def withPos(pos: SourcePosition): Inlined = Inlined(expr, caller, bindings)(pos)
  }

  /** A tree representing a quote `'{ body }`.
    *
    * @param body
    *   The tree that was quoted
    * @param bodyType
    *   Explicit type of quoted body, which is the source of truth from which we build the type of the quote
    */
  final case class Quote(body: TermTree, bodyType: Type)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      // `Quotes ?=> Expr[bodyType]`
      defn.ContextFunction1Class.staticRef.appliedTo(
        List(defn.QuotesClass.staticRef, defn.QuotedExprClass.staticRef.appliedTo(bodyType))
      )
    end calculateType

    override final def withPos(pos: SourcePosition): Quote =
      Quote(body, bodyType)(pos)
  }

  /** A tree representing a splice `${ expr }`.
    *
    * @param expr
    *   The tree that was spliced
    */
  final case class Splice(expr: TermTree, spliceType: Type)(pos: SourcePosition) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      spliceType

    override final def withPos(pos: SourcePosition): Splice =
      Splice(expr, spliceType)(pos)
  }

  /** A tree representing a pattern splice `${ pattern }`, `$ident` or `$ident(args*)` in a quote pattern.
    *
    * Parser will only create `${ pattern }` and `$ident`, hence they will not have args.
    * While typing, the `$ident(args*)` the args are identified and desugared into a `SplicePattern`
    * containing them.
    *
    * `SplicePattern` can only be contained within a `QuotePattern`.
    *
    * @param pattern
    *   The pattern that was spliced
    * @param targs
    *   The type arguments of the splice (the HOAS arguments)
    * @param args
    *   The arguments of the splice (the HOAS arguments)
    * @param spliceType
    *   The type of the splice, i.e., of this tree
    */
  final case class SplicePattern(pattern: PatternTree, targs: List[TypeTree], args: List[TermTree], spliceType: Type)(
    pos: SourcePosition
  ) extends TermTree(pos) {
    protected final def calculateType(using Context): TermType =
      spliceType

    override final def withPos(pos: SourcePosition): SplicePattern =
      SplicePattern(pattern, targs, args, spliceType)(pos)
  }

  // --- TypeTrees ------------------------------------------------------------

  sealed abstract class TypeArgTree(pos: SourcePosition) extends Tree(pos):
    def withPos(pos: SourcePosition): TypeArgTree

    def toTypeOrWildcard: TypeOrWildcard
  end TypeArgTree

  sealed abstract class TypeTree(pos: SourcePosition) extends TypeArgTree(pos) {
    private val myType: Memo[NonEmptyPrefix] = uninitializedMemo

    protected def calculateType: NonEmptyPrefix

    def withPos(pos: SourcePosition): TypeTree

    final def toPrefix: NonEmptyPrefix = memoized(myType) {
      calculateType
    }

    final def toType: Type = toPrefix.requireType

    final def toTypeOrWildcard: Type = toType
  }

  final case class TypeIdent(name: TypeName)(tpe: NonEmptyPrefix)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: NonEmptyPrefix =
      tpe

    override final def withPos(pos: SourcePosition): TypeIdent = TypeIdent(name)(tpe)(pos)
  }

  final case class TypeWrapper(tp: NonEmptyPrefix)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: NonEmptyPrefix = tp

    override final def withPos(pos: SourcePosition): TypeWrapper = TypeWrapper(tp)(pos)
  }

  /** ref.type */
  final case class SingletonTypeTree(ref: TermTree)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: NonEmptyPrefix =
      ref.toTypePrefix

    override final def withPos(pos: SourcePosition): SingletonTypeTree = SingletonTypeTree(ref)(pos)
  }

  type RefinementMemberDef = TypeMember | ValOrDefDef

  final case class RefinedTypeTree(
    underlying: TypeTree,
    refinements: List[RefinementMemberDef],
    refinedCls: ClassSymbol
  )(pos: SourcePosition)
      extends TypeTree(pos) {

    override protected def calculateType: Type =
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

    private def makeRefinedBounds(name: TypeName, rhs: TypeDefinitionTree): TypeBounds =
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

    override final def withPos(pos: SourcePosition): RefinedTypeTree =
      RefinedTypeTree(underlying, refinements, refinedCls)(pos)
  }

  /** => T */
  final case class ByNameTypeTree(result: TypeTree)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: Type =
      ByNameType(result.toType)

    override final def withPos(pos: SourcePosition): ByNameTypeTree = ByNameTypeTree(result)(pos)
  }

  /** tpt[args]
    * TypeBounds[Tree] for wildcard application: tpt[_], tpt[?]
    */
  final case class AppliedTypeTree(tycon: TypeTree, args: List[TypeArgTree])(pos: SourcePosition)
      extends TypeTree(pos) {
    override protected def calculateType: Type =
      AppliedType(tycon.toType, args.map(_.toTypeOrWildcard))

    override final def withPos(pos: SourcePosition): AppliedTypeTree = AppliedTypeTree(tycon, args)(pos)
  }

  /** qualifier#name */
  final case class SelectTypeTree(qualifier: TypeTree, name: TypeName)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: Type =
      TypeRef(qualifier.toPrefix, name)

    override final def withPos(pos: SourcePosition): SelectTypeTree = SelectTypeTree(qualifier, name)(pos)
  }

  /** qualifier.name */
  final case class TermRefTypeTree(qualifier: TermTree, name: TermName)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: NonEmptyPrefix =
      NamedType.possibleSelFromPackage(qualifier.toTypePrefix, name)

    override final def withPos(pos: SourcePosition): TermRefTypeTree = TermRefTypeTree(qualifier, name)(pos)
  }

  /** arg @annot */
  final case class AnnotatedTypeTree(tpt: TypeTree, annotation: TermTree)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: Type =
      AnnotatedType(tpt.toType, Annotation(annotation))

    override final def withPos(pos: SourcePosition): AnnotatedTypeTree = AnnotatedTypeTree(tpt, annotation)(pos)
  }

  /** [bound] selector match { cases } */
  final case class MatchTypeTree(bound: TypeTree, selector: TypeTree, cases: List[TypeCaseDef])(pos: SourcePosition)
      extends TypeTree(pos) {
    override protected def calculateType: Type =
      MatchType(bound.toType, selector.toType, cases.map(_.toMatchTypeCase))

    override final def withPos(pos: SourcePosition): MatchTypeTree = MatchTypeTree(bound, selector, cases)(pos)
  }

  final case class TypeCaseDef(pattern: TypeTree, body: TypeTree)(pos: SourcePosition) extends Tree(pos):
    def withPos(pos: SourcePosition): TypeCaseDef = TypeCaseDef(pattern, body)(pos)

    private[Trees] def toMatchTypeCase: MatchTypeCase =
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

  final case class TypeTreeBind(name: TypeName, body: TypeDefinitionTree, symbol: LocalTypeParamSymbol)(
    pos: SourcePosition
  ) extends TypeTree(pos)
      with DefTree {
    override protected def calculateType: Type =
      TypeRef(NoPrefix, symbol)

    override final def withPos(pos: SourcePosition): TypeTreeBind = TypeTreeBind(name, body, symbol)(pos)
  }

  final case class WildcardTypeArgTree(bounds: TypeBoundsTree)(pos: SourcePosition) extends TypeArgTree(pos) {
    private val myTypeOrWildcard: Memo[WildcardTypeArg] = uninitializedMemo

    def toTypeOrWildcard: TypeOrWildcard = memoized(myTypeOrWildcard) {
      WildcardTypeArg(bounds.toTypeBounds)
    }

    override final def withPos(pos: SourcePosition): WildcardTypeArgTree =
      WildcardTypeArgTree(bounds)(pos)
  }

  final case class TypeLambdaTree(tparams: List[TypeParam], body: TypeTree)(pos: SourcePosition) extends TypeTree(pos) {
    override protected def calculateType: Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), body.toType))

    override final def withPos(pos: SourcePosition): TypeLambdaTree = TypeLambdaTree(tparams, body)(pos)
  }

  final case class TypeBindingsTree(bindings: List[TypeMember], body: TypeTree)(pos: SourcePosition)
      extends TypeTree(pos):
    override protected def calculateType: Type = body.toType

    override def withPos(pos: SourcePosition): TypeBindingsTree = TypeBindingsTree(bindings, body)(pos)
  end TypeBindingsTree

  /** A tree representing an inlined type.
    *
    * @param caller
    *   The toplevel class from which the type was inlined.
    * @param expansion
    *   The expanded type.
    */
  final case class InlinedTypeTree(caller: Option[TypeIdent | SelectTypeTree], expansion: TypeTree)(pos: SourcePosition)
      extends TypeTree(pos):
    override protected def calculateType: NonEmptyPrefix =
      expansion.toPrefix

    override final def withPos(pos: SourcePosition): InlinedTypeTree = InlinedTypeTree(caller, expansion)(pos)
  end InlinedTypeTree

  // --- TypeDefinitionTrees and TypeBoundsTrees ------------------------------

  sealed abstract class TypeDefinitionTree(pos: SourcePosition) extends Tree(pos):
    def withPos(pos: SourcePosition): TypeDefinitionTree
  end TypeDefinitionTree

  sealed abstract class TypeBoundsTree(pos: SourcePosition) extends TypeDefinitionTree(pos):
    def withPos(pos: SourcePosition): TypeBoundsTree

    def toTypeBounds: TypeBounds
  end TypeBoundsTree

  final case class InferredTypeBoundsTree(bounds: TypeBounds)(pos: SourcePosition) extends TypeBoundsTree(pos):
    def withPos(pos: SourcePosition): InferredTypeBoundsTree =
      InferredTypeBoundsTree(bounds)(pos)

    def toTypeBounds: TypeBounds = bounds
  end InferredTypeBoundsTree

  final case class ExplicitTypeBoundsTree(low: TypeTree, high: TypeTree)(pos: SourcePosition)
      extends TypeBoundsTree(pos):
    def withPos(pos: SourcePosition): ExplicitTypeBoundsTree =
      ExplicitTypeBoundsTree(low, high)(pos)

    def toTypeBounds: TypeBounds =
      AbstractTypeBounds(low.toType, high.toType)
  end ExplicitTypeBoundsTree

  final case class TypeAliasDefinitionTree(alias: TypeTree)(pos: SourcePosition) extends TypeDefinitionTree(pos):
    def withPos(pos: SourcePosition): TypeAliasDefinitionTree =
      TypeAliasDefinitionTree(alias)(pos)
  end TypeAliasDefinitionTree

  final case class OpaqueTypeAliasDefinitionTree(bounds: TypeBoundsTree, alias: TypeTree)(pos: SourcePosition)
      extends TypeDefinitionTree(pos):
    def withPos(pos: SourcePosition): OpaqueTypeAliasDefinitionTree =
      OpaqueTypeAliasDefinitionTree(bounds, alias)(pos)
  end OpaqueTypeAliasDefinitionTree

  final case class PolyTypeDefinitionTree(tparams: List[TypeParam], body: TypeDefinitionTree)(pos: SourcePosition)
      extends TypeDefinitionTree(pos):
    def withPos(pos: SourcePosition): PolyTypeDefinitionTree =
      PolyTypeDefinitionTree(tparams, body)(pos)

    private[tastyquery] def integrateInto(resultType: Type): Type =
      TypeLambda.fromParams(tparams)(tl => tl.integrate(tparams.map(_.symbol), resultType))
  end PolyTypeDefinitionTree

  final case class NamedTypeBoundsTree(name: TypeName, bounds: TypeBounds)(pos: SourcePosition)
      extends TypeDefinitionTree(pos):
    override final def withPos(pos: SourcePosition): NamedTypeBoundsTree =
      NamedTypeBoundsTree(name, bounds)(pos)
  end NamedTypeBoundsTree

}
