package tastyquery

import java.io.{StringWriter, Writer}

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Modifiers.*
import tastyquery.Names.*
import tastyquery.Signatures.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

private[tastyquery] object Printers:
  def withWriterToString(printingOp: Writer => Unit): String =
    val output = new StringWriter
    printingOp(output)
    output.toString()
  end withWriterToString

  class Printer(out: Writer):
    protected def printPrefix(prefix: Prefix): Unit = prefix match
      case NoPrefix =>
        ()
      case prefix: PackageRef =>
        print(prefix)
        print(".")
      case prefix: TermRef =>
        printPrefix(prefix.prefix)
        print(prefix.name)
        print(".")
      case tpe: TermParamRef =>
        print(tpe.paramName)
        print(".")
      case tpe: ThisType =>
        print(tpe.tref.name)
        print(".this.")
      case tpe: SuperType =>
        print(tpe.thistpe.tref.name)
        print(".super")
        for explicitSupertpe <- tpe.explicitSupertpe do
          print("[")
          print(explicitSupertpe)
          print("]")
        print(".")
      case tpe: RecThis =>
        print(tpe.binder.debugID)
        print(".")
      case prefix: Type =>
        print(prefix)
        print("#")
    end printPrefix

    def print(tpe: TypeMappable): Unit = tpe match
      case NoPrefix =>
        print("ε") // U+03B5 Greek Small Letter Epsilon
      case tpe: PackageRef =>
        print(tpe.fullyQualifiedName.toString())

      case tpe: NothingType =>
        print("Nothing")
      case tpe: AnyKindType =>
        print("AnyKind")
      case tpe @ (_: TermRef | _: TermParamRef | _: ThisType | _: SuperType | _: RecThis) =>
        printPrefix(tpe)
        print("type")
      case tpe: TypeRef =>
        printPrefix(tpe.prefix)
        print(tpe.name)
      case tpe: ConstantType =>
        print(tpe.value)
      case tpe: AppliedType =>
        print(tpe.tycon)
        print("[")
        printCommaSeparatedList(tpe.args)(print(_))
        print("]")
      case tpe: FlexibleType =>
        print(tpe.nonNullableType)
        print("?")
      case tpe: ByNameType =>
        print("=> ")
        print(tpe.resultType)
      case tpe: RepeatedType =>
        print(tpe.elemType)
        print("*")
      case tpe: TypeLambda =>
        print("([")
        printCommaSeparatedList(tpe.typeLambdaParams)(print(_))
        print("] =>> ")
        print(tpe.resultType)
        print(")")
      case tpe: TypeParamRef =>
        print(tpe.paramName)
      case tpe: AnnotatedType =>
        print("(")
        print(tpe.annotation)
        print(" ")
        print(tpe.typ)
        print(")")
      case tpe: TypeRefinement =>
        print("(")
        print(tpe.parent)
        print(" { type ")
        print(tpe.refinedName)
        print(tpe.refinedBounds)
        print(" })")
      case tpe: TermRefinement =>
        print("(")
        print(tpe.parent)
        if tpe.isStable then print(" { val ")
        else print(" { def ")
        print(tpe.refinedName)
        if tpe.refinedType.isInstanceOf[Type] then print(": ")
        print(tpe.refinedType)
        print(" })")
      case tpe: RecType =>
        print("{ ")
        print(tpe.debugID)
        print(" => ")
        print(tpe.parent)
        print(" }")
      case tpe: MatchType =>
        print("(")
        print(tpe.scrutinee)
        print(" match")
        if !isSyntacticAny(tpe.bound) then
          print(" <: ")
          print(tpe.bound)
        printBlock(tpe.cases) { caze =>
          print("case ")
          print(caze.pattern)
          print(" => ")
          print(caze.result)
        }
        print(")")
      case tpe: SkolemType =>
        print("(\u2203") // ∃ U+2203 There Exists
        print(tpe.debugID)
        print(": ")
        print(tpe.tpe)
        print(")")
      case tpe: OrType =>
        print("(")
        print(tpe.first)
        print(" | ")
        print(tpe.second)
        print(")")
      case tpe: AndType =>
        print("(")
        print(tpe.first)
        print(" & ")
        print(tpe.second)
        print(")")
      case tpe: CustomTransientGroundType =>
        print("<")
        print(tpe.toString())
        print(">")

      case tpe: MethodType =>
        print("(")
        if tpe.isContextual then print("using ")
        else if tpe.isImplicit then print("implicit ")
        printCommaSeparatedList(tpe.paramNames.zip(tpe.paramTypes)) { (paramName, paramType) =>
          print(paramName)
          print(": ")
          print(paramType)
        }
        print(")")
        print(tpe.resultType)
      case tpe: PolyType =>
        print("[")
        printCommaSeparatedList(tpe.paramNames.zip(tpe.paramTypeBounds)) { (paramName, paramTypeBounds) =>
          print(paramName)
          print(paramTypeBounds)
        }
        print("]")
        print(tpe.resultType)

      case tpe: WildcardTypeArg =>
        print("?")
        print(tpe.bounds)

      case TypeAlias(alias) =>
        print(" = ")
        print(alias)
      case AbstractTypeBounds(low, high) =>
        if !isSyntacticNothing(low) then
          print(" >: ")
          print(low)
        if !isSyntacticAny(high) then
          print(" <: ")
          print(high)
    end print

    final def printAnyTree(tree: Tree): Unit = tree match
      case tree: TopLevelTree        => printTopLevel(tree)
      case tree: TypeTree            => print(tree)
      case tree: PatternTree         => print(tree)
      case tree: TypeDefinitionTree  => print(tree)
      case tree: Template            => print(tree)
      case tree: ImportIdent         => print(tree.name)
      case tree: ImportSelector      => print(tree)
      case tree: CaseDef             => print(tree)
      case tree: TypeCaseDef         => print(tree)
      case tree: WildcardTypeArgTree => print(tree)
      case tree: SelfDef             => print(tree)
    end printAnyTree

    def printTopLevel(tree: TopLevelTree): Unit = tree match
      case PackageDef(sym, stats) =>
        print("package ")
        print(sym.displayFullName)
        printBlock(stats)(printTopLevel(_))

      case tree: StatementTree =>
        print(tree)
    end printTopLevel

    def print(tree: StatementTree): Unit = tree match
      case Import(expr, selectors) =>
        print("import ")
        print(expr)
        print(".")
        selectors match
          case selector :: Nil =>
            print(selector)
          case _ =>
            print("{")
            printCommaSeparatedList(selectors)(print(_))
            print("}")

      case Export(expr, selectors) =>
        print("export ")
        print(expr)
        print(".")
        selectors match
          case selector :: Nil =>
            print(selector)
          case _ =>
            print("{")
            printCommaSeparatedList(selectors)(print(_))
            print("}")

      case ClassDef(name, rhs, symbol) =>
        if symbol.isTrait then print("trait ")
        else if symbol.isModuleClass then print("object class ")
        else print("class ")

        print(name)
        print(rhs)

      case TypeMember(name, rhs, symbol) =>
        print("type ")
        print(name)
        print(rhs)

      case TypeParam(name, bounds, symbol) =>
        symbol match
          case symbol: ClassTypeParamSymbol => print(symbol.declaredVariance)
          case symbol: LocalTypeParamSymbol => ()
        print(name)
        print(bounds)

      case ValDef(name, tpt, rhs, symbol) =>
        symbol.kind match
          case TermSymbolKind.Module  => print("object lazy val ")
          case TermSymbolKind.Val     => print("val ")
          case TermSymbolKind.LazyVal => print("lazy val ")
          case TermSymbolKind.Var     => print("var ")
          case TermSymbolKind.Def     => print("def ") // should not happen
        print(name)
        print(": ")
        print(tpt)
        for r <- rhs do
          print(" = ")
          print(r)

      case DefDef(name, paramLists, resultTpt, rhs, symbol) =>
        print("def ")
        print(name)

        for paramList <- paramLists do
          paramList match
            case Left(valDefs) =>
              if valDefs.isEmpty then print("()")
              else
                print("(")
                val first = valDefs.head
                if first.symbol.isGivenOrUsing then print("using ")
                else if first.symbol.isImplicit then print("implicit ")
                printCommaSeparatedList(valDefs) { valDef =>
                  print(valDef.name)
                  print(": ")
                  print(valDef.tpt)
                }
                print(")")
            case Right(typeDefs) =>
              print("[")
              printCommaSeparatedList(typeDefs) { typeDef =>
                print(typeDef.name)
                print(typeDef.bounds)
              }
              print("]")
        end for

        print(": ")
        print(resultTpt)

        for body <- rhs do
          print(" = ")
          print(body)

      case Ident(name) =>
        print(name)

      case Select(qualifier, name) =>
        print(qualifier)
        print(".")
        print(name)

      case SelectOuter(qualifier, levels) =>
        print(qualifier)
        for _ <- 0 until levels do print(".<outer>")

      case This(qualifier) =>
        print(qualifier)
        print(".this")

      case Super(qual, optMix) =>
        print(qual)
        print(".super")
        for mix <- optMix do
          print("[")
          print(mix)
          print("]")

      case tree: Apply =>
        printApplication(tree, hideNew = false)

      case tree: TypeApply =>
        printApplication(tree, hideNew = false)

      case New(tpt) =>
        print("new ")
        print(tpt)

      case Typed(expr, tpt) =>
        print("(")
        print(expr)
        print(": ")
        print(tpt)
        print(")")

      case Assign(lhs, rhs) =>
        print(lhs)
        print(" = ")
        print(rhs)

      case NamedArg(name, arg) =>
        print(name)
        print(" = ")
        print(arg)

      case Block(stats, expr) =>
        printBlock(stats, expr)(print(_))

      case If(cond, thenPart, elsePart) =>
        print("if ")
        print(cond)
        print(" then ")
        print(thenPart)
        print(" else ")
        print(elsePart)

      case InlineIf(cond, thenPart, elsePart) =>
        print("inline ")
        print(If(cond, thenPart, elsePart)(tree.pos))

      case Lambda(meth, tpt) =>
        print("(")
        print(meth)
        print(": ")
        tpt match
          case Some(tpt) => print(tpt)
          case None      => print("<function>")
        print(")")

      case Match(selector, cases) =>
        print("(")
        print(selector)
        print(" match")
        printBlock(cases)(print(_))
        print(")")

      case InlineMatch(selector, cases) =>
        print("(inline ")
        selector match
          case Some(sel) => print(sel)
          case None      => print("_")
        print(" match")
        printBlock(cases)(print(_))
        print(")")

      case SeqLiteral(elems, elemtpt) =>
        print("[")
        printCommaSeparatedList(elems)(print(_))
        print(": ")
        print(elemtpt)
        print("]")

      case While(cond, body) =>
        print("while ")
        print(cond)
        print(" do ")
        print(body)

      case Throw(expr) =>
        print("throw ")
        print(expr)

      case Try(expr, cases, finalizer) =>
        print("try ")
        print(expr)
        if cases.nonEmpty then
          print(" catch")
          printBlock(cases)(print(_))
        for fin <- finalizer do
          print(" finally ")
          print(fin)

      case Literal(constant) =>
        print(constant)

      case Return(expr, from) =>
        expr match
          case Some(expr) =>
            print("return ")
            print(expr)
          case None =>
            print("return")

      case Inlined(expr, caller, bindings) =>
        for c <- caller do
          print("<inlined: ")
          print(c)
          print(">")
        printBlock(bindings, expr)(print(_))

      case Quote(body, bodyType) =>
        print("'[")
        print(bodyType)
        print("]")
        printBlock(Nil, body)(print(_))

      case Splice(expr, spliceType) =>
        print("$[")
        print(spliceType)
        print("]")
        printBlock(Nil, expr)(print(_))

      case SplicePattern(pattern, targs, args, spliceType) =>
        print("$[")
        print(spliceType)
        print("]")
        print(pattern)
        if targs.nonEmpty then
          print("[")
          printCommaSeparatedList(targs)(print(_))
          print("]")
        if args.nonEmpty then
          print("(")
          printCommaSeparatedList(args)(print(_))
          print(")")
    end print

    def print(caze: CaseDef): Unit =
      print("case ")
      print(caze.pattern)
      for guard <- caze.guard do
        print(" if ")
        print(guard)
      print(" => ")
      print(caze.body)
    end print

    def printApplication(tree: TermTree, hideNew: Boolean): Unit = tree match
      case Apply(fun, args) =>
        printApplication(fun, hideNew)
        print("(")
        printCommaSeparatedList(args)(print(_))
        print(")")

      case TypeApply(fun, args) =>
        printApplication(fun, hideNew)
        print("[")
        printCommaSeparatedList(args)(print(_))
        print("]")

      case Select(New(tpt), SignedName(nme.Constructor, _, _)) =>
        if !hideNew then print("new ")
        print(tpt)

      case Select(New(tpt), nme.Constructor) =>
        if !hideNew then print("new ")
        print(tpt)

      case Select(qual, SignedName(underlying, _, _)) =>
        print(qual)
        print(".")
        print(underlying)

      case New(tpt) if hideNew =>
        print(tpt)

      case _ =>
        print(tree)
    end printApplication

    def print(tree: ImportSelector): Unit =
      if tree.isGiven then
        tree.bound match
          case Some(bound) =>
            print("given ")
            print(bound)
          case None =>
            print("given")
      else
        print(tree.name)
        for renamed <- tree.renamed do
          print(" as ")
          print(renamed.name)
    end print

    def print(tree: Template): Unit =
      val Template(constr, parents, self, body) = tree

      val (typeParams, otherStats) = body.partition(_.isInstanceOf[TypeParam])

      if typeParams.nonEmpty then
        print("[")
        printCommaSeparatedList(typeParams)(print(_))
        print("]")
      end if

      print(" extends ")
      parents.head match
        case parent: TermTree => printApplication(parent, hideNew = true)
        case parent: TypeTree => print(parent)
      for parent <- parents.tail do
        print(" with ")
        parent match
          case parent: TermTree => printApplication(parent, hideNew = true)
          case parent: TypeTree => print(parent)
      end for

      printBlock[SelfDef | StatementTree](self.toList ::: constr :: otherStats) { stat =>
        stat match
          case stat: SelfDef       => print(stat)
          case stat: StatementTree => print(stat)
      }
    end print

    def print(tree: SelfDef): Unit =
      print(tree.name)
      print(": ")
      print(tree.tpt)
      print(" =>")
    end print

    def print(tree: PatternTree): Unit = tree match
      case WildcardPattern(tpe) =>
        print("_")

      case TypeTest(body, tpt) =>
        print(body)
        print(": ")
        print(tpt)

      case Bind(name, body, symbol) =>
        print(name)
        print(" @ ")
        print(body)

      case Alternative(trees) =>
        print(trees.head)
        for tree <- trees do
          print(" | ")
          print(tree)

      case Unapply(fun, implicits, patterns) =>
        fun match
          case Select(extractor, SignedName(nme.m_unapply, _, _)) =>
            print(extractor)
          case _ =>
            printApplication(fun, hideNew = false)
        print("(")
        printCommaSeparatedList(patterns)(print(_))
        print(")")
        if implicits.nonEmpty then
          print("(")
          printCommaSeparatedList(implicits)(print(_))
          print(")")

      case ExprPattern(expr) =>
        print(expr)

      case QuotePattern(bindings, body, quotes, patternType) =>
        print("'<")
        print(quotes)
        print(">")
        body match
          case Left(termBody) =>
            print("{ ")
            for binding <- bindings do
              print(binding)
              print("; ")
            print(termBody)
            print(" }")
          case Right(typeBody) =>
            print("[ ")
            for binding <- bindings do
              print(binding)
              print("; ")
            print(typeBody)
            print(" ]")
    end print

    def print(tree: TypeTree): Unit = tree match
      case TypeIdent(name) =>
        print(name)

      case TypeWrapper(tp) =>
        print(tp)

      case SingletonTypeTree(ref) =>
        print(ref)
        print(".type")

      case RefinedTypeTree(underlying, refinements, refinedCls) =>
        print("(")
        print(underlying)
        printBlock(refinements) { refinement =>
          print(refinement)
        }
        print(")")

      case ByNameTypeTree(result) =>
        print("=> ")
        print(result)

      case AppliedTypeTree(tycon, args) =>
        print(tycon)
        print("[")
        printCommaSeparatedList(args) { arg =>
          arg match
            case arg: TypeTree            => print(arg)
            case arg: WildcardTypeArgTree => print(arg)
        }
        print("]")

      case SelectTypeTree(qualifier, name) =>
        print(qualifier)
        print(".")
        print(name)

      case TermRefTypeTree(qualifier, name) =>
        print(qualifier)
        print(".")
        print(name)

      case AnnotatedTypeTree(tpt, annotation) =>
        print("(")
        print(tpt)
        print(" ")
        print(annotation)
        print(")")

      case MatchTypeTree(bound, selector, cases) =>
        print("(")
        print(selector)
        print(" match")
        if !isSyntacticAny(bound.toType) then
          print(" <: ")
          print(bound)
        printBlock(cases)(print(_))
        print(")")

      case TypeTreeBind(name, body, symbol) =>
        print(name)

      case TypeLambdaTree(tparams, body) =>
        print("([")
        printCommaSeparatedList(tparams)(print(_))
        print("] =>> ")
        print(body)
        print(")")

      case TypeBindingsTree(bindings, body) =>
        printBlock[TypeMember | TypeTree](bindings, body) { elem =>
          elem match
            case elem: TypeMember => print(elem)
            case elem: TypeTree   => print(elem)
        }

      case InlinedTypeTree(caller, expansion) =>
        for c <- caller do
          print("<inlined: ")
          print(c)
          print(">")
        print(expansion)
    end print

    def print(tree: WildcardTypeArgTree): Unit =
      print("?")
      print(tree.bounds)
    end print

    def print(tree: TypeCaseDef): Unit =
      print("case ")
      print(tree.pattern)
      print(" => ")
      print(tree.body)
    end print

    def print(tree: TypeDefinitionTree): Unit = tree match
      case InferredTypeBoundsTree(bounds) =>
        print(bounds)

      case ExplicitTypeBoundsTree(low, high) =>
        if !isSyntacticNothing(low.toType) then
          print(" >: ")
          print(low)
        if !isSyntacticAny(high.toType) then
          print(" <: ")
          print(high)

      case TypeAliasDefinitionTree(alias) =>
        alias match
          case MatchTypeTree(bound, selector, cases) =>
            if !isSyntacticAny(bound.toType) then
              print(" <: ")
              print(bound)
            print(" = ")
            print(selector)
            print(" match")
            printBlock(cases) { caze =>
              print("case ")
              print(caze.pattern)
              print(" => ")
              print(caze.body)
            }
          case _ =>
            print(" = ")
            print(alias)

      case OpaqueTypeAliasDefinitionTree(bounds, alias) =>
        print(bounds)
        print(alias)

      case PolyTypeDefinitionTree(tparams, body) =>
        print("[")
        printCommaSeparatedList(tparams)(print(_))
        print("]")
        print(body)

      case NamedTypeBoundsTree(name, bounds) =>
        print(name)
    end print

    def printCommaSeparatedList[A](elems: List[A])(printElem: A => Unit): Unit =
      if elems.nonEmpty then
        printElem(elems.head)
        for elem <- elems.tail do
          print(", ")
          printElem(elem)
    end printCommaSeparatedList

    final def printBlock[A](initElems: List[A], lastElem: A)(printElem: A => Unit): Unit =
      printBlock(initElems :+ lastElem)(printElem)

    def printBlock[A](elems: List[A])(printElem: A => Unit): Unit =
      if elems.isEmpty then print(" {}")
      else
        print(" { ")
        printElem(elems.head)
        for elem <- elems.tail do
          print("; ")
          printElem(elem)
        print(" }")
    end printBlock

    def print(name: Name): Unit =
      print(name.toString())
    end print

    def print(constant: Constant): Unit =
      constant.tag match
        case Constants.UnitTag =>
          print("()")
        case Constants.ByteTag =>
          print(s"${constant.value}b") // not valid syntax
        case Constants.ShortTag =>
          print(s"${constant.value}s") // not valid syntax
        case Constants.CharTag =>
          print("'")
          printEscaped(constant.charValue.toString)
          print("'")
        case Constants.LongTag =>
          print(s"${constant.value}L")
        case Constants.FloatTag =>
          print(s"${constant.value}f")
        case Constants.StringTag =>
          print("\"")
          printEscaped(constant.stringValue)
          print("\"")
        case Constants.NullTag =>
          print("null")
        case Constants.ClazzTag =>
          print("classOf[")
          print(constant.typeValue)
          print("]")
        case _ =>
          print(constant.value.toString())
    end print

    def printEscaped(str: String): Unit =
      for c <- str do
        c match
          case '\''                      => print("\\'")
          case '\"'                      => print("\\\"")
          case '\n'                      => print("\\n")
          case _ if c >= ' ' && c < 0x80 => print(c.toString())
          case _                         => print("\\u%04x".format(c.toInt))
    end printEscaped

    def print(annot: Annotation): Unit =
      print("@")
      printApplication(annot.tree, hideNew = true)

    def print(tparam: TypeConstructorParam): Unit =
      print(tparam.declaredVariance)
      print(tparam.name)
      print(tparam.declaredBounds)
    end print

    def print(variance: Variance): Unit =
      variance match
        case Variance.Invariant     => ()
        case Variance.Covariant     => println("+")
        case Variance.Contravariant => println("-")

    def print(i: Int): Unit =
      print(i.toString())

    def print(str: String): Unit =
      out.write(str)
  end Printer

  /** A `Printer` that prints blocks with line separators and indentation. */
  class MultilinePrinter(out: Writer) extends Printer(out):
    private var spaces: String = "                                        " // 40 spaces
    private var currentIndent: Int = 0

    private final val IndentWidth = 2

    protected final def printNewLine(): Unit =
      print("\n")
      out.write(spaces, 0, currentIndent)

    protected final def printNewLineAndIndent(): Unit =
      currentIndent += IndentWidth
      if spaces.length() < currentIndent then spaces = spaces + spaces
      printNewLine()

    protected final def printNewLineAndOutdent(): Unit =
      if currentIndent < IndentWidth then throw IllegalStateException("Trying to outdent more than indent")
      currentIndent -= IndentWidth
      printNewLine()

    override def printBlock[A](elems: List[A])(printElem: A => Unit): Unit =
      if elems.isEmpty then print(" {}")
      else
        print(" {")
        printNewLineAndIndent()
        printElem(elems.head)
        for elem <- elems.tail do
          printNewLine()
          printElem(elem)
        printNewLineAndOutdent()
        print("}")
    end printBlock
  end MultilinePrinter

  private def isSyntacticNothing(tpe: Type): Boolean = tpe match
    case tpe: TypeRef => tpe.name == tpnme.Nothing && isScalaPackageRef(tpe.prefix)
    case _            => false
  end isSyntacticNothing

  private def isSyntacticAny(tpe: Type): Boolean = tpe match
    case tpe: TypeRef => tpe.name == tpnme.Any && isScalaPackageRef(tpe.prefix)
    case _            => false
  end isSyntacticAny

  private def isScalaPackageRef(prefix: Prefix): Boolean = prefix match
    case prefix: PackageRef =>
      prefix.fullyQualifiedName.path match
        case nme.scalaPackageName :: Nil => true
        case _                           => false
    case _ =>
      false
end Printers
