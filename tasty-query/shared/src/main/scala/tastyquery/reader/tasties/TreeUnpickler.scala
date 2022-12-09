package tastyquery.reader.tasties

import scala.annotation.tailrec

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.NotGiven

import dotty.tools.tasty.TastyReader
import dotty.tools.tasty.TastyBuffer.*
import dotty.tools.tasty.TastyFormat.*

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Spans.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import TastyUnpickler.NameTable

private[tasties] sealed trait AbstractCaseDefFactory[CaseDefType]
private[tasties] case object CaseDefFactory extends AbstractCaseDefFactory[CaseDef]
private[tasties] case object TypeCaseDefFactory extends AbstractCaseDefFactory[TypeCaseDef]

private[tasties] class TreeUnpickler(
  protected val reader: TastyReader,
  nameAtRef: NameTable,
  posUnpicklerOpt: Option[PositionUnpickler]
)(using Context) {
  import TreeUnpickler.*

  private val recursiveTypeAtAddr = mutable.Map.empty[Addr, Type]

  private val sharedTypesCache = mutable.Map.empty[Addr, Type]

  def unpickle(filename: String): List[Tree] =
    val fileContext = new LocalContext(filename, defn.RootPackage, mutable.HashMap.empty, Map.empty)

    @tailrec
    def read(acc: ListBuffer[Tree]): List[Tree] =
      acc += readTopLevelStat(using fileContext)
      if !reader.isAtEnd then read(acc) else acc.toList

    fork.enterSymbols()(using fileContext)
    val result = read(new ListBuffer[Tree])

    // Check that all the Symbols we created have been completed
    for sym <- fileContext.allRegisteredSymbols do sym.checkCompleted()

    result
  end unpickle

  private def enterSymbols()(using LocalContext): Unit =
    while !reader.isAtEnd do createSymbols()

  /* This method walks a TASTy file and creates all symbols in it.
   *
   * This is useful for forward references. Example: type parameters in the following case:
   * class ExampleClass[T1 <: T2, T2]
   * The example is equally applicable to methods, which can be arbitrarily nested.
   * The alternative is to create a symbol when we encounter a forward reference, but it is hard to
   * keep track of the owner in this case.
   * */
  private def createSymbols()(using LocalContext): Unit = {
    val start = reader.currentAddr
    val tag = reader.readByte()
    tag match {
      // ---------- tags that trigger symbol creation -----------------------------------
      case PACKAGE =>
        val end = reader.readEnd()
        val pid = readPotentiallyShared({
          assert(reader.readByte() == TERMREFpkg, posErrorMsg)
          ctx.findPackageFromRootOrCreate(readFullyQualifiedName)
        })
        reader.until(end)(createSymbols()(using localCtx.withOwner(pid)))
      case TYPEDEF =>
        val end = reader.readEnd()
        val name = readName.toTypeName
        val tag = reader.nextByte
        val newOwner =
          if tag == TEMPLATE then ClassSymbol.create(name, localCtx.owner)
          else TypeMemberSymbol.create(name, localCtx.owner)
        localCtx.registerSym(start, newOwner)
        readSymbolModifiers(newOwner, tag, end)
        reader.until(end)(createSymbols()(using localCtx.withOwner(newOwner)))
      case DEFDEF | VALDEF | PARAM =>
        val end = reader.readEnd()
        val name = readName
        val newSymbol = TermSymbol.create(name, localCtx.owner)
        localCtx.registerSym(start, newSymbol)
        readSymbolModifiers(newSymbol, tag, end)
        reader.until(end)(createSymbols()(using localCtx.withOwner(newSymbol)))
      case TYPEPARAM =>
        val end = reader.readEnd()
        val name = readName.toTypeName
        val newSymbol =
          if localCtx.owner.isClass then ClassTypeParamSymbol.create(name, localCtx.owner.asClass)
          else LocalTypeParamSymbol.create(name, localCtx.owner)
        localCtx.registerSym(start, newSymbol)
        readSymbolModifiers(newSymbol, tag, end)
        reader.until(end)(createSymbols()(using localCtx.withOwner(newSymbol)))
      case BIND =>
        val end = reader.readEnd()
        val name = readName
        val sym =
          if tagFollowShared == TYPEBOUNDS then LocalTypeParamSymbol.create(name.toTypeName, localCtx.owner)
          else TermSymbol.create(name, localCtx.owner)
        localCtx.registerSym(start, sym)
        sym.withFlags(Case, None)
        // bind is never an owner
        reader.until(end)(createSymbols())

      // ---------- tags with potentially nested symbols --------------------------------
      case tag if firstASTTreeTag <= tag && tag < firstNatASTTreeTag => createSymbols()
      case tag if firstNatASTTreeTag <= tag && tag < firstLengthTreeTag =>
        reader.readNat()
        createSymbols()
      case TEMPLATE | APPLY | TYPEAPPLY | SUPER | TYPED | ASSIGN | BLOCK | INLINED | LAMBDA | IF | MATCH | TRY | WHILE |
          REPEATED | ALTERNATIVE | UNAPPLY | REFINEDtpt | APPLIEDtpt | LAMBDAtpt | TYPEBOUNDStpt | ANNOTATEDtpt |
          MATCHtpt | CASEDEF =>
        val end = reader.readEnd()
        reader.until(end)(createSymbols())
      case SELECTin =>
        val end = reader.readEnd()
        readName
        reader.until(end)(createSymbols())
      case RETURN | SELECTouter =>
        val end = reader.readEnd()
        reader.readNat()
        reader.until(end)(createSymbols())

      // ---------- no nested symbols ---------------------------------------------------
      case _ => skipTree(tag)
    }
  }

  private def normalizeFlags(tag: Int, givenFlags: FlagSet, name: Name, rhsIsEmpty: Boolean)(
    using LocalContext
  ): FlagSet =
    var flags = givenFlags
    if tag == DEFDEF then flags |= Method
    if rhsIsEmpty && (tag == VALDEF || tag == DEFDEF) then flags |= Abstract
    if givenFlags.is(Module) then flags |= (if tag == VALDEF then ModuleValCreationFlags else ModuleClassCreationFlags)
    if flags.is(Enum) && !flags.is(Method) && name.isTermName then flags |= StableRealizable
    if localCtx.owner.isClass then
      if tag == PARAM then
        flags |= ParamAccessor
        if !rhsIsEmpty then // param alias
          flags |= Method
    if tag == TYPEPARAM then flags |= TypeParameter
    flags

  private def posErrorMsg(using LocalContext): String = s"at address ${reader.currentAddr} in file ${localCtx.getFile}"
  private def posErrorMsg(atAddr: Addr)(using LocalContext): String = s"at address $atAddr in file ${localCtx.getFile}"

  def spanAt(addr: Addr): Span =
    posUnpicklerOpt match {
      case Some(posUnpickler) =>
        posUnpickler.spanAt(addr)
      case _ =>
        NoSpan
    }

  def span: Span =
    spanAt(reader.currentAddr)

  private def spanSeq(trees: Seq[Tree]): Span = trees.foldLeft(NoSpan)((s, t) => s.union(t.span))
  private def spanSeqT(trees: Seq[TypeTree]): Span = trees.foldLeft(NoSpan)((s, t) => s.union(t.span))

  def forkAt(start: Addr): TreeUnpickler =
    new TreeUnpickler(reader.subReader(start, reader.endAddr), nameAtRef, posUnpicklerOpt)

  def fork: TreeUnpickler =
    forkAt(reader.currentAddr)

  def skipTree(tag: Int): Unit =
    if (tag >= firstLengthTreeTag) reader.goto(reader.readEnd())
    else if (tag >= firstNatASTTreeTag) { reader.readNat(); skipTree() }
    else if (tag >= firstASTTreeTag) skipTree()
    else if (tag >= firstNatTreeTag) reader.readNat()

  def skipTree(): Unit = skipTree(reader.readByte())

  private def skipParams(): Unit =
    while
      val tag = reader.nextByte
      tag == PARAM || tag == TYPEPARAM || tag == EMPTYCLAUSE || tag == SPLITCLAUSE
    do skipTree()

  private def nothingButMods(end: Addr): Boolean =
    reader.currentAddr == end || isModifierTag(reader.nextByte)

  def isSharedTag(tag: Int): Boolean = tag == SHAREDtype || tag == SHAREDterm

  /** The tag at the end of SHAREDtype/term chain */
  def tagFollowShared: Int = {
    val tag = reader.nextByte
    if (isSharedTag(tag)) {
      val lookAhead = fork
      // skip SHAREDtype / SHAREDterm tag, read the address
      lookAhead.reader.readByte()
      val addrShared = lookAhead.reader.readAddr()
      forkAt(addrShared).tagFollowShared
    } else {
      tag
    }
  }

  private def readSymbolModifiers(sym: Symbol, tag: Int, end: Addr)(using LocalContext): Unit =
    val modsReader = fork
    modsReader.skipParams()
    modsReader.skipTree() // tpt
    val rhsIsEmpty = modsReader.nothingButMods(end)
    if !rhsIsEmpty then modsReader.skipTree()
    val (flags, privateWithin) = modsReader.readModifiers(end)
    val normalizedFlags = normalizeFlags(tag, flags, sym.name, rhsIsEmpty)
    sym.withFlags(normalizedFlags, privateWithin)

  /** Read modifiers into a set of flags and a privateWithin boundary symbol. */
  private def readModifiers(end: Addr)(using LocalContext): (FlagSet, Option[Symbol]) =
    var flags: FlagSet = EmptyFlagSet
    var privateWithin: Option[Symbol] = None
    def addFlag(flag: FlagSet): Unit =
      flags |= flag
      reader.readByte()
    def ignoreFlag(): Unit = reader.readByte()
    def ignoreAnnot(): Unit =
      val end = reader.readEnd()
      reader.goto(end)
    while reader.currentAddr.index != end.index do
      reader.nextByte match
        case PRIVATE   => addFlag(Private)
        case PROTECTED => addFlag(Protected)
        case ABSTRACT =>
          reader.readByte()
          reader.nextByte match {
            case OVERRIDE => addFlag(AbsOverride)
            case _        => flags |= Abstract
          }
        case FINAL         => addFlag(Final)
        case SEALED        => addFlag(Sealed)
        case CASE          => addFlag(Case)
        case IMPLICIT      => addFlag(Implicit)
        case ERASED        => addFlag(Erased)
        case LAZY          => addFlag(Lazy)
        case OVERRIDE      => addFlag(Override)
        case INLINE        => addFlag(Inline)
        case INLINEPROXY   => addFlag(InlineProxy)
        case MACRO         => addFlag(Macro)
        case OPAQUE        => addFlag(Opaque)
        case STATIC        => addFlag(Static)
        case OBJECT        => addFlag(Module)
        case TRAIT         => addFlag(Trait)
        case ENUM          => addFlag(Enum)
        case LOCAL         => addFlag(Local)
        case SYNTHETIC     => addFlag(Synthetic)
        case ARTIFACT      => addFlag(Artifact)
        case MUTABLE       => addFlag(Mutable)
        case FIELDaccessor => addFlag(Accessor)
        case CASEaccessor  => addFlag(CaseAccessor)
        case COVARIANT     => addFlag(Covariant)
        case CONTRAVARIANT => addFlag(Contravariant)
        case HASDEFAULT    => ignoreFlag()
        case STABLE        => addFlag(StableRealizable)
        case EXTENSION     => addFlag(Extension)
        case GIVEN         => addFlag(Given)
        case PARAMsetter   => addFlag(ParamAccessor)
        case PARAMalias    => addFlag(SuperParamAlias)
        case EXPORTED      => addFlag(Exported)
        case OPEN          => addFlag(Open)
        case INVISIBLE     => ignoreFlag()
        case TRANSPARENT   => addFlag(Transparent)
        case INFIX         => addFlag(Infix)
        case PRIVATEqualified =>
          ignoreFlag()
          privateWithin = Some(readWithin)
        case PROTECTEDqualified =>
          addFlag(Protected)
          privateWithin = Some(readWithin)
        case ANNOTATION =>
          ignoreFlag()
          ignoreAnnot()
        case tag =>
          assert(false, s"illegal modifier tag $tag at ${reader.currentAddr}, end = $end")
    end while
    (flags, privateWithin)
  end readModifiers

  private def readWithin(using LocalContext): Symbol =
    readType match
      case typeRef: TypeRef   => typeRef.symbol
      case pkgRef: PackageRef => pkgRef.symbol
      case tpe                => throw TastyFormatException(s"unexpected type for readWithin: $tpe")
  end readWithin

  private def readAnnotationsInModifiers(sym: Symbol, end: Addr)(using LocalContext): Unit =
    val innerCtx = localCtx.withOwner(sym)
    var annots: List[Annotation] = Nil

    while reader.currentAddr != end && isModifierTag(reader.nextByte) do
      reader.readByte() match
        case PRIVATEqualified | PROTECTEDqualified =>
          skipTree()
        case ANNOTATION =>
          annots ::= readAnnotation()(using innerCtx)
        case _ =>
          ()
    end while

    sym.setAnnotations(annots)
  end readAnnotationsInModifiers

  private def readAnnotation()(using LocalContext): Annotation =
    val end = reader.readEnd()
    skipTree() // skip the typeref to the annotation class; we only use the tree
    val tree = readTerm
    Annotation(tree)
  end readAnnotation

  /** Performs the read action as if SHARED tags were transparent:
    *  - follows the SHARED tags to the term or type that is shared
    *  - reads the shared term or type with {@code read} action
    *  - restores the reader to seamlessly continue reading after the SHARED tag we started from
    */
  def readPotentiallyShared[T](read: => T): T =
    if (isSharedTag(reader.nextByte)) {
      reader.readByte()
      val addr = reader.readAddr()
      val returnTo = reader.currentAddr
      reader.goto(addr)
      val result = if (isSharedTag(reader.nextByte)) {
        readPotentiallyShared(read)
      } else {
        read
      }
      reader.goto(returnTo)
      result
    } else {
      read
    }

  def readName: TermName = nameAtRef.simple(reader.readNameRef())

  def readFullyQualifiedName: FullyQualifiedName = nameAtRef.fullyQualified(reader.readNameRef())

  def readSignedName(): SignedName = readName.asInstanceOf[SignedName]

  private def readTopLevelStat(using LocalContext): TopLevelTree = reader.nextByte match {
    case PACKAGE =>
      val spn = span
      reader.readByte()
      val packageEnd = reader.readEnd()
      val pid = readPotentiallyShared({
        assert(reader.readByte() == TERMREFpkg, posErrorMsg)
        ctx.findPackageFromRootOrCreate(readFullyQualifiedName)
      })
      PackageDef(pid, reader.until(packageEnd)(readTopLevelStat(using localCtx.withOwner(pid))))(spn)
    case _ => readStat
  }

  private def readStats(end: Addr)(using LocalContext): List[StatementTree] =
    reader.until(end)(readStat)

  private def readStat(using LocalContext): StatementTree = reader.nextByte match {
    case IMPORT | EXPORT =>
      def readSelector: ImportSelector = {
        assert(reader.nextByte == IMPORTED, posErrorMsg)
        val nameSpan = span
        reader.readByte()
        val name = ImportIdent(readName)(nameSpan)
        // IMPORTED can be followed by RENAMED or BOUNDED
        reader.nextByte match {
          case RENAMED =>
            val renamedSpan = span
            reader.readByte()
            val renamed = ImportIdent(readName)(renamedSpan)
            ImportSelector(name, Some(renamed), bound = None)(nameSpan.union(renamedSpan))
          case BOUNDED =>
            reader.readByte()
            val boundSpan = span
            val bound = readTypeTree
            ImportSelector(name, renamed = None, Some(bound))(nameSpan.union(boundSpan))
          case _ =>
            ImportSelector(name, renamed = None, bound = None)(nameSpan)
        }
      }
      val spn = span
      val tag = reader.readByte()
      val end = reader.readEnd()
      val qual = readTerm
      val selectors = reader.until(end)(readSelector)
      if (tag == IMPORT) Import(qual, selectors)(spn) else Export(qual, selectors)(spn)
    case TYPEDEF =>
      val spn = span
      val start = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      val typeDef: ClassDef | TypeMember = if (reader.nextByte == TEMPLATE) {
        val classSymbol = localCtx.getSymbol[ClassSymbol](start)
        val template = readTemplate(using localCtx.withOwner(classSymbol))
        definingTree(classSymbol, ClassDef(name, template, classSymbol)(spn))
      } else {
        val symbol = localCtx.getSymbol[TypeMemberSymbol](start)
        val innerCtx = localCtx.withOwner(symbol)
        val typeBounds: TypeTree | TypeBounds =
          if tagFollowShared == TYPEBOUNDS then readTypeBounds(using innerCtx)
          else readTypeTree(using innerCtx)
        val typeDef = typeBounds match
          case tpt: TypeTree =>
            tpt.toType match
              case bt: BoundedType =>
                bt.alias match
                  case None        => TypeMemberDefinition.AbstractType(bt.bounds)
                  case Some(alias) => TypeMemberDefinition.OpaqueTypeAlias(bt.bounds, alias)
              case alias =>
                TypeMemberDefinition.TypeAlias(alias)
          case bounds: TypeBounds =>
            TypeMemberDefinition.AbstractType(bounds)
        symbol.withDefinition(typeDef)
        definingTree(symbol, TypeMember(name, typeBounds, symbol)(spn))
      }
      readAnnotationsInModifiers(typeDef.symbol, end)
      typeDef
    case VALDEF | DEFDEF => readValOrDefDef
    case _               => readTerm
  }

  /** Reads type bounds for a synthetic typedef */
  private def readTypeBounds(using LocalContext): TypeBounds = {
    assert(tagFollowShared == TYPEBOUNDS, posErrorMsg)
    readPotentiallyShared({
      reader.readByte()
      val end = reader.readEnd()
      val low = readType
      if (reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
        val high = readType
        // TODO: read variance (a modifier)
        skipModifiers(end)
        RealTypeBounds(low, high)
      } else {
        skipModifiers(end)
        TypeAlias(low)
      }
    })
  }

  private def readTypeParams(using LocalContext): List[TypeParam] = {
    def readTypeParamType(using LocalContext): TypeBounds | TypeBoundsTree | TypeLambdaTree = {
      def readTypeBoundsType(using LocalContext): TypeBounds = {
        assert(reader.readByte() == TYPEBOUNDS, posErrorMsg)
        val end = reader.readEnd()
        val low = readType
        // type bounds for type parameters have to be bounds, not an alias
        assert(reader.currentAddr != end && !isModifierTag(reader.nextByte), posErrorMsg)
        val high = readType
        // TODO: read variance (a modifier)
        skipModifiers(end)
        RealTypeBounds(low, high)
      }

      def readTypeBoundsTree(using LocalContext): TypeBoundsTree = {
        val spn = span
        assert(reader.readByte() == TYPEBOUNDStpt, posErrorMsg)
        val end = reader.readEnd()
        val low = readTypeTree
        val high = readTypeTree
        // assert atEnd: no alias for type parameters
        assert(reader.currentAddr == end, posErrorMsg)
        TypeBoundsTree(low, high)(spn)
      }

      def readLambdaTpt(using LocalContext): TypeLambdaTree = {
        assert(reader.nextByte == LAMBDAtpt, posErrorMsg)
        readTypeTree.asInstanceOf[TypeLambdaTree]
      }

      readPotentiallyShared(
        if (tagFollowShared == TYPEBOUNDS)
          readTypeBoundsType
        else if (tagFollowShared == TYPEBOUNDStpt)
          readTypeBoundsTree
        else
          readLambdaTpt
      )
    }

    def readTypeParam: TypeParam = {
      val spn = span
      val start = reader.currentAddr
      val paramSymbol = localCtx.getSymbol[TypeParamSymbol](start)
      val expectedFlags = if paramSymbol.owner.isClass then ClassTypeParam else TypeParameter
      assert(paramSymbol.flags.isAllOf(expectedFlags))
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      val bounds = readTypeParamType(using localCtx.withOwner(paramSymbol))
      val typeBounds = bounds match
        case bounds: TypeBounds     => bounds
        case bounds: TypeBoundsTree => bounds.toTypeBounds
        case bounds: TypeLambdaTree => defn.NothingAnyBounds
      paramSymbol.setBounds(typeBounds)
      readAnnotationsInModifiers(paramSymbol, end)
      definingTree(paramSymbol, TypeParam(name, bounds, paramSymbol)(spn))
    }
    val acc = new ListBuffer[TypeParam]()
    while (reader.nextByte == TYPEPARAM) {
      acc += readTypeParam
    }
    acc.toList
  }

  /** Reads TYPEBOUNDStpt of a typedef */
  private def readBoundedTypeTree(using LocalContext): BoundedTypeTree = {
    assert(reader.readByte() == TYPEBOUNDStpt, posErrorMsg)
    val spn = span
    val end = reader.readEnd()
    val low = readTypeTree
    val high = readTypeTree
    val alias = reader.ifBeforeOpt(end)(readTypeTree)
    BoundedTypeTree(TypeBoundsTree(low, high)(spn), alias)(spn)
  }

  private def readTypeBoundsTree(using LocalContext): TypeBoundsTree = {
    assert(tagFollowShared == TYPEBOUNDStpt, posErrorMsg)
    readPotentiallyShared({
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val low = readTypeTree
      val high = readTypeTree
      TypeBoundsTree(low, high)(spn)
    })
  }

  // TODO: classinfo of the owner
  private def readTemplate(using LocalContext): Template = {
    val spn = span
    reader.readByte()
    val end = reader.readEnd()
    val cls = localCtx.owner.asClass
    val tparams = readTypeParams
    cls.withTypeParams(tparams.map(_.symbol.asInstanceOf[ClassTypeParamSymbol]))
    val params = readParams
    val parents: List[Apply | Block | TypeTree] =
      reader.collectWhile(reader.nextByte != SELFDEF && reader.nextByte != DEFDEF) {
        reader.nextByte match {
          // class parents of classes and trait parents with arguments are APPLYs, because they specify the constructor
          // BLOCK when the parent constructor has default parameters and the call specifies only some of them
          case APPLY => readTerm.asInstanceOf[Apply]
          case BLOCK => readTerm.asInstanceOf[Block]
          case _     => readTypeTree
        }
      }
    cls.withParentsDelayed { () =>
      parents.map {
        case parent: Apply    => parent.tpe
        case parent: Block    => parent.tpe
        case parent: TypeTree => parent.toType
      }
    }
    val self = readSelf
    // The first entry is the constructor
    val cstr = readStat.asInstanceOf[DefDef]
    val body = readStats(end)
    Template(cstr, parents, self, tparams ++ params ++ body)(spn)
  }

  private def readAllParams(using LocalContext): List[ParamsClause] =
    reader.nextByte match {
      case PARAM => Left(readParams) :: readAllParams
      case EMPTYCLAUSE =>
        reader.readByte()
        Left(Nil) :: readAllParams
      case TYPEPARAM => Right(readTypeParams) :: readAllParams
      case _         => Nil
    }

  private def readParamLists(using LocalContext): List[List[ValDef]] = {
    var acc = new ListBuffer[List[ValDef]]()
    while (reader.nextByte == PARAM || reader.nextByte == EMPTYCLAUSE) {
      reader.nextByte match {
        case PARAM => acc += readParams
        case EMPTYCLAUSE =>
          reader.readByte()
          acc += Nil
      }
    }
    acc.toList
  }

  private def readParams(using LocalContext): List[ValDef] = {
    var acc = new ListBuffer[ValDef]()
    while (reader.nextByte == PARAM) {
      acc += readValOrDefDef.asInstanceOf[ValDef]
    }
    if (reader.nextByte == SPLITCLAUSE) {
      reader.readByte()
    }
    acc.toList
  }

  private def readSelf(using LocalContext): Option[SelfDef] =
    if (reader.nextByte != SELFDEF) {
      None
    } else {
      val spn = span
      reader.readByte()
      val name = readName
      val tpt = readTypeTree
      Some(SelfDef(name, tpt)(tpt.span))
    }

  private def readValOrDefDef(using LocalContext): ValOrDefDef = {
    val spn = span
    val start = reader.currentAddr
    val tag = reader.readByte()
    val end = reader.readEnd()
    val name = readName
    // Only for DefDef, but reading works for empty lists
    val symbol = localCtx.getSymbol[TermSymbol](start)
    val insideCtx = localCtx.withOwner(symbol)
    val params = readAllParams(using insideCtx)
    val tpt = readTypeTree(using insideCtx)
    val rhs =
      if (reader.currentAddr == end || isModifierTag(reader.nextByte)) None
      else Some(readTerm(using insideCtx))
    readAnnotationsInModifiers(symbol, end)
    tag match {
      case VALDEF | PARAM =>
        symbol.withDeclaredType(tpt.toType)
        definingTree(symbol, ValDef(name, tpt, rhs, symbol)(spn))
      case DEFDEF =>
        symbol.withDeclaredType(makeDefDefType(params, tpt))
        definingTree(symbol, DefDef(name, params, tpt, rhs, symbol)(spn))
    }
  }

  private def makeDefDefType(paramLists: List[ParamsClause], resultTpt: TypeTree): Type =
    def rec(paramLists: List[ParamsClause]): Type =
      paramLists match
        case Left(params) :: rest =>
          val paramSymbols = params.map(_.symbol)
          MethodType.fromSymbols(paramSymbols, rec(rest))
        case Right(tparams) :: rest =>
          PolyType.fromParams(tparams, rec(rest))
        case Nil =>
          resultTpt.toType

    if paramLists.isEmpty then ExprType(resultTpt.toType)
    else rec(paramLists)
  end makeDefDefType

  private def readTerms(end: Addr)(using LocalContext): List[TermTree] =
    reader.until(end)(readTerm)

  def definingTree(symbol: Symbol, tree: symbol.DefiningTreeType): tree.type =
    symbol.withTree(tree)
    tree

  private def readPattern(using LocalContext): PatternTree = reader.nextByte match
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readType
      if name == nme.Wildcard then WildcardPattern(typ)(spn)
      else ExprPattern(Ident(name)(typ)(spn))(spn)
    case TYPED =>
      reader.readByte()
      reader.readEnd()
      val body = readPattern
      val tpt = readTypeTree
      TypeTest(body, tpt)(body.span.union(tpt.span))
    case BIND =>
      val spn = span
      val start = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val name = readName
      val typ = readType
      val body = readPattern
      val symbol = localCtx.getSymbol[TermSymbol](start)
      readAnnotationsInModifiers(symbol, end)
      symbol.withDeclaredType(typ)
      definingTree(symbol, Bind(name, body, symbol)(spn))
    case ALTERNATIVE =>
      reader.readByte()
      val end = reader.readEnd()
      val alts = reader.until(end)(readPattern)
      Alternative(alts)(spanSeq(alts))
    case UNAPPLY =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val fun = readTerm
      val args = reader.collectWhile(reader.nextByte == IMPLICITarg)({
        assert(reader.readByte() == IMPLICITarg, posErrorMsg)
        readTerm
      })
      // TODO: use pattern type
      val patType = readType
      val patterns = reader.until(end)(readPattern)
      Unapply(fun, args, patterns)(spn)
    case _ =>
      val expr = readTerm
      ExprPattern(expr)(expr.span)
  end readPattern

  private def readTerm(using LocalContext): TermTree = reader.nextByte match {
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readType
      Ident(name)(typ)(spn)
    case APPLY =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val fn = readTerm
      val args = readTerms(end)
      Apply(fn, args)(spn)
    case NAMEDARG =>
      val spn = span
      reader.readByte()
      NamedArg(readName, readTerm)(spn)
    case TYPEAPPLY =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val fn = readTerm
      TypeApply(fn, reader.until(end)(readTypeTree))(spn)
    case SELECT =>
      val spn = span
      reader.readByte()
      val name = readName
      val qual = readTerm
      Select(qual, name)(selectOwner = None)(spn)
    case QUALTHIS =>
      val spn = span
      reader.readByte()
      val qualifier = readTypeTree.asInstanceOf[TypeIdent]
      This(qualifier)(spn)
    case SUPER =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val qual = readTerm
      val mixin = reader.ifBefore(end)(Some(readTypeTree.asInstanceOf[TypeIdent]), None)
      Super(qual, mixin)(spn)
    case SELECTin =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val name = readSignedName()
      val qual = readTerm
      val owner = readTypeRef()
      Select(qual, name)(Some(owner))(spn)
    case NEW =>
      val spn = span
      reader.readByte()
      val cls = readTypeTree
      New(cls)(spn)
    case TYPED =>
      reader.readByte()
      reader.readEnd()
      val expr = readTerm
      val tpt = readTypeTree
      Typed(expr, tpt)(expr.span.union(tpt.span))
    case THROW =>
      val spn = span
      reader.readByte()
      val thrown = readTerm
      Throw(thrown)(spn)
    case TRY =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val expr = readTerm
      val catchCases = readCases[CaseDef](CaseDefFactory, end)
      val finalizer = reader.ifBeforeOpt(end)(readTerm)
      Try(expr, catchCases, finalizer)(spn)
    case ASSIGN =>
      reader.readByte()
      reader.readEnd()
      val lhsSpan = span
      val lhs = readTerm
      val rhsSpan = span
      val rhs = readTerm
      Assign(lhs, rhs)(lhsSpan.union(rhsSpan))
    case BLOCK =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val expr = readTerm
      Block(readStats(end), expr)(spn)
    case IF =>
      val spn = span
      reader.readByte()
      reader.readEnd()
      if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineIf(readTerm, readTerm, readTerm)(spn)
      } else {
        If(readTerm, readTerm, readTerm)(spn)
      }
    case LAMBDA =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val method = readTerm
      val tpt = reader.ifBeforeOpt(end)(readTypeTree)
      Lambda(method, tpt)(spn)
    case MATCH =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      if (reader.nextByte == IMPLICIT) {
        reader.readByte()
        new InlineMatch(None, readCases[CaseDef](CaseDefFactory, end))(spn)
      } else if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineMatch(Some(readTerm), readCases[CaseDef](CaseDefFactory, end))(spn)
      } else Match(readTerm, readCases[CaseDef](CaseDefFactory, end))(spn)
    case REPEATED =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val elemType = readTypeTree
      SeqLiteral(reader.until(end)(readTerm), elemType)(spn)
    case WHILE =>
      val spn = span
      reader.readByte()
      reader.readEnd()
      While(readTerm, readTerm)(spn)
    case RETURN =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val trtSpan = spn
      val from = readSymRef.asTerm
      val expr = reader.ifBeforeOpt(end)(readTerm)
      Return(expr, from)(spn)
    case INLINED =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val expr = readTerm
      val caller: Option[TypeIdent] =
        reader.ifBefore(end)(
          tagFollowShared match {
            // The caller is not specified, this is a binding (or next val or def)
            case VALDEF | DEFDEF => None
            case _               => Some(readTypeTree.asInstanceOf[TypeIdent])
          },
          None
        )
      val bindings = reader.until(end)(readValOrDefDef)
      Inlined(expr, caller, bindings)(spn)
    case SHAREDterm =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readTerm.withSpan(spn)

    // paths
    case THIS =>
      val spn = span
      reader.readByte()
      val typ = readType.asInstanceOf[TypeRef]
      This(TypeIdent(typ.name)(typ)(spn))(spn)
    case TERMREF =>
      val spn = span
      reader.readByte()
      val name = readName
      val prefix = readType
      Ident(name)(TermRef(prefix, name))(spn)
    case TERMREFpkg =>
      val spn = span
      reader.readByte()
      val fullyQualifiedName = readFullyQualifiedName
      val simpleName = fullyQualifiedName.sourceName.asSimpleName
      val tpe = PackageRef(fullyQualifiedName)
      Ident(simpleName)(tpe)(span)
    case TERMREFdirect =>
      val spn = span
      reader.readByte()
      val sym = readSymRef.asTerm
      val tpe = TermRef(NoPrefix, sym)
      Ident(sym.name)(tpe)(spn)
    case TERMREFsymbol =>
      val spn = span
      reader.readByte()
      val sym = readSymRef.asTerm
      val pre = readType
      Ident(sym.name)(TermRef(pre, sym))(spn)
    case SHAREDtype =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readTerm.withSpan(spn)
    case tag if isConstantTag(tag) =>
      val spn = span
      Literal(readConstant)(spn)
    case tag =>
      throw TastyFormatException(s"Unexpected term tag ${astTagToString(tag)} $posErrorMsg")
  }

  /** The next tag, following through SHARED tags */
  def nextUnsharedTag: Int = {
    val tag = reader.nextByte
    if (tag == SHAREDtype || tag == SHAREDterm) {
      val lookAhead = fork
      lookAhead.reader.readByte()
      forkAt(lookAhead.reader.readAddr()).nextUnsharedTag
    } else tag
  }

  private def readCases[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T], end: Addr)(
    using LocalContext
  ): List[T] =
    reader.collectWhile((nextUnsharedTag == CASEDEF) && reader.currentAddr != end) {
      if (reader.nextByte == SHAREDterm) {
        // skip the SHAREDterm tag
        reader.readByte()
        // TODO: changes in the context?
        forkAt(reader.readAddr()).readCaseDef[T](factory)
      }
      // TODO: changes in the context?
      else readCaseDef[T](factory)
    }

  private def readCaseDef[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T])(using LocalContext): T = {
    val spn = span
    assert(reader.readByte() == CASEDEF, posErrorMsg)
    val end = reader.readEnd()
    factory match {
      case CaseDefFactory =>
        val pattern = readPattern
        val body = readTerm
        CaseDef(pattern, reader.ifBeforeOpt(end)(readTerm), body)(spn)
      case TypeCaseDefFactory =>
        TypeCaseDef(readTypeTree, readTypeTree)(spn)
    }
  }

  private def readSymRef(using LocalContext): Symbol = {
    val symAddr = reader.readAddr()
    assert(localCtx.hasSymbolAt(symAddr), posErrorMsg)
    localCtx.getSymbol[Symbol](symAddr)
  }

  private def readTypeRef()(using LocalContext): TypeRef =
    readType.asInstanceOf[TypeRef]

  private def readType(using LocalContext): Type = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readType, name)
    case TYPEREFin =>
      reader.readByte()
      reader.readEnd()
      val name = readName.toTypeName
      val prefix = readType
      // TODO: use the namespace
      val namespace = readType
      TypeRef(prefix, name)
    case TYPEREFdirect =>
      reader.readByte()
      val sym = readSymRef.asType
      TypeRef(NoPrefix, sym)
    case TYPEREFsymbol =>
      reader.readByte()
      val sym = readSymRef.asType
      TypeRef(readType, sym)
    case TYPEREFpkg =>
      reader.readByte()
      PackageRef(readFullyQualifiedName)
    case SHAREDtype =>
      reader.readByte()
      val addr = reader.readAddr()
      recursiveTypeAtAddr.getOrElse(addr, sharedTypesCache.getOrElseUpdate(addr, forkAt(addr).readType))
    case TERMREFdirect =>
      reader.readByte()
      val sym = readSymRef.asTerm
      TermRef(NoPrefix, sym)
    case TERMREFsymbol =>
      reader.readByte()
      val sym = readSymRef.asTerm
      TermRef(readType, sym)
    case TERMREFpkg =>
      reader.readByte()
      new PackageRef(readFullyQualifiedName)
    case TERMREF =>
      reader.readByte()
      val name = readName
      TermRef(readType, name)
    case APPLIEDtype =>
      reader.readByte()
      val end = reader.readEnd()
      val tycon = readType
      // TODO: type operations can be much more complicated
      AppliedType(
        tycon,
        reader.until(end)(if (tagFollowShared == TYPEBOUNDS) WildcardTypeBounds(readTypeBounds) else readType)
      )
    case THIS =>
      reader.readByte()
      readType match
        case typeRef: TypeRef       => ThisType(typeRef)
        case packageRef: PackageRef => packageRef
        case tpe =>
          throw TastyFormatException(s"Unexpected underlying type of THIS: $tpe")
    case QUALTHIS =>
      reader.readByte()
      if (tagFollowShared != IDENTtpt) {
        throw TastyFormatException(s"Unexpected tag after QUALTHIS: ${astTagToString(tagFollowShared)} $posErrorMsg")
      }
      // Skip IDENTtpt tag and name
      reader.readByte()
      readName
      // Type of QUALTHIS is ThisType for the type reference, which is the type of the IDENTtpt
      ThisType(readType.asInstanceOf[TypeRef])
    case ANNOTATEDtype =>
      reader.readByte()
      reader.readEnd()
      val typ = readType
      val annot = readTerm
      AnnotatedType(typ, annot)
    case ANDtype =>
      reader.readByte()
      reader.readEnd()
      AndType(readType, readType)
    case ORtype =>
      reader.readByte()
      reader.readEnd()
      OrType(readType, readType)
    case BYNAMEtype =>
      reader.readByte()
      ExprType(readType)
    case POLYtype =>
      readLambdaType(_ => PolyType, name => name.toTypeName, _.readTypeBounds)
    case METHODtype =>
      // TODO Record the `mods` somehow (given, implicit, erased)
      readLambdaType(_ => MethodType, name => name, _.readType)
    case TYPELAMBDAtype =>
      readLambdaType(_ => TypeLambda, _.toTypeName, _.readTypeBounds)
    case PARAMtype =>
      reader.readByte()
      reader.readEnd()
      val lambdaAddr = reader.readAddr()
      val num = reader.readNat()
      localCtx.getEnclosingBinders(lambdaAddr).asInstanceOf[ParamRefBinders].paramRefs(num)
    case REFINEDtype =>
      reader.readByte()
      val end = reader.readEnd()
      val refinementName = readName
      val underlying = readType
      if tagFollowShared == TYPEBOUNDS then
        // Type refinement with a type member of the form `Underlying { type refinementName <:> TypeBounds }`
        val refinedMemberBounds = readTypeBounds
        TypeRefinement(underlying, refinementName.toTypeName, refinedMemberBounds)
      else
        // Type refinement with a term member of the form `Underlying { val/def refinementName: Type }`
        val refinedMemberType = readType
        TermRefinement(underlying, refinementName, refinedMemberType)
    case RECtype =>
      val start = reader.currentAddr
      reader.readByte()
      recursiveTypeAtAddr.get(start) match
        case Some(tp) =>
          skipTree()
          tp
        case None =>
          RecType { rt =>
            recursiveTypeAtAddr(start) = rt
            readType
          }
    case RECthis =>
      reader.readByte()
      val recType = recursiveTypeAtAddr(reader.readAddr()).asInstanceOf[RecType]
      recType.recThis
    case MATCHtype =>
      val start = reader.currentAddr
      reader.readByte() // tag
      val end = reader.readEnd()
      val upperBound = readType
      val scrutinee = readType
      val cases: List[MatchTypeCase | TypeLambda] = reader.until(end)(readType match
        case tpe: (MatchTypeCase | TypeLambda) => tpe
        case tpe => throw TastyFormatException(s"Unexpected type in MATCHtype: $tpe $posErrorMsg")
      )
      MatchType(upperBound, scrutinee, cases)
    case MATCHCASEtype =>
      reader.readByte() // tag
      reader.readEnd() // end
      val pattern = readType
      val body = readType
      MatchTypeCase(pattern, body)
    case tag if (isConstantTag(tag)) =>
      ConstantType(readConstant)
    case tag =>
      throw TastyFormatException(s"Unexpected type tag ${astTagToString(tag)} $posErrorMsg")
  }

  private def readLambdaType[N <: Name, PInfo <: Type | TypeBounds, LT <: LambdaType](
    companionOp: FlagSet => LambdaTypeCompanion[N, PInfo, LT],
    nameMap: TermName => N,
    readInfo: TreeUnpickler => PInfo
  )(using LocalContext): LT =
    val lambdaAddr = reader.currentAddr
    reader.readByte()
    val end = reader.readEnd()

    val resultUnpickler = fork // remember where the result type is
    skipTree() // skip the result type
    val paramInfosUnpickler = fork // remember where the params are

    // Read names -- skip infos, and stop if we find a modifier
    val paramNames = reader.collectWhile(reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
      skipTree()
      nameMap(readName)
    }

    // Read mods
    var mods = EmptyFlagSet
    while reader.currentAddr != end do // avoid boxing the mods
      reader.readByte() match
        case IMPLICIT => mods |= Implicit
        case ERASED   => mods |= Erased
        case GIVEN    => mods |= Given

    // Read infos -- skip names
    def readParamInfos()(using LocalContext): List[PInfo] =
      val reader = paramInfosUnpickler.reader
      reader.collectWhile(reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
        val bounds = readInfo(paramInfosUnpickler)
        reader.readNat() // skip name
        bounds
      }
    end readParamInfos

    val factory = companionOp(mods)
    factory(paramNames)(
      tl => readParamInfos()(using localCtx.withEnclosingBinders(lambdaAddr, tl)),
      tl => resultUnpickler.readType(using localCtx.withEnclosingBinders(lambdaAddr, tl))
    )
  end readLambdaType

  private def readTypeTree(using LocalContext): TypeTree = reader.nextByte match {
    case IDENTtpt =>
      val spn = span
      reader.readByte()
      val typeName = readName.toTypeName
      val typ = readType
      TypeIdent(typeName)(typ)(spn)
    case SINGLETONtpt =>
      val spn = span
      reader.readByte()
      SingletonTypeTree(readTerm)(spn)
    case REFINEDtpt =>
      val spn = span
      val cls = ClassSymbol.createRefinedClassSymbol(localCtx.owner, spn)
      recursiveTypeAtAddr(reader.currentAddr) = cls.typeRef
      reader.readByte()
      val end = reader.readEnd()
      val parent = readTypeTree
      val statements = readStats(end)(using localCtx.withOwner(cls))
      val refinements = statements.map {
        case memberDef: RefinementMemberDef =>
          memberDef
        case otherDef =>
          throw TastyFormatException(s"Unexpected member $otherDef in refinement type")
      }
      RefinedTypeTree(parent, refinements, cls)(spn)
    case APPLIEDtpt =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val tycon = readTypeTree
      AppliedTypeTree(
        tycon,
        reader.until(end)(
          if (tagFollowShared == TYPEBOUNDS) TypeWrapper(WildcardTypeBounds(readTypeBounds))(spn)
          else if (tagFollowShared == TYPEBOUNDStpt) WildcardTypeBoundsTree(readTypeBoundsTree)(spn)
          else readTypeTree
        )
      )(spn)
    case LAMBDAtpt =>
      val spn = span
      reader.readByte()
      reader.readEnd()
      TypeLambdaTree(readTypeParams, readTypeTree)(spn)
    // select type from a term
    case SELECT =>
      val spn = span
      reader.readByte()
      val name = readName
      val qual = readTerm
      TermRefTypeTree(qual, name)(spn)
    case SELECTtpt =>
      val spn = span
      reader.readByte()
      val name = readName.toTypeName
      SelectTypeTree(readTypeTree, name)(spn)
    case ANNOTATEDtpt =>
      val spn = span
      reader.readByte()
      reader.readEnd()
      AnnotatedTypeTree(readTypeTree, readTerm)(spn)
    case MATCHtpt =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val selOrBound = readTypeTree
      val (bound, selector) =
        if tagFollowShared == CASEDEF then (None, selOrBound)
        else (Some(selOrBound), readTypeTree)
      MatchTypeTree(bound, selector, readCases[TypeCaseDef](TypeCaseDefFactory, end))(spn)
    // TODO: why in TYPEAPPLY?
    // in MATCHtpt, TYPEAPPLY
    case BIND =>
      val spn = span
      val start = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      val bounds = readTypeBounds
      /* This is a workaround: consider a BIND inside a MATCHtpt
       * example: case List[t] => t
       * Such a bind has IDENT(_) as its body, which is not a type tree and therefore not expected.
       * Treat it as if it were an IDENTtpt. */
      val body: TypeTree = if (reader.nextByte == IDENT) {
        val bodySpn = span
        reader.readByte()
        val typeName = readName.toTypeName
        val typ = readTypeBounds
        NamedTypeBoundsTree(typeName, typ)(bodySpn)
      } else readTypeTree
      val sym = localCtx.getSymbol[LocalTypeParamSymbol](start)
      readAnnotationsInModifiers(sym, end)
      sym.setBounds(bounds)
      definingTree(sym, TypeTreeBind(name, body, sym)(spn))
    // Type tree for a type member (abstract or bounded opaque)
    case TYPEBOUNDStpt => readBoundedTypeTree
    case BYNAMEtpt =>
      val spn = span
      reader.readByte()
      ByNameTypeTree(readTypeTree)(spn)
    case SHAREDterm =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readTypeTree.withSpan(spn)
    case tag if isTypeTreeTag(tag) =>
      throw TastyFormatException(s"Unexpected type tree tag ${astTagToString(tag)} $posErrorMsg")
    case _ => TypeWrapper(readType)(span)
  }

  private def readConstant(using LocalContext): Constant = reader.readByte() match {
    case UNITconst =>
      Constant(())
    case TRUEconst =>
      Constant(true)
    case FALSEconst =>
      Constant(false)
    case BYTEconst =>
      Constant(reader.readInt().toByte)
    case SHORTconst =>
      Constant(reader.readInt().toShort)
    case CHARconst =>
      Constant(reader.readNat().toChar)
    case INTconst =>
      Constant(reader.readInt())
    case LONGconst =>
      Constant(reader.readLongInt())
    case FLOATconst =>
      Constant(java.lang.Float.intBitsToFloat(reader.readInt()))
    case DOUBLEconst =>
      Constant(java.lang.Double.longBitsToDouble(reader.readLongInt()))
    case STRINGconst =>
      Constant(readName.toString)
    case NULLconst =>
      Constant(null)
    case CLASSconst =>
      Constant(readType)
  }

  // TODO: read modifiers and return them instead
  private def skipModifiers(end: Addr)(using LocalContext): Unit = {
    def skipModifier(): Unit = reader.readByte() match {
      case PRIVATEqualified =>
        readType
        ()
      case PROTECTEDqualified =>
        readType
        ()
      case ANNOTATION =>
        val end = reader.readEnd()
        reader.goto(end)
      case _ => ()
    }
    while (reader.currentAddr != end && isModifierTag(reader.nextByte)) {
      skipModifier()
    }
  }

  private def isConstantTag(tag: Int): Boolean =
    tag match {
      case UNITconst | FALSEconst | TRUEconst | BYTEconst | SHORTconst | CHARconst | INTconst | LONGconst | FLOATconst |
          DOUBLEconst | STRINGconst | NULLconst | CLASSconst =>
        true
      case _ => false
    }
}

private[tasties] object TreeUnpickler {

  extension (reader: TastyReader)
    def ifBeforeOpt[T](end: Addr)(op: => T): Option[T] =
      reader.ifBefore(end)(Some(op), None)

  private inline def localCtx(using ctx: LocalContext): LocalContext = ctx

  /** LocalContext is used when unpickling a given .tasty file.
    * It contains information local to the file and to the scope, and
    * keeps track of the current owner.
    *
    * @param filename
    *   the .tasty file being unpickled, used for error reporting
    * @param owner
    *   the owner for symbols created in the current scope
    * @param localSymbols
    *   map of the symbols, created when unpickling the current file.
    *   A symbol can be referred to from anywhere in the file, therefore once the symbol is added
    *   to the file info, it is kept in the context and its subcontexts.
    * @param enclosingBinders
    *   map of the type binders which have the current address in scope.
    *   A type binder can only be referred to if it encloses the referring address.
    *   A new FileLocalInfo (hence a new LocalContext) is created when an enclosing is added
    *   to mimic the scoping.
    */
  private class LocalContext(
    filename: String,
    val owner: Symbol,
    localSymbols: mutable.HashMap[Addr, Symbol],
    enclosingBinders: Map[Addr, Binders]
  ) { base =>

    def withEnclosingBinders(addr: Addr, b: Binders): LocalContext =
      new LocalContext(filename, owner, localSymbols, enclosingBinders.updated(addr, b))

    def withOwner(newOwner: Symbol): LocalContext =
      if (newOwner == owner) this
      else new LocalContext(filename, newOwner, localSymbols, enclosingBinders)

    def getFile: String = filename

    def getEnclosingBinders(addr: Addr): Binders = enclosingBinders(addr)

    def hasSymbolAt(addr: Addr): Boolean = localSymbols.contains(addr)

    /** Registers a symbol at @addr with @name. */
    def registerSym(addr: Addr, sym: Symbol): sym.type =
      if hasSymbolAt(addr) then throw AssertionError(s"Duplicate symbol $sym for address $addr")
      localSymbols(addr) = sym
      sym

    def getSymbol[T <: Symbol](addr: Addr)(using scala.reflect.TypeTest[Symbol, T], NotGiven[T =:= Nothing]): T =
      localSymbols(addr) match
        case sym: T => sym
        case sym =>
          throw AssertionError(s"Illegal kind of symbol found at address $addr; got: ${sym.getClass()}")

    def allRegisteredSymbols: Iterator[Symbol] =
      localSymbols.valuesIterator
  }

}
