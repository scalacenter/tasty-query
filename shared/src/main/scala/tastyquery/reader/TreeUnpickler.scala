package tastyquery.reader

import tastyquery.Contexts.*
import tastyquery.ast.Constants.Constant
import tastyquery.ast.Flags
import tastyquery.ast.Names.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Trees.*
import tastyquery.ast.TypeTrees.*
import tastyquery.ast.Types.*
import tastyquery.ast.Flags.*
import tastyquery.ast.Spans.{Span, NoSpan}
import tastyquery.reader.TastyUnpickler.NameTable

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import scala.util.NotGiven
import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyReader}
import TastyBuffer.*
import TastyFormat.*
import tastyquery.Definitions
import tastyquery.reader.classfiles.Classpaths

class TreeUnpicklerException(msg: String) extends RuntimeException(msg)

sealed trait AbstractCaseDefFactory[CaseDefType]
case object CaseDefFactory extends AbstractCaseDefFactory[CaseDef]
case object TypeCaseDefFactory extends AbstractCaseDefFactory[TypeCaseDef]

class TreeUnpickler(
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
    read(new ListBuffer[Tree])

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
          ctx.createPackageSymbolIfNew(readFullyQualifiedName)
        })
        reader.until(end)(createSymbols()(using localCtx.withOwner(pid)))
      case TYPEDEF =>
        val end = reader.readEnd()
        val name = readName.toTypeName
        val tag = reader.nextByte
        val factory = if tag == TEMPLATE then ClassSymbolFactory else RegularSymbolFactory
        val newOwner = localCtx.createSymbol(start, name, factory, addToDecls = localCtx.owner.isClass)
        readSymbolModifiers(newOwner, tag, end)
        reader.until(end)(createSymbols()(using localCtx.withOwner(newOwner)))
        if tag == TEMPLATE then newOwner.asInstanceOf[ClassSymbol].initialised = true
      case DEFDEF | VALDEF | PARAM | TYPEPARAM =>
        val end = reader.readEnd()
        val name = if tag == TYPEPARAM then readName.toTypeName else readName
        val addToDecls = tag != TYPEPARAM && localCtx.owner.isClass
        val newSymbol =
          localCtx.createSymbol(start, name, RegularSymbolFactory, addToDecls)
        readSymbolModifiers(newSymbol, tag, end)
        reader.until(end)(createSymbols()(using localCtx.withOwner(newSymbol)))
      case BIND =>
        val end = reader.readEnd()
        var name: Name = readName
        if (tagFollowShared == TYPEBOUNDS) name = name.toTypeName
        localCtx.createSymbol(start, name, RegularSymbolFactory, addToDecls = false)
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
    sym.withFlags(normalizedFlags)
    privateWithin.foreach(sym.withPrivateWithin)

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

  private def readWithin(using LocalContext): Symbol = readType.typeSymbol

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

  private def readTopLevelStat(using LocalContext): Tree = reader.nextByte match {
    case PACKAGE =>
      val spn = span
      reader.readByte()
      val packageEnd = reader.readEnd()
      val pid = readPotentiallyShared({
        assert(reader.readByte() == TERMREFpkg, posErrorMsg)
        ctx.createPackageSymbolIfNew(readFullyQualifiedName)
      })
      PackageDef(pid, reader.until(packageEnd)(readTopLevelStat(using localCtx.withOwner(pid))))(spn)
    case _ => readStat
  }

  private def readStats(end: Addr)(using LocalContext): List[Tree] =
    reader.until(end)(readStat)

  private def readStat(using LocalContext): Tree = reader.nextByte match {
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
            ImportSelector(name, renamed)(nameSpan.union(renamedSpan))
          case BOUNDED =>
            reader.readByte()
            val boundSpan = span
            val bound = readTypeTree
            ImportSelector(name, EmptyTree, bound)(nameSpan.union(boundSpan))
          case _ => ImportSelector(name)(nameSpan)
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
      val typedef: ClassDef | TypeMember = if (reader.nextByte == TEMPLATE) {
        val classSymbol = localCtx.getSymbol(start, ClassSymbolFactory)
        ClassDef(name, readTemplate(using localCtx.withOwner(classSymbol)), classSymbol)(spn).definesTreeOf(classSymbol)
      } else {
        val symbol = localCtx.getSymbol(start, RegularSymbolFactory)
        val innerCtx = localCtx.withOwner(symbol)
        val typeBounds: TypeTree | TypeBounds =
          if tagFollowShared == TYPEBOUNDS then readTypeBounds(using innerCtx)
          else readTypeTree(using innerCtx)
        val declaredType = typeBounds match
          case tpt: TypeTree          => tpt.toType
          case typeBounds: TypeBounds => WildcardTypeBounds(typeBounds)
        symbol.withDeclaredType(declaredType)
        TypeMember(name, typeBounds, symbol)(spn).definesTreeOf(symbol)
      }
      // TODO: read modifiers
      skipModifiers(end)
      typedef
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
        assert(reader.readByte() == TYPEBOUNDStpt, posErrorMsg)
        val end = reader.readEnd()
        val low = readTypeTree
        val high = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
        // assert atEnd: no alias for type parameters
        assert(reader.currentAddr == end, posErrorMsg)
        TypeBoundsTree(low, high)
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
      val paramSymbol = localCtx.getSymbol(start, RegularSymbolFactory)
      val expectedFlags = if paramSymbol.owner.isClass then ClassTypeParam else TypeParameter
      assert(paramSymbol.flags.isAllOf(expectedFlags))
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      val bounds = readTypeParamType(using localCtx.withOwner(paramSymbol))
      val typeBounds = bounds match
        case bounds: TypeBounds     => bounds
        case bounds: TypeBoundsTree => bounds.toTypeBounds
        case bounds: TypeLambdaTree => RealTypeBounds(NothingType, AnyType)
      paramSymbol.withDeclaredType(WildcardTypeBounds(typeBounds))
      skipModifiers(end)
      TypeParam(name, bounds, paramSymbol)(spn).definesTreeOf(paramSymbol)
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
    val high = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
    val alias = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
    BoundedTypeTree(TypeBoundsTree(low, high), alias)(spn)
  }

  private def readTypeBoundsTree(using LocalContext): TypeBoundsTree = {
    assert(tagFollowShared == TYPEBOUNDStpt, posErrorMsg)
    readPotentiallyShared({
      reader.readByte()
      val end = reader.readEnd()
      val low = readTypeTree
      val high = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
      TypeBoundsTree(low, high)
    })
  }

  // TODO: classinfo of the owner
  private def readTemplate(using LocalContext): Template = {
    val spn = span
    reader.readByte()
    val end = reader.readEnd()
    val cls = localCtx.owner.asClass
    val tparams = readTypeParams
    cls.withTypeParams(tparams.map(_.symbol), tparams.map(_.computeDeclarationTypeBounds()))
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
    def parentsTpes = parents.map {
      case parent: Apply    => parent.tpe
      case parent: Block    => parent.tpe
      case parent: TypeTree => parent.toType
    }
    cls.withDeclaredType(ClassInfo.defer(cls, parentsTpes))
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

  private def readSelf(using LocalContext): ValDef =
    if (reader.nextByte != SELFDEF) {
      reusable.EmptyValDef
    } else {
      val spn = span
      reader.readByte()
      val name = readName
      val tpt = readTypeTree
      // no symbol for self, because it's never referred to by symbol
      ValDef(name, tpt, EmptyTree, NoSymbol)(tpt.span)
    }

  private def readValOrDefDef(using LocalContext): Tree = {
    val spn = span
    val start = reader.currentAddr
    val tag = reader.readByte()
    val end = reader.readEnd()
    val name = readName
    // Only for DefDef, but reading works for empty lists
    val symbol = localCtx.getSymbol(start, RegularSymbolFactory)
    val insideCtx = localCtx.withOwner(symbol)
    val params = readAllParams(using insideCtx)
    val tpt = readTypeTree(using insideCtx)
    val rhs =
      if (reader.currentAddr == end || isModifierTag(reader.nextByte)) EmptyTree
      else readTerm(using insideCtx)
    skipModifiers(end)
    tag match {
      case VALDEF | PARAM =>
        symbol.withDeclaredType(tpt.toType)
        ValDef(name, tpt, rhs, symbol)(spn).definesTreeOf(symbol)
      case DEFDEF =>
        symbol.withDeclaredType(makeDefDefType(params, tpt))
        DefDef(name, params, tpt, rhs, symbol)(spn).definesTreeOf(symbol)
    }
  }

  private def makeDefDefType(paramLists: List[ParamsClause], resultTpt: TypeTree): Type =
    def rec(paramLists: List[ParamsClause]): Type =
      paramLists match
        case Left(params) :: rest =>
          val paramNames = params.map(_.name)
          val paramTypes = params.map(_.tpt.toType)
          MethodType(paramNames, paramTypes, rec(rest))
        case Right(tparams) :: rest =>
          PolyType.fromParams(tparams, rec(rest))
        case Nil =>
          resultTpt.toType

    if paramLists.isEmpty then ExprType(resultTpt.toType)
    else rec(paramLists)
  end makeDefDefType

  private def readTerms(end: Addr)(using LocalContext): List[Tree] =
    reader.until(end)(readTerm)

  extension [T <: DefTree](tree: T)
    /** Adds `tree` to the `symbol`, returning the tree.
      * @todo remove and assign tree to symbol in ctor of tree
      */
    inline def definesTreeOf[S <: Symbol](symbol: S)(using inline ev: NotGiven[T <:< PackageDef]): T =
      symbol.withTree(tree)
      tree

  private def readTerm(using LocalContext): Tree = reader.nextByte match {
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readType
      FreeIdent(name, typ)(spn)
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
      Select(qual, name)(spn)
    case QUALTHIS =>
      val spn = span
      reader.readByte()
      val qualifier = readTypeTree.asInstanceOf[TypeIdent]
      This(Some(qualifier))(spn)
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
      SelectIn(qual, name, owner)(spn)
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
      val finalizer = reader.ifBefore(end)(readTerm, EmptyTree)
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
      val tpt = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
      Lambda(method, tpt)(spn)
    case MATCH =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      if (reader.nextByte == IMPLICIT) {
        reader.readByte()
        new InlineMatch(EmptyTree, readCases[CaseDef](CaseDefFactory, end))(spn)
      } else if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineMatch(readTerm, readCases[CaseDef](CaseDefFactory, end))(spn)
      } else Match(readTerm, readCases[CaseDef](CaseDefFactory, end))(spn)
    case BIND =>
      val spn = span
      val start = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val name = readName
      // TODO: use type
      val typ = readType
      val term = readTerm
      skipModifiers(end)
      val symbol = localCtx.getSymbol(start, RegularSymbolFactory)
      Bind(name, term, symbol)(spn).definesTreeOf(symbol)
    case ALTERNATIVE =>
      reader.readByte()
      val end = reader.readEnd()
      val terms = reader.until(end)(readTerm)
      Alternative(terms)(spanSeq(terms))
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
      val patterns = reader.until(end)(readTerm)
      Unapply(fun, args, patterns)(spn)
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
      val from = readSymRef
      val expr = reader.ifBefore(end)(readTerm, EmptyTree)
      // TODO: always just taking the name?
      // return always returns from a method, i.e. something with a TermName
      Return(expr, TermRefTree(from.name.asInstanceOf[TermName], TermRef(NoPrefix, from))(trtSpan))(spn)
    case INLINED =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val expr = readTerm
      val caller: TypeIdent =
        reader.ifBefore(end)(
          tagFollowShared match {
            // The caller is not specified, this is a binding (or next val or def)
            case VALDEF | DEFDEF => EmptyTypeIdent
            case _               => readTypeTree.asInstanceOf[TypeIdent]
          },
          EmptyTypeIdent
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
      This(Some(TypeIdent(typ.name)(typ)(spn)))(spn)
    case TERMREF =>
      val spn = span
      reader.readByte()
      val name = readName
      val prefix = readType
      TermRefTree(name, TermRef(prefix, name))(spn)
    case TERMREFpkg =>
      val spn = span
      reader.readByte()
      val name = readFullyQualifiedName
      // TODO: create a termref and store as a tpe
      new ReferencedPackage(name)(spn)
    case TERMREFdirect =>
      val spn = span
      reader.readByte()
      val sym = readSymRef
      assert(sym.name.isInstanceOf[TermName], posErrorMsg)
      val tpe = TermRef(NoPrefix, sym)
      TermRefTree(sym.name.asInstanceOf[TermName], tpe)(spn)
    case TERMREFsymbol =>
      val spn = span
      reader.readByte()
      val sym = readSymRef
      val pre = readType
      assert(sym.name.isInstanceOf[TermName], posErrorMsg)
      TermRefTree(sym.name.asInstanceOf[TermName], TermRef(pre, sym))(spn)
    case SHAREDtype =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readTerm.withSpan(spn)
    case tag if isConstantTag(tag) =>
      val spn = span
      Literal(readConstant)(spn)
    case tag =>
      throw TreeUnpicklerException(s"Unexpected term tag ${astTagToString(tag)} $posErrorMsg")
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
        val pattern = readTerm
        val body = readTerm
        CaseDef(pattern, reader.ifBefore(end)(readTerm, EmptyTree), body)(spn)
      case TypeCaseDefFactory =>
        TypeCaseDef(readTypeTree, readTypeTree)
    }
  }

  private def readSymRef(using LocalContext): Symbol = {
    val symAddr = reader.readAddr()
    assert(localCtx.hasSymbolAt(symAddr), posErrorMsg)
    localCtx.getSymbol(symAddr)
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
      val sym = readSymRef
      TypeRef(NoPrefix, sym)
    case TYPEREFsymbol =>
      reader.readByte()
      val sym = readSymRef
      TypeRef(readType, sym)
    case TYPEREFpkg =>
      reader.readByte()
      PackageTypeRef(readFullyQualifiedName)
    case SHAREDtype =>
      reader.readByte()
      val addr = reader.readAddr()
      recursiveTypeAtAddr.getOrElse(addr, sharedTypesCache.getOrElseUpdate(addr, forkAt(addr).readType))
    case TERMREFdirect =>
      reader.readByte()
      val sym = readSymRef
      TermRef(NoPrefix, sym)
    case TERMREFsymbol =>
      reader.readByte()
      val sym = readSymRef
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
      ThisType(readType.asInstanceOf[TypeRef])
    case QUALTHIS =>
      reader.readByte()
      if (tagFollowShared != IDENTtpt) {
        throw TreeUnpicklerException(s"Unexpected tag after QUALTHIS: ${astTagToString(tagFollowShared)} $posErrorMsg")
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
    case TYPELAMBDAtype =>
      val lambdaAddr = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val resultUnpickler = fork // remember where the result type is
      skipTree() // skip the result type
      val paramTypeBoundsUnpickler = fork // remember where the params are
      val paramNames = reader.until(end) {
        skipTree() // skip the type bounds
        readName.toTypeName
      }
      def readParamTypeBounds()(using LocalContext): List[TypeBounds] =
        paramTypeBoundsUnpickler.reader.until(end) {
          val bounds = paramTypeBoundsUnpickler.readTypeBounds
          paramTypeBoundsUnpickler.reader.readNat() // skip name
          bounds
        }
      TypeLambda.rec(paramNames)(
        tl => readParamTypeBounds()(using localCtx.withEnclosingBinders(lambdaAddr, tl)),
        tl => resultUnpickler.readType(using localCtx.withEnclosingBinders(lambdaAddr, tl))
      )
    case PARAMtype =>
      reader.readByte()
      reader.readEnd()
      val lambdaAddr = reader.readAddr()
      val num = reader.readNat()
      localCtx.getEnclosingBinders(lambdaAddr).asInstanceOf[TypeBinders].paramRefs(num)
    case REFINEDtype =>
      reader.readByte()
      val end = reader.readEnd()
      val refinementName = readName
      val underlying = readType
      if tagFollowShared == TYPEBOUNDS then
        // Type refinement with a type member of the form `Underlying { type refinementName <:> TypeBounds }`
        val refinedMemberBounds = readTypeBounds
        RefinedType(underlying, refinementName.toTypeName, refinedMemberBounds)
      else
        // Type refinement with a term member of the form `Underlying { def refinementName: Type }`
        // TODO Actually take the refined member type into account
        reader.goto(end)
        underlying
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
    case tag if (isConstantTag(tag)) =>
      ConstantType(readConstant)
    case tag =>
      throw TreeUnpicklerException(s"Unexpected type tag ${astTagToString(tag)} $posErrorMsg")
  }

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
      val cls = ClassSymbolFactory.createRefinedClassSymbol(localCtx.owner, spn)
      recursiveTypeAtAddr(reader.currentAddr) = cls.typeRef
      reader.readByte()
      val end = reader.readEnd()
      val parent = readTypeTree
      val statements = readStats(end)(using localCtx.withOwner(cls))
      RefinedTypeTree(parent, statements, cls)(spn)
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
        if (tagFollowShared == CASEDEF)
          (EmptyTypeTree, selOrBound)
        else (selOrBound, readTypeTree)
      MatchTypeTree(bound, selector, readCases[TypeCaseDef](TypeCaseDefFactory, end))(spn)
    // TODO: why in TYPEAPPLY?
    // in MATCHtpt, TYPEAPPLY
    case BIND =>
      val spn = span
      val start = reader.currentAddr
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      // TODO: use type bounds
      val typ = readTypeBounds
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
      skipModifiers(end)
      val sym = localCtx.getSymbol(start, RegularSymbolFactory)
      TypeTreeBind(name, body, sym)(spn).definesTreeOf(sym)
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
      throw TreeUnpicklerException(s"Unexpected type tree tag ${astTagToString(tag)} $posErrorMsg")
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

object TreeUnpickler {

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

    private def registerSym[T <: Symbol](addr: Addr, sym: T, addToDecls: Boolean): T =
      localSymbols(addr) = sym
      if addToDecls then
        owner match
          case owner: DeclaringSymbol => owner.addDecl(sym)
          case _ => throw IllegalArgumentException(s"can not add $sym to decls of non-declaring symbol $owner")
      sym

    /** Creates a new symbol at @addr with @name. If `addToDecls` is true, the symbol is added to the owner's
      * declarations: this requires that the owner is a `DeclaringSymbol`, or else throws.
      *
      * @note `addToDecls` should be `true` for ValDef and DefDef, `false` for parameters and type parameters.
      * @note A method is added to the declarations of its class, but a nested method should not added
      *    to declarations of the outer method.
      */
    def createSymbol[T <: Symbol](addr: Addr, name: Name, factory: ClosedSymbolFactory[T], addToDecls: Boolean)(
      using Context
    ): T =
      if !hasSymbolAt(addr) then registerSym(addr, factory.createSymbol(name, owner), addToDecls)
      else throw ExistingDefinitionException(owner, name)

    def getSymbol(addr: Addr): Symbol =
      localSymbols(addr)
    def getSymbol[T <: Symbol](addr: Addr, symbolFactory: SymbolFactory[T]): T =
      symbolFactory.castSymbol(localSymbols(addr))
  }

}
