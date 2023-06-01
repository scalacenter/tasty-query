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

private[tasties] class TreeUnpickler private (
  filename: String,
  protected val reader: TastyReader,
  nameAtRef: NameTable,
  posUnpicklerOpt: Option[PositionUnpickler],
  caches: TreeUnpickler.Caches
)(using Context) {
  import TreeUnpickler.*

  def this(filename: String, reader: TastyReader, nameAtRef: NameTable, posUnpicklerOpt: Option[PositionUnpickler])(
    using Context
  ) = this(filename, reader, nameAtRef, posUnpicklerOpt, new TreeUnpickler.Caches)

  def unpickle(): List[Tree] =
    @tailrec
    def read(acc: ListBuffer[Tree]): List[Tree] =
      acc += readTopLevelStat
      if !reader.isAtEnd then read(acc) else acc.toList

    fork.enterSymbols()
    val result = read(new ListBuffer[Tree])

    // Check that all the Symbols we created have been completed
    for sym <- caches.allRegisteredSymbols do sym.checkCompleted()

    result
  end unpickle

  private def enterSymbols(): Unit =
    while !reader.isAtEnd do createSymbols(defn.RootPackage)

  /* This method walks a TASTy file and creates all symbols in it.
   *
   * This is useful for forward references. Example: type parameters in the following case:
   * class ExampleClass[T1 <: T2, T2]
   * The example is equally applicable to methods, which can be arbitrarily nested.
   * The alternative is to create a symbol when we encounter a forward reference, but it is hard to
   * keep track of the owner in this case.
   * */
  private def createSymbols(owner: Symbol): Unit = {
    val start = reader.currentAddr
    val tag = reader.readByte()
    tag match {
      // ---------- tags that trigger symbol creation -----------------------------------
      case PACKAGE =>
        val end = reader.readEnd()
        val sym = readPotentiallyShared({
          assert(reader.readByte() == TERMREFpkg, posErrorMsg)
          ctx.findPackageFromRootOrCreate(readFullyQualifiedName)
        })
        reader.until(end)(createSymbols(owner = sym))
      case TYPEDEF =>
        val end = reader.readEnd()
        val name = readName.toTypeName
        val tag = reader.nextByte
        val sym =
          if tag == TEMPLATE then ClassSymbol.create(name, owner)
          else TypeMemberSymbol.create(name, owner)
        caches.registerSym(start, sym)
        readSymbolModifiers(sym, tag, end)
        reader.until(end)(createSymbols(owner = sym))
      case DEFDEF | VALDEF | PARAM =>
        val end = reader.readEnd()
        val name = readName
        val sym = TermSymbol.create(name, owner)
        caches.registerSym(start, sym)
        readSymbolModifiers(sym, tag, end)
        reader.until(end)(createSymbols(owner = sym))
      case TYPEPARAM =>
        val end = reader.readEnd()
        val name = readName.toTypeName
        val sym =
          if owner.isClass then ClassTypeParamSymbol.create(name, owner.asClass)
          else LocalTypeParamSymbol.create(name, owner)
        caches.registerSym(start, sym)
        readSymbolModifiers(sym, tag, end)
        reader.until(end)(createSymbols(owner = sym))
      case BIND =>
        val end = reader.readEnd()
        val name = readName
        val sym =
          if tagFollowShared == TYPEBOUNDS then LocalTypeParamSymbol.create(name.toTypeName, owner)
          else TermSymbol.create(name, owner)
        caches.registerSym(start, sym)
        sym.withFlags(Case, None)
        // bind is never an owner
        reader.until(end)(createSymbols(owner))
      case REFINEDtpt =>
        val spn = spanAt(start)
        val sym = ClassSymbol.createRefinedClassSymbol(owner, EmptyFlagSet, spn)
        caches.registerSym(start, sym)
        val end = reader.readEnd()
        reader.until(end)(createSymbols(owner = sym))

      case TEMPLATE =>
        /* In a template, top-level definitions must have the enclosing class as owner.
         * However, any definition nested in a statement, such as a block, must instead
         * be owned by the primary constructor (in dotc, there is a "local dummy"
         * instead, but a similar problem essentially exists).
         * We must therefore first create the symbol for the primary constructor,
         * which is the first DEFDEF in the template. Then, we go back and create
         * everything else, passing the right owner depending on the kind of nested
         * tree.
         */
        val cls = owner.asClass
        val end = reader.readEnd()
        val parentsAndSelfDefReader = fork
        while reader.nextByte != DEFDEF do skipTree()
        val ctorAddr = reader.currentAddr
        createSymbols(owner)
        val ctor = caches.getSymbol[TermSymbol](ctorAddr)
        parentsAndSelfDefReader.reader.until(ctorAddr)(parentsAndSelfDefReader.createSymbolsInTemplate(cls, ctor))
        reader.until(end)(createSymbolsInTemplate(cls, ctor))

      // ---------- tags with potentially nested symbols --------------------------------
      case tag if firstASTTreeTag <= tag && tag < firstNatASTTreeTag => createSymbols(owner)
      case tag if firstNatASTTreeTag <= tag && tag < firstLengthTreeTag =>
        reader.readNat()
        createSymbols(owner)
      case APPLY | TYPEAPPLY | SUPER | TYPED | ASSIGN | BLOCK | INLINED | LAMBDA | IF | MATCH | TRY | WHILE | REPEATED |
          ALTERNATIVE | UNAPPLY | APPLIEDtpt | LAMBDAtpt | TYPEBOUNDStpt | ANNOTATEDtpt | MATCHtpt | CASEDEF =>
        val end = reader.readEnd()
        reader.until(end)(createSymbols(owner))
      case SELECTin =>
        val end = reader.readEnd()
        readName
        reader.until(end)(createSymbols(owner))
      case RETURN | SELECTouter =>
        val end = reader.readEnd()
        reader.readNat()
        reader.until(end)(createSymbols(owner))

      // ---------- no nested symbols ---------------------------------------------------
      case _ => skipTree(tag)
    }
  }

  private def createSymbolsInTemplate(classOwner: ClassSymbol, ctorOwner: TermSymbol): Unit =
    reader.nextByte match
      case TYPEDEF | DEFDEF | VALDEF | PARAM | TYPEPARAM =>
        createSymbols(classOwner)
      case _ =>
        createSymbols(ctorOwner)
  end createSymbolsInTemplate

  private def normalizeFlags(sym: Symbol, tag: Int, givenFlags: FlagSet, rhsIsEmpty: Boolean): FlagSet =
    var flags = givenFlags
    if tag == DEFDEF then flags |= Method
    if rhsIsEmpty && (tag == VALDEF || tag == DEFDEF) then flags |= Abstract
    if givenFlags.is(Module) then flags |= (if tag == VALDEF then ModuleValCreationFlags else ModuleClassCreationFlags)
    if flags.is(Enum) && !flags.is(Method) && sym.isTerm then flags |= StableRealizable
    if sym.owner.nn.isClass then
      if tag == PARAM then
        flags |= ParamAccessor
        if !rhsIsEmpty then // param alias
          flags |= Method
    if tag == TYPEPARAM then flags |= TypeParameter
    flags

  private def posErrorMsg: String = s"at address ${reader.currentAddr} in file $filename"
  private def posErrorMsg(atAddr: Addr): String = s"at address $atAddr in file $filename"

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
    new TreeUnpickler(filename, reader.subReader(start, reader.endAddr), nameAtRef, posUnpicklerOpt, caches)

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

  private def readSymbolModifiers(sym: Symbol, tag: Int, end: Addr): Unit =
    val modsReader = fork
    modsReader.skipParams()
    modsReader.skipTree() // tpt
    val rhsIsEmpty = modsReader.nothingButMods(end)
    if !rhsIsEmpty then modsReader.skipTree()
    val (flags, privateWithin) = modsReader.readModifiers(end)
    val normalizedFlags = normalizeFlags(sym, tag, flags, rhsIsEmpty)
    sym.withFlags(normalizedFlags, privateWithin)

  /** Read modifiers into a set of flags and a privateWithin boundary symbol. */
  private def readModifiers(end: Addr): (FlagSet, Option[Symbol]) =
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

  private def readWithin: Symbol =
    readTypeMappable() match
      case TypeRef.OfClass(cls) => cls
      case pkgRef: PackageRef   => pkgRef.symbol
      case tpe                  => throw TastyFormatException(s"unexpected type for readWithin: $tpe")
  end readWithin

  private def readAnnotationsInModifiers(sym: Symbol, end: Addr): Unit =
    var annots: List[Annotation] = Nil

    while reader.currentAddr != end && isModifierTag(reader.nextByte) do
      reader.readByte() match
        case PRIVATEqualified | PROTECTEDqualified =>
          skipTree()
        case ANNOTATION =>
          annots ::= readAnnotation()
        case _ =>
          ()
    end while

    sym.setAnnotations(annots)
  end readAnnotationsInModifiers

  private def readAnnotation(): Annotation =
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

  private def readTopLevelStat: TopLevelTree = reader.nextByte match {
    case PACKAGE =>
      val spn = span
      reader.readByte()
      val packageEnd = reader.readEnd()
      val pid = readPotentiallyShared({
        assert(reader.readByte() == TERMREFpkg, posErrorMsg)
        ctx.findPackageFromRootOrCreate(readFullyQualifiedName)
      })
      PackageDef(pid, reader.until(packageEnd)(readTopLevelStat))(spn)
    case _ => readStat
  }

  private def readStats(end: Addr): List[StatementTree] =
    reader.until(end)(readStat)

  private def readStat: StatementTree = reader.nextByte match {
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
        val classSymbol = caches.getSymbol[ClassSymbol](start)
        val template = readTemplate(classSymbol)
        definingTree(classSymbol, ClassDef(name, template, classSymbol)(spn))
      } else {
        val symbol = caches.getSymbol[TypeMemberSymbol](start)
        val isOpaque = symbol.is(Opaque)
        val typeDefTree = readTypeDefinition(forOpaque = isOpaque)
        val typeDef = makeTypeMemberDefinition(typeDefTree)
        if isOpaque != typeDef.isInstanceOf[TypeMemberDefinition.OpaqueTypeAlias] then
          throw TastyFormatException(
            s"typeDef $typeDef inconsistent with Opaque flag $isOpaque for $symbol at $posErrorMsg"
          )
        symbol.withDefinition(typeDef)
        definingTree(symbol, TypeMember(name, typeDefTree, symbol)(spn))
      }
      readAnnotationsInModifiers(typeDef.symbol, end)
      typeDef
    case VALDEF | DEFDEF => readValOrDefDef
    case _               => readTerm
  }

  /** Turns a `TypeDefinitionTree` used as the rhs of a type member into a type member definition.
    *
    * `PolyTypeDefinitionTree`s are distributed over the components of the
    * recursively transformed body.
    */
  private def makeTypeMemberDefinition(tpt: TypeDefinitionTree): TypeMemberDefinition =
    import TypeMemberDefinition.*

    tpt match
      case tpt: TypeBoundsTree =>
        AbstractType(tpt.toTypeBounds)

      case TypeAliasDefinitionTree(alias) =>
        TypeAlias(alias.toType)

      case OpaqueTypeAliasDefinitionTree(bounds, alias) =>
        OpaqueTypeAlias(bounds.toTypeBounds, alias.toType)

      case tpt @ PolyTypeDefinitionTree(_, body) =>
        makeTypeMemberDefinition(body) match
          case TypeAlias(alias) =>
            TypeAlias(tpt.integrateInto(alias))
          case AbstractType(bounds) =>
            AbstractType(bounds.mapBounds(tpt.integrateInto(_)))
          case OpaqueTypeAlias(bounds, alias) =>
            OpaqueTypeAlias(bounds.mapBounds(tpt.integrateInto(_)), tpt.integrateInto(alias))

      case _: NamedTypeBoundsTree =>
        throw TastyFormatException(s"Unexpected type member definition $tpt at $posErrorMsg")
  end makeTypeMemberDefinition

  private def readTypeDefinition(forOpaque: Boolean): TypeDefinitionTree =
    readPotentiallyShared {
      reader.nextByte match
        case TYPEBOUNDS =>
          val bounds = readTypeBounds
          if forOpaque then throw TastyFormatException(s"Unexpected abstract type bounds $bounds at $posErrorMsg")
          InferredTypeBoundsTree(bounds)(NoSpan)

        case TYPEBOUNDStpt =>
          val spn = span
          reader.readByte()
          val end = reader.readEnd()
          val low = readTypeTree
          val high = readTypeTree
          val bounds = ExplicitTypeBoundsTree(low, high)(spn)
          val result = reader.ifBefore(end)(OpaqueTypeAliasDefinitionTree(bounds, readTypeTree)(spn), bounds)
          if forOpaque != result.isInstanceOf[OpaqueTypeAliasDefinitionTree] then
            if forOpaque then throw TastyFormatException(s"Unexpected abstract type bounds $bounds at $posErrorMsg")
            else throw TastyFormatException(s"Unexpected opaque type alias definition $result at $posErrorMsg")
          end if
          result

        case LAMBDAtpt =>
          val spn = span
          reader.readByte()
          reader.readEnd()
          PolyTypeDefinitionTree(readTypeParams, readTypeDefinition(forOpaque))(spn)

        case _ =>
          val alias = readTypeTree
          if forOpaque then
            OpaqueTypeAliasDefinitionTree(InferredTypeBoundsTree(defn.NothingAnyBounds)(NoSpan), alias)(alias.span)
          else TypeAliasDefinitionTree(alias)(alias.span)
    }
  end readTypeDefinition

  private def readTypeOrWildcard(): TypeOrWildcard =
    readPotentiallyShared {
      reader.nextByte match
        case TYPEBOUNDS =>
          WildcardTypeArg(readTypeBounds)
        case _ =>
          readTrueType()
    }
  end readTypeOrWildcard

  private def readTypeOrWildcardTree(span: Span): TypeArgTree =
    readPotentiallyShared {
      reader.nextByte match
        case TYPEBOUNDS | TYPEBOUNDStpt =>
          val bounds = readTypeDefinition(forOpaque = false).asInstanceOf[TypeBoundsTree]
          WildcardTypeArgTree(bounds)(span)
        case _ =>
          readTypeTree
    }
  end readTypeOrWildcardTree

  /** Reads type bounds for a synthetic typedef */
  private def readTypeBounds: TypeBounds = {
    assert(tagFollowShared == TYPEBOUNDS, posErrorMsg)
    readPotentiallyShared({
      reader.readByte()
      val end = reader.readEnd()
      val low = readTrueType()
      if (reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
        val high = readTrueType()
        // TODO: read variance (a modifier)
        skipModifiers(end)
        RealTypeBounds(low, high)
      } else {
        skipModifiers(end)
        TypeAlias(low)
      }
    })
  }

  private def readTypeParams: List[TypeParam] = {
    def toTypeParamBounds(tpt: TypeDefinitionTree): TypeBounds = tpt match
      case tpt: TypeBoundsTree =>
        tpt.toTypeBounds
      case tpt @ PolyTypeDefinitionTree(_, body) =>
        toTypeParamBounds(body).mapBounds(tpt.integrateInto(_))
      case _ =>
        throw TastyFormatException(s"unexpected type param bounds tree $tpt at $posErrorMsg")
    end toTypeParamBounds

    def readTypeParam: TypeParam = {
      val spn = span
      val start = reader.currentAddr
      val paramSymbol = caches.getSymbol[TypeParamSymbol](start)
      reader.readByte()
      val end = reader.readEnd()
      val name = readName.toTypeName
      val typeDefTree = readTypeDefinition(forOpaque = false)
      val typeBounds = toTypeParamBounds(typeDefTree)
      paramSymbol.setBounds(typeBounds)
      readAnnotationsInModifiers(paramSymbol, end)
      definingTree(paramSymbol, TypeParam(name, typeDefTree, paramSymbol)(spn))
    }

    val acc = new ListBuffer[TypeParam]()
    while (reader.nextByte == TYPEPARAM) {
      acc += readTypeParam
    }
    acc.toList
  }

  // TODO: classinfo of the owner
  private def readTemplate(cls: ClassSymbol): Template = {
    val spn = span
    reader.readByte()
    val end = reader.readEnd()
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
        case parent: TermTree =>
          Apply.computeAppliedNewType(parent).getOrElse {
            throw InvalidProgramStructureException(s"Unexpected super call $parent in class $cls")
          }
        case parent: TypeTree => parent.toType
      }
    }
    val self = readSelf
    cls.withGivenSelfType(self.map(_.tpt.toType))
    // The first entry is the constructor
    val cstr = readStat.asInstanceOf[DefDef]
    val body = readStats(end)
    Template(cstr, parents, self, tparams ++ params ++ body)(spn)
  }

  private def readAllParams: List[ParamsClause] =
    reader.nextByte match {
      case PARAM =>
        Left(readParams) :: readAllParams
      case EMPTYCLAUSE =>
        reader.readByte()
        Left(Nil) :: readAllParams
      case TYPEPARAM =>
        Right(readTypeParams) :: readAllParams
      case SPLITCLAUSE =>
        reader.readByte()
        readAllParams
      case _ =>
        Nil
    }
  end readAllParams

  private def readParams: List[ValDef] = {
    var acc = new ListBuffer[ValDef]()
    while (reader.nextByte == PARAM) {
      acc += readValOrDefDef.asInstanceOf[ValDef]
    }
    acc.toList
  }

  private def readSelf: Option[SelfDef] =
    if (reader.nextByte != SELFDEF) {
      None
    } else {
      val spn = span
      reader.readByte()
      val name = readName
      val tpt = readTypeTree
      Some(SelfDef(name, tpt)(tpt.span))
    }

  private def readValOrDefDef: ValOrDefDef = {
    val spn = span
    val start = reader.currentAddr
    val symbol = caches.getSymbol[TermSymbol](start)
    val tag = reader.readByte()
    val end = reader.readEnd()
    val name = readName
    // Only for DefDef, but reading works for empty lists
    val params = readAllParams
    val tpt = readTypeTree
    val rhs =
      if (reader.currentAddr == end || isModifierTag(reader.nextByte)) None
      else if tag == VALDEF then Some(readTermOrUninitialized())
      else Some(readTerm)
    readAnnotationsInModifiers(symbol, end)
    tag match {
      case VALDEF | PARAM =>
        symbol.withDeclaredType(tpt.toType)
        definingTree(symbol, ValDef(name, tpt, rhs, symbol)(spn))
      case DEFDEF =>
        val normalizedParams =
          if name == nme.Constructor then normalizeCtorParamClauses(params)
          else params
        symbol.withDeclaredType(ParamsClause.makeDefDefType(normalizedParams, tpt))
        definingTree(symbol, DefDef(name, normalizedParams, tpt, rhs, symbol)(spn))
    }
  }

  /** Normalizes the param clauses of a constructor definition.
    *
    * Make sure it has at least one non-implicit parameter list. This is done
    * by adding a `()` in front of a leading old style implicit parameter,
    * or by adding a `()` as last -- or only -- parameter list if the
    * constructor has only using clauses as parameters.
    */
  private def normalizeCtorParamClauses(paramLists: List[ParamsClause]): List[ParamsClause] =
    paramLists match
      case (tparams @ Right(_)) :: paramListsTail =>
        tparams :: normalizeCtorParamClauses(paramListsTail)

      case Left(vparam1 :: _) :: _ if vparam1.symbol.is(Implicit) =>
        // Found a leading `implicit` param lists -> add `()` in front
        Left(Nil) :: paramLists

      case _ =>
        val anyNonUsingTermClause = paramLists.exists {
          case Left(vparams)  => vparams.isEmpty || !vparams.head.symbol.is(Given)
          case Right(tparams) => false
        }
        if anyNonUsingTermClause then paramLists
        else paramLists :+ Left(Nil) // add `()` at the end
  end normalizeCtorParamClauses

  private def readTerms(end: Addr): List[TermTree] =
    reader.until(end)(readTerm)

  def definingTree(symbol: Symbol, tree: symbol.DefiningTreeType): tree.type =
    symbol.withTree(tree)
    tree

  private def makeIdent(name: TermName, tpe: TermType, spn: Span): Ident =
    val tpe1: TermRef | PackageRef = tpe match
      case tpe: TermRef    => tpe
      case tpe: PackageRef => tpe
      case _ => throw TastyFormatException(s"unexpected type $tpe for Ident name $name span $spn in $posErrorMsg")
    Ident(name)(tpe1)(spn)
  end makeIdent

  private def readPattern: PatternTree = reader.nextByte match
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readTermType()
      if name == nme.Wildcard || name == nme.WildcardSequence then WildcardPattern(typ.requireType)(spn)
      else ExprPattern(makeIdent(name, typ, spn))(spn)
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
      val typ = readTrueType()
      val body = readPattern
      val symbol = caches.getSymbol[TermSymbol](start)
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
      val patType = readTrueType()
      val patterns = reader.until(end)(readPattern)
      Unapply(fun, args, patterns)(spn)
    case SHAREDterm =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readPattern.withSpan(spn)
    case _ =>
      val expr = readTerm
      ExprPattern(expr)(expr.span)
  end readPattern

  private def readTermOrUninitialized(): TermTree = reader.nextByte match
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readTermType()
      val typ1 =
        if name == nme.Wildcard then defn.uninitializedMethodTermRef
        else typ
      makeIdent(name, typ1, spn)
    case _ =>
      readTerm
  end readTermOrUninitialized

  private def readTerm: TermTree = reader.nextByte match {
    case IDENT =>
      val spn = span
      reader.readByte()
      val name = readName
      val typ = readTermType()
      val typ1 =
        if name == nme.Wildcard then
          /* This is a bit of a hack for default arguments to Java annotations with default values.
           * See simple_trees.Annotations.javaAnnotWithDefaultImplicit().
           */
          defn.uninitializedMethodTermRef
        else typ
      makeIdent(name, typ1, spn)
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
    case SELECTouter =>
      val spn = span
      reader.readByte()
      val levels = reader.readNat()
      val qual = readTerm
      val tpe = readTrueType()
      SelectOuter(qual, levels)(tpe)(spn)
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
      val mixin = reader.ifBeforeOpt(end)(readTypeTree.asInstanceOf[TypeIdent])
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
      val caller: Option[TypeIdent | SelectTypeTree] =
        reader.ifBefore(end)(
          tagFollowShared match {
            // The caller is not specified, this is a binding (or next val or def)
            case VALDEF | DEFDEF => None
            case _ =>
              readTypeTree match
                case caller: TypeIdent      => Some(caller)
                case caller: SelectTypeTree => Some(caller)
                case caller =>
                  throw TastyFormatException(s"Unexpected Inlined caller $caller $posErrorMsg")
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
      val typ = readTrueType().asInstanceOf[TypeRef]
      This(TypeIdent(typ.name)(typ)(spn))(spn)
    case TERMREF =>
      val spn = span
      reader.readByte()
      val name = readName
      val prefix = readNonEmptyPrefix()
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
      val pre = readNonEmptyPrefix()
      Ident(sym.name)(TermRef(pre, sym))(spn)
    case TERMREFin =>
      val spn = span
      reader.readByte()
      reader.readEnd()
      val name = readName
      val prefix = readNonEmptyPrefix()
      val ownerRef = readTypeRef()
      Ident(name)(TermRef(prefix, LookupIn(ownerRef, name)))(spn)
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

  private def readCases[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T], end: Addr): List[T] =
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

  private def readCaseDef[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T]): T = {
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

  private def readSymRef: Symbol = {
    val symAddr = reader.readAddr()
    assert(caches.hasSymbolAt(symAddr), posErrorMsg)
    caches.getSymbol[Symbol](symAddr)
  }

  private def readTypeRef(): TypeRef =
    readTypeMappable().asInstanceOf[TypeRef]

  private def readTrueType(): Type =
    readTypeMappable().requireType

  private def readNonEmptyPrefix(): NonEmptyPrefix =
    readTypeMappable().asInstanceOf[NonEmptyPrefix]

  private def readTypeOrMethodic(): TypeOrMethodic =
    readTypeMappable().asInstanceOf[TypeOrMethodic]

  private def readTermType(): TermType =
    readTypeMappable().asInstanceOf[TermType]

  private def readTypeMappable(): TypeMappable = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readNonEmptyPrefix(), name)
    case TYPEREFin =>
      reader.readByte()
      reader.readEnd()
      val name = readName.toTypeName
      val prefix = readNonEmptyPrefix()
      val ownerRef = readTypeRef()
      TypeRef(prefix, LookupTypeIn(ownerRef, name))
    case TYPEREFdirect =>
      reader.readByte()
      val sym = readSymRef.asType
      TypeRef(NoPrefix, sym)
    case TYPEREFsymbol =>
      reader.readByte()
      val sym = readSymRef.asType
      TypeRef(readNonEmptyPrefix(), sym)
    case TYPEREFpkg =>
      reader.readByte()
      PackageRef(readFullyQualifiedName)
    case SHAREDtype =>
      reader.readByte()
      val addr = reader.readAddr()
      caches.sharedTypesCache.getOrElseUpdate(addr, forkAt(addr).readTypeMappable())
    case TERMREFdirect =>
      reader.readByte()
      val sym = readSymRef.asTerm
      TermRef(NoPrefix, sym)
    case TERMREFsymbol =>
      reader.readByte()
      val sym = readSymRef.asTerm
      TermRef(readNonEmptyPrefix(), sym)
    case TERMREFpkg =>
      reader.readByte()
      new PackageRef(readFullyQualifiedName)
    case TERMREF =>
      reader.readByte()
      val name = readName
      TermRef(readNonEmptyPrefix(), name)
    case TERMREFin =>
      reader.readByte()
      reader.readEnd()
      val name = readName
      val prefix = readNonEmptyPrefix()
      val ownerRef = readTypeRef()
      TermRef(prefix, LookupIn(ownerRef, name))
    case APPLIEDtype =>
      reader.readByte()
      val end = reader.readEnd()
      val tycon = readTrueType()
      AppliedType(tycon, reader.until(end)(readTypeOrWildcard()))
    case THIS =>
      reader.readByte()
      readTypeMappable() match
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
      ThisType(readTrueType().asInstanceOf[TypeRef])
    case SUPERtype =>
      reader.readByte()
      reader.readEnd()
      val thistpe = readTypeMappable() match
        case thistpe: ThisType => thistpe
        case thistpe           => throw TastyFormatException(s"Unexpected this type for SuperType: $thistpe")
      val supertpe = readTrueType()
      SuperType(thistpe, Some(supertpe))
    case ANNOTATEDtype =>
      reader.readByte()
      reader.readEnd()
      val typ = readTrueType()
      val annot = readTerm
      AnnotatedType(typ, Annotation(annot))
    case ANDtype =>
      reader.readByte()
      reader.readEnd()
      AndType(readTrueType(), readTrueType())
    case ORtype =>
      reader.readByte()
      reader.readEnd()
      OrType(readTrueType(), readTrueType())
    case BYNAMEtype =>
      reader.readByte()
      ByNameType(readTrueType())
    case POLYtype =>
      readLambdaType(_ => PolyType, name => name.toTypeName, _.readTypeBounds, _.readTypeOrMethodic())
    case METHODtype =>
      // TODO Record the `mods` somehow (given, implicit, erased)
      readLambdaType(_ => MethodType, name => name, _.readTrueType(), _.readTypeOrMethodic())
    case TYPELAMBDAtype =>
      readLambdaType(_ => TypeLambda, _.toTypeName, _.readTypeBounds, _.readTrueType())
    case PARAMtype =>
      reader.readByte()
      reader.readEnd()
      val lambda = readBindersRef[ParamRefBinders]()
      val num = reader.readNat()
      lambda.paramRefs(num)
    case REFINEDtype =>
      reader.readByte()
      val end = reader.readEnd()
      val refinementName = readName
      val underlying = readTrueType()
      if tagFollowShared == TYPEBOUNDS then
        // Type refinement with a type member of the form `Underlying { type refinementName <:> TypeBounds }`
        val refinedMemberBounds = readTypeBounds
        TypeRefinement(underlying, refinementName.toTypeName, refinedMemberBounds)
      else
        // Type refinement with a term member of the form `Underlying { val/def refinementName: Type }`
        val refinedMemberType = readTypeOrMethodic()
        refinedMemberType match
          case refinedMemberType: ByNameType =>
            TermRefinement(underlying, isStable = false, refinementName, refinedMemberType.resultType)
          case _ =>
            val isStable = !refinedMemberType.isInstanceOf[MethodicType]
            TermRefinement(underlying, isStable, refinementName, refinedMemberType)
    case RECtype =>
      readRegisteringBinders { register =>
        reader.readByte()
        RecType { rt =>
          register(rt)
          readTrueType()
        }
      }
    case RECthis =>
      reader.readByte()
      readBindersRef[RecType]().recThis
    case MATCHtype =>
      val start = reader.currentAddr
      reader.readByte() // tag
      val end = reader.readEnd()
      val upperBound = readTrueType()
      val scrutinee = readTrueType()
      val cases: List[MatchTypeCase] = reader.until(end)(readMatchTypeCase)
      MatchType(upperBound, scrutinee, cases)
    case REFINEDtpt =>
      /* This is kind of a hack at the TASTy format level. A `Type` with tag
       * `REFINEDtpt` (but not a `TypeTree` with that tag!) is in fact the
       * `cls.typeRef` of the refined class `cls` implicitly declared by that
       * `REFINEDtpt`.
       */
      val start = reader.currentAddr
      skipTree()
      caches.getSymbol[ClassSymbol](start).typeRef
    case tag if (isConstantTag(tag)) =>
      ConstantType(readConstant)
    case tag =>
      throw TastyFormatException(s"Unexpected type tag ${astTagToString(tag)} $posErrorMsg")
  }

  private def readRegisteringBinders[A <: Binders](body: (A => Unit) => A): A =
    val start = reader.currentAddr
    caches.registeredBinders.get(start) match
      case Some(existing) =>
        skipTree()
        existing.asInstanceOf[A]
      case None =>
        body(result => caches.registeredBinders.update(start, result))
  end readRegisteringBinders

  private def readBindersRef[A <: Binders]()(using scala.reflect.Typeable[A]): A =
    /* Usually, we read references to binders while reading the target binders,
     * because references are always nested within the binders. That is the
     * fast path below.
     *
     * However, due to `SHAREDtype`, we sometimes read the inside of some
     * binders without going through the binders first. In that case, the
     * binders will not be registered yet, and we need to go read them first.
     */
    val addr = reader.readAddr()
    val binders = caches.registeredBinders.get(addr) match
      case Some(binders) => binders // fast path
      case None          => forkAt(addr).readTrueType()
    binders match
      case binders: A => binders
      case _          => throw TastyFormatException(s"Unexpected binders type $binders ${posErrorMsg(addr)}")
  end readBindersRef

  private def readLambdaType[N <: Name, PInfo <: Type | TypeBounds, RT <: TypeOrMethodic, LT <: LambdaType](
    companionOp: FlagSet => LambdaTypeCompanion[N, PInfo, RT, LT],
    nameMap: TermName => N,
    readInfo: TreeUnpickler => PInfo,
    readResultType: TreeUnpickler => RT
  ): LT =
    readRegisteringBinders { register =>
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
      def readParamInfos(): List[PInfo] =
        val reader = paramInfosUnpickler.reader
        reader.collectWhile(reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
          val bounds = readInfo(paramInfosUnpickler)
          reader.readNat() // skip name
          bounds
        }
      end readParamInfos

      val factory = companionOp(mods)
      factory(paramNames)(
        { tl =>
          register(tl)
          readParamInfos()
        },
        tl => readResultType(resultUnpickler)
      )
    }
  end readLambdaType

  private def readMatchTypeCase: MatchTypeCase = reader.nextByte match {
    case MATCHCASEtype =>
      reader.readByte() // tag
      reader.readEnd() // end
      val pattern = readTrueType()
      val body = readTrueType()
      MatchTypeCase(pattern, body)

    case TYPELAMBDAtype =>
      // This is unfortunately a lot of copy-past wrt. readLambdaType above

      readRegisteringBinders { register =>
        reader.readByte()
        val end = reader.readEnd()

        val matchTypeCaseUnpickler = fork // remember where the underlying MATCHCASEtype is
        skipTree() // skip the MATCHCASEtype
        val paramInfosUnpickler = fork // remember where the params are

        // Read names -- skip infos, and stop if we find a modifier
        val paramNames = reader.collectWhile(reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
          skipTree()
          readName.toTypeName
        }

        if reader.currentAddr != end then
          throw TastyFormatException(s"unexpected modifiers for match-type-case TYPELAMBDAtype at $posErrorMsg")

        // Read infos -- skip names
        def readParamInfos(): List[TypeBounds] =
          val reader = paramInfosUnpickler.reader
          reader.collectWhile(reader.currentAddr != end && !isModifierTag(reader.nextByte)) {
            val bounds = paramInfosUnpickler.readTypeBounds
            reader.readNat() // skip name
            bounds
          }
        end readParamInfos

        // Flatten out the underlying MatchTypeCase -- this is not pretty
        var resultType: Type | Null = null
        MatchTypeCase(paramNames)(
          { mtc =>
            register(mtc)
            readParamInfos()
          },
          { mtc =>
            val inner = matchTypeCaseUnpickler.readMatchTypeCase
            if inner.paramNames.nonEmpty then
              throw TastyFormatException(s"unexpected nested $inner for match-type-case at $posErrorMsg")
            resultType = inner.result
            inner.pattern
          },
          mtc => resultType.nn
        )
      }

    case SHAREDtype =>
      reader.readByte()
      val addr = reader.readAddr()
      forkAt(addr).readMatchTypeCase

    case tag =>
      throw TastyFormatException(s"Unexpected type in MATCHtype case: $tag $posErrorMsg")
  }

  private def readTypeTree: TypeTree = reader.nextByte match {
    case IDENTtpt =>
      val spn = span
      reader.readByte()
      val typeName = readName.toTypeName
      val typ = readTrueType()
      TypeIdent(typeName)(typ)(spn)
    case SINGLETONtpt =>
      val spn = span
      reader.readByte()
      SingletonTypeTree(readTerm)(spn)
    case REFINEDtpt =>
      protectReadDefiningTypeTree {
        val spn = span
        val cls = caches.getSymbol[ClassSymbol](reader.currentAddr)
        reader.readByte()
        val end = reader.readEnd()
        val parent = readTypeTree
        val statements = readStats(end)
        val refinements = statements.map {
          case memberDef: RefinementMemberDef =>
            memberDef
          case otherDef =>
            throw TastyFormatException(s"Unexpected member $otherDef in refinement type")
        }
        RefinedTypeTree(parent, refinements, cls)(spn)
      }
    case APPLIEDtpt =>
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val tycon = readTypeTree
      AppliedTypeTree(tycon, reader.until(end)(readTypeOrWildcardTree(spn)))(spn)
    case LAMBDAtpt =>
      protectReadDefiningTypeTree {
        val spn = span
        reader.readByte()
        reader.readEnd()
        TypeLambdaTree(readTypeParams, readTypeTree)(spn)
      }
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
      protectReadDefiningTypeTree {
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
        val body: TypeDefinitionTree = if (reader.nextByte == IDENT) {
          val identSpn = spn // for some reason, the span of the IDENT itself is empty, so we reuse the span of the BIND
          reader.readByte()
          val typeName = readName.toTypeName
          val typ = readTypeBounds
          NamedTypeBoundsTree(typeName, typ)(identSpn)
        } else readTypeDefinition(forOpaque = false)
        val sym = caches.getSymbol[LocalTypeParamSymbol](start)
        readAnnotationsInModifiers(sym, end)
        sym.setBounds(bounds)
        definingTree(sym, TypeTreeBind(name, body, sym)(spn))
      }
    case BYNAMEtpt =>
      val spn = span
      reader.readByte()
      ByNameTypeTree(readTypeTree)(spn)
    case BLOCK =>
      // #284 See QuotesAndSplices.typeQuoteMatching
      val spn = span
      reader.readByte()
      val end = reader.readEnd()
      val body = readTypeTree
      val bindings = readStats(end).map(_.asInstanceOf[TypeMember])
      TypeBindingsTree(bindings, body)(spn)
    case SHAREDterm =>
      val spn = span
      reader.readByte()
      forkAt(reader.readAddr()).readTypeTree.withSpan(spn)
    case tag if isTypeTreeTag(tag) =>
      throw TastyFormatException(s"Unexpected type tree tag ${astTagToString(tag)} $posErrorMsg")
    case _ =>
      TypeWrapper(readNonEmptyPrefix())(span)
  }

  private def protectReadDefiningTypeTree[A <: TypeTree](body: => A): A =
    /* It is possible to find SHAREDterm's referencing REFINEDtpt, `LAMBDAtpt`, etc.
     * This is bad because a these TypeTree's define symbols. If we read them
     * again, we will try to re-fill the information of the symbols, which is
     * not allowed. To work around this problem, we maintain a special map of
     * those "sensitive" nodes we have already read.
     *
     * A better solution would be not to rely on symbols at all; but that is
     * tricky because there are standard TYPEDEF, VALDEF and DEFDEF in the
     * REFINEDtpt, and those create trees that define symbols as well. We
     * would need a different mode of reading those nested definitions, which
     * would create other kinds of trees without symbols. The same problem
     * appears for other kinds of type trees with definitions.
     */
    val start = reader.currentAddr
    caches.definingTypeTreeCache.get(start) match
      case Some(existing) =>
        skipTree()
        existing.asInstanceOf[A]
      case None =>
        val result = body
        caches.definingTypeTreeCache(start) = result
        result
  end protectReadDefiningTypeTree

  private def readConstant: Constant = reader.readByte() match {
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
      Constant(readTrueType())
  }

  // TODO: read modifiers and return them instead
  private def skipModifiers(end: Addr): Unit = {
    def skipModifier(): Unit = reader.readByte() match {
      case PRIVATEqualified =>
        readTrueType()
        ()
      case PROTECTEDqualified =>
        readTrueType()
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

  private final class Caches:
    private val localSymbols = mutable.HashMap.empty[Addr, Symbol]

    val sharedTypesCache = mutable.Map.empty[Addr, TypeMappable]

    val definingTypeTreeCache = mutable.Map.empty[Addr, TypeTree]

    val registeredBinders = mutable.Map.empty[Addr, Binders]

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
  end Caches

  extension (reader: TastyReader)
    def ifBeforeOpt[T](end: Addr)(op: => T): Option[T] =
      reader.ifBefore(end)(Some(op), None)

}
