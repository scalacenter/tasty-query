package tastyquery.reader

import tastyquery.Contexts._
import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names._
import tastyquery.ast.Symbols.{DummySymbol, Symbol}
import tastyquery.ast.Trees._
import tastyquery.ast.TypeTrees._
import tastyquery.ast.Types._
import tastyquery.reader.TastyUnpickler.NameTable

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyReader}
import TastyBuffer._
import TastyFormat._
import TastyReader._

class TreeUnpicklerException(msg: String) extends RuntimeException(msg)

sealed trait AbstractCaseDefFactory[CaseDefType]
case object CaseDefFactory     extends AbstractCaseDefFactory[CaseDef]
case object TypeCaseDefFactory extends AbstractCaseDefFactory[TypeCaseDef]

class TreeUnpickler(protected val reader: TastyReader, nameAtRef: NameTable) {
  def unpickle(using Context): List[Tree] = {
    @tailrec def read(acc: ListBuffer[Tree]): List[Tree] = {
      acc += readTopLevelStat
      if (!reader.isAtEnd) read(acc) else acc.toList
    }
    read(new ListBuffer[Tree])
  }

  def forkAt(start: Addr): TreeUnpickler =
    new TreeUnpickler(reader.subReader(start, reader.endAddr), nameAtRef)

  def fork: TreeUnpickler =
    forkAt(reader.currentAddr)

  def skipTree(tag: Int): Unit =
    if (tag >= firstLengthTreeTag) reader.goto(reader.readEnd())
    else if (tag >= firstNatASTTreeTag) { reader.readNat(); skipTree() }
    else if (tag >= firstASTTreeTag) skipTree()
    else if (tag >= firstNatTreeTag) reader.readNat()

  def skipTree(): Unit = skipTree(reader.readByte())

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

  /**
   * Performs the read action as if SHARED tags were transparent:
   *  - follows the SHARED tags to the term or type that is shared
   *  - reads the shared term or type with {@code read} action
   *  - restores the reader to seamlessly continue reading after the SHARED tag we started from
   */
  def readPotentiallyShared[T](read: => T): T =
    if (isSharedTag(reader.nextByte)) {
      reader.readByte()
      val addr     = reader.readAddr()
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

  def readName: TermName = nameAtRef(reader.readNameRef())

  def readTopLevelStat(using Context): Tree = reader.nextByte match {
    case PACKAGE =>
      reader.readByte()
      val packageEnd = reader.readEnd()
      assert(reader.readByte() == TERMREFpkg, reader.currentAddr)
      // TODO: only create a symbol if it does not exist yet
      val pid = new Symbol(readName)
      PackageDef(pid, reader.until(packageEnd)(readTopLevelStat))
    case _ => readStat
  }

  def readStats(end: Addr)(using Context): List[Tree] =
    reader.until(end)(readStat)

  def readStat(using Context): Tree = reader.nextByte match {
    case IMPORT =>
      def readSelector: ImportSelector = {
        assert(reader.nextByte == IMPORTED, reader.currentAddr)
        reader.readByte()
        val name = Ident(readName)
        // IMPORTED can be followed by RENAMED or BOUNDED
        reader.nextByte match {
          case RENAMED =>
            reader.readByte()
            val renamed = Ident(readName)
            ImportSelector(name, renamed)
          case BOUNDED =>
            reader.readByte()
            ???
          case _ => ImportSelector(name)
        }
      }
      reader.readByte()
      val end  = reader.readEnd()
      val qual = readTerm
      Import(qual, reader.until(end)(readSelector))
    case TYPEDEF =>
      val start = reader.currentAddr
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName.toTypeName
      val typedef: Class | TypeMember = if (reader.nextByte == TEMPLATE) {
        ctx.createClassSymbolIfNew(start, name)
        Class(name, readTemplate)
      } else {
        ctx.createSymbolIfNew(start, name)
        if (tagFollowShared == TYPEBOUNDS)
          TypeMember(name, readTypeBounds)
        else
          TypeMember(name, readTypeTree)
      }
      // TODO: read modifiers
      skipModifiers(end)
      typedef
    case VALDEF | DEFDEF => readValOrDefDef
    case _               => readTerm
  }

  /** Reads type bounds for a synthetic typedef */
  def readTypeBounds(using Context): TypeBounds = {
    assert(tagFollowShared == TYPEBOUNDS, reader.currentAddr)
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

  def readTypeParams(using Context): List[TypeParam] = {
    def readTypeParamType(using Context): TypeBounds | TypeBoundsTree | TypeLambdaTree = {
      def readTypeBoundsType(using Context): TypeBounds = {
        assert(reader.readByte() == TYPEBOUNDS, reader.currentAddr)
        val end = reader.readEnd()
        val low = readType
        // type bounds for type parameters have to be bounds, not an alias
        assert(reader.currentAddr != end && !isModifierTag(reader.nextByte), reader.currentAddr)
        val high = readType
        // TODO: read variance (a modifier)
        skipModifiers(end)
        RealTypeBounds(low, high)
      }

      def readTypeBoundsTree(using Context): TypeBoundsTree = {
        assert(reader.readByte() == TYPEBOUNDStpt, reader.currentAddr)
        val end  = reader.readEnd()
        val low  = readTypeTree
        val high = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
        // assert atEnd: no alias for type parameters
        assert(reader.currentAddr == end, reader.currentAddr)
        TypeBoundsTree(low, high)
      }

      def readLambdaTpt(using Context): TypeLambdaTree = {
        assert(reader.nextByte == LAMBDAtpt, reader.currentAddr)
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
      val start = reader.currentAddr
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName.toTypeName
      ctx.createSymbolIfNew(start, name)
      val bounds = readTypeParamType
      skipModifiers(end)
      TypeParam(name, bounds)
    }
    var acc = new ListBuffer[TypeParam]()
    while (reader.nextByte == TYPEPARAM) {
      acc += readTypeParam
    }
    acc.toList
  }

  /** Reads TYPEBOUNDStpt of a typedef */
  def readBoundedTypeTree(using Context): BoundedTypeTree = {
    assert(reader.readByte() == TYPEBOUNDStpt, reader.currentAddr)
    val end   = reader.readEnd()
    val low   = readTypeTree
    val high  = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
    val alias = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
    BoundedTypeTree(TypeBoundsTree(low, high), alias)
  }

  // TODO: classinfo of the owner
  def readTemplate(using Context): Template = {
    reader.readByte()
    val end     = reader.readEnd()
    val tparams = readTypeParams
    val params  = readParams
    val parents: List[Apply | TypeTree] = reader.collectWhile(reader.nextByte != SELFDEF && reader.nextByte != DEFDEF) {
      reader.nextByte match {
        // class parents of classes are APPLYs, because they specify the constructor
        case APPLY => readTerm.asInstanceOf[Apply]
        case _     => readTypeTree
      }
    }
    val classParent  = parents.collect { case p: Apply => p }.headOption
    val traitParents = parents.collect { case p: TypeTree => p }
    val self         = readSelf
    // The first entry is the constructor
    val cstr = readStat.asInstanceOf[DefDef]
    val body = readStats(end)
    Template(cstr, classParent, traitParents, self, tparams ++ params ++ body)
  }

  def readParamLists(using Context): List[List[ValDef]] = {
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

  def readParams(using Context): List[ValDef] = {
    var acc = new ListBuffer[ValDef]()
    while (reader.nextByte == PARAM) {
      acc += readValOrDefDef.asInstanceOf[ValDef]
    }
    if (reader.nextByte == SPLITCLAUSE) {
      reader.readByte()
    }
    acc.toList
  }

  def readSelf(using Context): ValDef =
    if (reader.nextByte != SELFDEF) {
      EmptyValDef
    } else {
      reader.readByte()
      val name = readName
      val tpt  = readTypeTree
      ValDef(name, tpt, EmptyTree)
    }

  def readValOrDefDef(using Context): Tree = {
    val start = reader.currentAddr
    val tag   = reader.readByte()
    val end   = reader.readEnd()
    val name  = readName
    ctx.createSymbolIfNew(start, name)
    // Only for DefDef, but reading works for empty lists
    val tparams = readTypeParams
    val params  = readParamLists
    val tpt     = readTypeTree
    val rhs     = if (reader.currentAddr == end || isModifierTag(reader.nextByte)) EmptyTree else readTerm
    skipModifiers(end)
    tag match {
      case VALDEF | PARAM => ValDef(name, tpt, rhs)
      case DEFDEF =>
        DefDef(name, tparams, params, tpt, rhs)
    }
  }

  def readTerms(end: Addr)(using Context): List[Tree] =
    reader.until(end)(readTerm)

  def readTerm(using Context): Tree = reader.nextByte match {
    case IDENT =>
      reader.readByte()
      val name = readName
      val typ  = readType
      // TODO: assign type
      Ident(name)
    case APPLY =>
      reader.readByte()
      val end  = reader.readEnd()
      val fn   = readTerm
      val args = readTerms(end)
      Apply(fn, args)
    case NAMEDARG =>
      reader.readByte()
      NamedArg(readName, readTerm)
    case TYPEAPPLY =>
      reader.readByte()
      val end = reader.readEnd()
      val fn  = readTerm
      TypeApply(fn, reader.until(end)(readTypeTree))
    case SELECT =>
      reader.readByte()
      val name = readName
      val qual = readTerm
      Select(qual, name)
    case QUALTHIS =>
      reader.readByte()
      val qualifier = readTypeTree.asInstanceOf[TypeIdent]
      This(Some(qualifier))
    case SUPER =>
      reader.readByte()
      val end   = reader.readEnd()
      val qual  = readTerm
      val mixin = reader.ifBefore(end)(Some(readTypeTree.asInstanceOf[TypeIdent]), None)
      Super(qual, mixin)
    case SELECTin =>
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName
      val qual = readTerm
      // TODO: use owner
      val owner = readType
      Select(qual, name)
    case NEW =>
      reader.readByte()
      val cls = readTypeTree
      New(cls)
    case TYPED =>
      reader.readByte()
      reader.readEnd()
      Typed(readTerm, readTypeTree)
    case THROW =>
      reader.readByte()
      val thrown = readTerm
      Throw(thrown)
    case TRY =>
      reader.readByte()
      val end        = reader.readEnd()
      val expr       = readTerm
      val catchCases = readCases[CaseDef](CaseDefFactory, end)
      val finalizer  = reader.ifBefore(end)(readTerm, EmptyTree)
      Try(expr, catchCases, finalizer)
    case ASSIGN =>
      reader.readByte()
      reader.readEnd()
      Assign(readTerm, readTerm)
    case BLOCK =>
      reader.readByte()
      val end  = reader.readEnd()
      val expr = readTerm
      Block(readStats(end), expr)
    case IF =>
      reader.readByte()
      reader.readEnd()
      if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineIf(readTerm, readTerm, readTerm)
      } else {
        If(readTerm, readTerm, readTerm)
      }
    case LAMBDA =>
      reader.readByte()
      val end    = reader.readEnd()
      val method = readTerm
      val tpt    = reader.ifBefore(end)(readTypeTree, EmptyTypeTree)
      Lambda(method, tpt)
    case MATCH =>
      reader.readByte()
      val end = reader.readEnd()
      if (reader.nextByte == IMPLICIT) {
        reader.readByte()
        new InlineMatch(EmptyTree, readCases[CaseDef](CaseDefFactory, end))
      } else if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineMatch(readTerm, readCases[CaseDef](CaseDefFactory, end))
      } else Match(readTerm, readCases[CaseDef](CaseDefFactory, end))
    case BIND =>
      val start = reader.currentAddr
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName
      ctx.createSymbolIfNew(start, name)
      // TODO: use type
      val typ  = readType
      val term = readTerm
      skipModifiers(end)
      Bind(name, term)
    case ALTERNATIVE =>
      reader.readByte()
      val end = reader.readEnd()
      Alternative(reader.until(end)(readTerm))
    case UNAPPLY =>
      reader.readByte()
      val end = reader.readEnd()
      val fun = readTerm
      val args = reader.collectWhile(reader.nextByte == IMPLICITarg)({
        assert(reader.readByte() == IMPLICITarg, reader.currentAddr)
        readTerm
      })
      // TODO: use pattern type
      val patType  = readType
      val patterns = reader.until(end)(readTerm)
      Unapply(fun, args, patterns)
    case REPEATED =>
      reader.readByte()
      val end      = reader.readEnd()
      val elemType = readTypeTree
      SeqLiteral(reader.until(end)(readTerm), elemType)
    case WHILE =>
      reader.readByte()
      reader.readEnd()
      While(readTerm, readTerm)
    case RETURN =>
      reader.readByte()
      val end  = reader.readEnd()
      val from = readSymRef
      val expr = reader.ifBefore(end)(readTerm, EmptyTree)
      // TODO: always just taking the name?
      // return always returns from a method, i.e. something with a TermName
      Return(expr, Ident(from.name.asInstanceOf[TermName]))
    case INLINED =>
      reader.readByte()
      val end  = reader.readEnd()
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
      Inlined(expr, caller, bindings)
    case SHAREDterm =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm

    // paths
    case THIS =>
      reader.readByte()
      val typ = readType
      // TODO: assign type
      This(None)
    case TERMREF =>
      reader.readByte()
      val name = readName
      val typ  = readType
      // TODO: use type
      // TODO: this might be more complicated than Ident
      Ident(name)
    case TERMREFpkg =>
      DummyTree(readType, "TermRef into tree")
    case TERMREFdirect =>
      reader.readByte()
      val sym = readSymRef
      // TODO: assign type
      assert(sym.name.isInstanceOf[TermName], reader.currentAddr)
      Ident(sym.name.asInstanceOf[TermName])
    // TODO: is it always Ident?
    case TERMREFsymbol =>
      reader.readByte()
      val sym = readSymRef
      val typ = readType
      assert(sym.name.isInstanceOf[TermName], reader.currentAddr)
      // TODO: assign type
      Ident(sym.name.asInstanceOf[TermName])
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm
    case tag if isConstantTag(tag) =>
      Literal(readConstant)
    case tag =>
      throw TreeUnpicklerException(s"Unexpected term tag ${astTagToString(tag)} at address ${reader.currentAddr}")
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

  def readCases[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T], end: Addr)(using Context): List[T] =
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

  def readCaseDef[T <: CaseDef | TypeCaseDef](factory: AbstractCaseDefFactory[T])(using Context): T = {
    assert(reader.readByte() == CASEDEF, reader.currentAddr)
    val end = reader.readEnd()
    factory match {
      case CaseDefFactory =>
        val pattern = readTerm
        val body    = readTerm
        CaseDef(pattern, reader.ifBefore(end)(readTerm, EmptyTree), body)
      case TypeCaseDefFactory =>
        TypeCaseDef(readTypeTree, readTypeTree)
    }
  }

  def readSymRef(using Context): Symbol = {
    val symAddr = reader.readAddr()
    if (!ctx.localSymbols.contains(symAddr)) {
      // will create the symbol
      forkAt(symAddr).readStat
      assert(ctx.localSymbols.contains(symAddr), reader.currentAddr)
    }
    ctx.localSymbols(symAddr)
  }

  def readType(using Context): Type = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readType, name)
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
      PackageTypeRef(readName)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readType
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
      val name = readName
      TermRef(DummyType, name)
    case TERMREF =>
      reader.readByte()
      val name = readName
      TermRef(readType, name)
    case APPLIEDtype =>
      reader.readByte()
      val end   = reader.readEnd()
      val tycon = readType
      // TODO: type operations can be much more complicated
      AppliedType(tycon, reader.until(end)(readType))
    case THIS =>
      reader.readByte()
      ThisType(readType.asInstanceOf[TypeRef])
    case ANNOTATEDtype =>
      reader.readByte()
      reader.readEnd()
      val typ   = readType
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
    case TYPELAMBDAtype =>
      val lambdaAddr = reader.currentAddr
      reader.readByte()
      val end             = reader.readEnd()
      val resultUnpickler = fork
      // skip the result type: it might refer to the parameters, which we haven't read yet
      skipTree()
      val params = reader.until(end)({
        val bounds = readTypeBounds
        val name   = readName.toTypeName
        TypeParam(name, bounds)
      })
      TypeLambda(params, (tl: TypeLambda) => resultUnpickler.readType (using ctx.withEnclosingLambda(lambdaAddr, tl)))
    case PARAMtype =>
      reader.readByte()
      reader.readEnd()
      val lambdaAddr = reader.readAddr()
      val num        = reader.readNat()
      TypeParamRef(ctx.enclosingLambdas(lambdaAddr), num)
    case tag if (isConstantTag(tag)) =>
      ConstantType(readConstant)
    case tag =>
      throw TreeUnpicklerException(s"Unexpected type tag ${astTagToString(tag)} at address ${reader.currentAddr}")
  }

  def readTypeTree(using Context): TypeTree = reader.nextByte match {
    case IDENTtpt =>
      reader.readByte()
      val typeName = readName.toTypeName
      val typ      = readType
      // TODO: assign type
      TypeIdent(typeName)
    case SINGLETONtpt =>
      reader.readByte()
      SingletonTypeTree(readTerm)
    case REFINEDtpt =>
      reader.readByte()
      val end = reader.readEnd()
      RefinedTypeTree(readTypeTree, readStats(end))
    case APPLIEDtpt =>
      reader.readByte()
      val end   = reader.readEnd()
      val tycon = readTypeTree
      AppliedTypeTree(tycon, reader.until(end)(readTypeTree))
    case LAMBDAtpt =>
      reader.readByte()
      reader.readEnd()
      TypeLambdaTree(readTypeParams, readTypeTree)
    // select type from a term
    case SELECT =>
      reader.readByte()
      val name = readName.toTypeName
      val qual = readTerm
      SelectTypeFromTerm(qual, name)
    case SELECTtpt =>
      reader.readByte()
      val name = readName.toTypeName
      SelectTypeTree(readTypeTree, name)
    case ANNOTATEDtpt =>
      reader.readByte()
      reader.readEnd()
      AnnotatedTypeTree(readTypeTree, readTerm)
    case MATCHtpt =>
      reader.readByte()
      val end        = reader.readEnd()
      val selOrBound = readTypeTree
      val (bound, selector) =
        if (tagFollowShared == CASEDEF)
          (EmptyTypeTree, selOrBound)
        else (selOrBound, readTypeTree)
      MatchTypeTree(bound, selector, readCases[TypeCaseDef](TypeCaseDefFactory, end))
    // TODO: why in TYPEAPPLY?
    // in MATCHtpt, TYPEAPPLY
    case BIND =>
      val start = reader.currentAddr
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName.toTypeName
      ctx.createSymbolIfNew(start, name)
      // TODO: use type
      val typ  = readTypeBounds
      val body = readTypeTree
      skipModifiers(end)
      TypeTreeBind(name, body)
    // Type tree for a type member (abstract or bounded opaque)
    case TYPEBOUNDStpt => readBoundedTypeTree
    case BYNAMEtpt =>
      reader.readByte()
      ByNameTypeTree(readTypeTree)
    case SHAREDterm =>
      reader.readByte()
      forkAt(reader.readAddr()).readTypeTree
    case tag if isTypeTreeTag(tag) =>
      throw TreeUnpicklerException(s"Unexpected type tree tag ${astTagToString(tag)} at address ${reader.currentAddr}")
    case _ => TypeWrapper(readType)
  }

  def readConstant(using Context): Constant = reader.readByte() match {
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
  def skipModifiers(end: Addr)(using Context): Unit = {
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
