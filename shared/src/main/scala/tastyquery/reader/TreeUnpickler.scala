package tastyquery.reader

import tastyquery.Contexts._
import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names._
import tastyquery.ast.Symbols.{DummySymbol, Symbol}
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{AppliedType, ConstantType, DummyType, TermRef, ThisType, Type, TypeRef}
import tastyquery.reader.TastyUnpickler.NameTable

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyReader}
import TastyBuffer._
import TastyFormat._
import TastyReader._

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

  def readName: TermName = nameAtRef(reader.readNameRef())

  def readTopLevelStat(using Context): Tree = reader.nextByte match {
    case PACKAGE =>
      reader.readByte()
      val packageEnd = reader.readEnd()
      assert(reader.readByte() == TERMREFpkg)
      // TODO: only create a symbol if it does not exist yet
      val pid = new Symbol(readName)
      PackageDef(pid, readStats(packageEnd))
    case _ => readStat
  }

  def readStats(end: Addr)(using Context): List[Tree] =
    reader.until(end)(readStat)

  def readStat(using Context): Tree = reader.nextByte match {
    case IMPORT =>
      def readSelector: ImportSelector = {
        assert(reader.nextByte == IMPORTED)
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
      val rhs = if (reader.nextByte == TEMPLATE) {
        ctx.createClassSymbolIfNew(start, name)
        readTemplate
      } else {
        ctx.createSymbolIfNew(start, name)
        readTerm
      }
      // TODO: read modifiers
      skipModifiers(end)
      TypeDef(name, rhs)
    case VALDEF | DEFDEF | PARAM => readValOrDefDef
    case _                       => readTerm
  }

  // TODO: classinfo of the owner
  def readTemplate(using Context): Template = {
    reader.readByte()
    val end     = reader.readEnd()
    val tparams = readTypeParams
    val params  = readParams
    val parents = reader.collectWhile(reader.nextByte != SELFDEF && reader.nextByte != DEFDEF) {
      reader.nextByte match {
        // class parents of classes are APPLYs, because they specify the constructor
        case APPLY => readTerm
        case _     => readTypeTree
      }
    }
    val self = readSelf
    // The first entry is the constructor
    val cstr = readStat.asInstanceOf[DefDef]
    val body = readStats(end)
    Template(cstr, parents, self, tparams ++ params ++ body)
  }

  def readTypeParams(using Context): List[TypeDef] = {
    def readTypeParam: TypeDef = {
      reader.readByte()
      // TODO: create symbols
      ???
    }
    var acc = new ListBuffer[TypeDef]()
    while (reader.nextByte == TYPEPARAM) {
      acc += readTypeParam
    }
    acc.toList
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
      val qualifier = readTerm.asInstanceOf[Ident]
      This(Some(qualifier))
    case SUPER =>
      reader.readByte()
      val end   = reader.readEnd()
      val qual  = readTerm
      val mixin = reader.ifBefore(end)(Some(readTerm.asInstanceOf[Ident]), None)
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
      val catchCases = readCases(end)
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
      val tpt    = reader.ifBefore(end)(readTypeTree, EmptyTree)
      Lambda(method, tpt)
    case MATCH =>
      reader.readByte()
      val end = reader.readEnd()
      if (reader.nextByte == IMPLICIT) {
        reader.readByte()
        new InlineMatch(EmptyTree, readCases(end))
      } else if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineMatch(readTerm, readCases(end))
      } else Match(readTerm, readCases(end))
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
        assert(reader.readByte() == IMPLICITarg)
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
      Return(expr, Ident(from.name))
    // type trees
    case IDENTtpt =>
      reader.readByte()
      val typeName = readName.toTypeName
      val typ      = readType
      // TODO: assign type
      Ident(typeName)
    case SINGLETONtpt =>
      reader.readByte()
      SingletonTypeTree(readTerm)
    case APPLIEDtpt =>
      reader.readByte()
      val end   = reader.readEnd()
      val tycon = readTypeTree
      AppliedTypeTree(tycon, reader.until(end)(readTypeTree))
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
      Ident(sym.name)
    // TODO: is it always Ident?
    case TERMREFsymbol =>
      reader.readByte()
      val sym = readSymRef
      val typ = readType
      // TODO: assign type
      Ident(sym.name)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm
    case _ => Literal(readConstant)
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

  def readCases(end: Addr)(using Context): List[CaseDef] =
    reader.collectWhile((nextUnsharedTag == CASEDEF) && reader.currentAddr != end) {
      if (reader.nextByte == SHAREDterm) {
        // skip the SHAREDterm tag
        reader.readByte()
        // TODO: changes in the context?
        forkAt(reader.readAddr()).readCaseDef
      }
      // TODO: changes in the context?
      else readCaseDef
    }

  def readCaseDef(using Context): CaseDef = {
    assert(reader.readByte() == CASEDEF)
    val end     = reader.readEnd()
    val pattern = readTerm
    val body    = readTerm
    CaseDef(pattern, reader.ifBefore(end)(readTerm, EmptyTree), body)
  }

  def readSymRef(using Context): Symbol = {
    val symAddr = reader.readAddr()
    if (!ctx.localSymbols.contains(symAddr)) {
      // will create the symbol
      forkAt(symAddr).readStat
      assert(ctx.localSymbols.contains(symAddr))
    }
    ctx.localSymbols(symAddr)
  }

  def readType(using Context): Type = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readType, name)
    case TYPEREFsymbol =>
      reader.readByte()
      val sym = readSymRef
      TypeRef(readType, sym)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readType
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
    case _ => ConstantType(readConstant)
  }

  def readTypeTree(using Context): Tree = reader.nextByte match {
    case tag if isTypeTreeTag(tag) => readTerm
    case SHAREDterm =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm
    case _ => TypeTree(readType)
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
}
