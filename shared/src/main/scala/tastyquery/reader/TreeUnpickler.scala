package tastyquery.reader

import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names._
import tastyquery.ast.Symbols.{DummySymbol, Symbol}
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{DummyType, TermRef, Type, TypeRef}
import tastyquery.reader.TastyUnpickler.NameTable

import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyReader}, TastyBuffer._, TastyFormat._

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

class TreeUnpickler(reader: TastyReader, nameAtRef: NameTable) {
  def unpickle: List[Tree] = {
    @tailrec def read(acc: ListBuffer[Tree]): List[Tree] = {
      acc += readTopLevelStat
      if (!reader.isAtEnd) read(acc) else acc.toList
    }
    read(new ListBuffer[Tree])
  }

  def forkAt(start: Addr): TreeUnpickler =
    new TreeUnpickler(reader.subReader(start, reader.endAddr), nameAtRef)

  def readName: TermName = nameAtRef(reader.readNameRef())

  def readTopLevelStat: Tree = reader.nextByte match {
    case PACKAGE =>
      reader.readByte()
      val packageEnd = reader.readEnd()
      assert(reader.readByte() == TERMREFpkg)
      // TODO: only create a symbol if it does not exist yet
      val pid = new Symbol(readName)
      PackageDef(pid, readStats(packageEnd))
    case _ => readStat
  }

  def readStats(end: Addr): List[Tree] =
    reader.until(end)(readStat)

  def readStat: Tree = reader.nextByte match {
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
      reader.readByte()
      val end  = reader.readEnd()
      val name = readName
      // TODO: this is only for classes, read type for other typedefs
      val template = readTemplate
      // TODO: read modifiers
      skipModifiers(end)
      TypeDef(name.toTypeName, template)
    case VALDEF | DEFDEF => readValOrDefDef
    case _               => readTerm
  }

  // TODO: classinfo of the owner
  def readTemplate: Template = {
    reader.readByte()
    val end     = reader.readEnd()
    val tparams = readTypeParams
    val params  = readParams
    val parents = reader.collectWhile(reader.nextByte != SELFDEF && reader.nextByte != DEFDEF)(readTerm)
    val self    = readSelf
    // The first entry is the constructor
    val cstr = readStat.asInstanceOf[DefDef]
    val body = readStats(end)
    Template(cstr, parents, self, tparams ++ params ++ body)
  }

  def readTypeParams: List[TypeDef] = {
    def readTypeParam: TypeDef = {
      reader.readByte()
      ???
    }
    var acc = new ListBuffer[TypeDef]()
    while (reader.nextByte == TYPEPARAM) {
      acc += readTypeParam
    }
    acc.toList
  }

  def readParamLists: List[List[ValDef]] = {
    var acc = new ListBuffer[List[ValDef]]()
    while (reader.nextByte == PARAM) {
      acc += readParams
    }
    if (reader.nextByte == PARAMEND) {
      reader.readByte()
    }
    acc.toList
  }

  def readParams: List[ValDef] = {
    var acc = new ListBuffer[ValDef]()
    while (reader.nextByte == PARAM) {
      acc += readValOrDefDef.asInstanceOf[ValDef]
    }
    if (reader.nextByte == PARAMEND) {
      reader.readByte()
    }
    acc.toList
  }

  def readSelf: ValDef =
    if (reader.nextByte != SELFDEF) {
      EmptyValDef
    } else {
      reader.readByte()
      ???
    }

  def readValOrDefDef: Tree = {
    val tag  = reader.readByte()
    val end  = reader.readEnd()
    val name = readName
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

  def readTerms(end: Addr): List[Tree] =
    reader.until(end)(readTerm)

  def readTerm: Tree = reader.nextByte match {
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
    case SELECT =>
      reader.readByte()
      val name = readName
      val qual = readTerm
      Select(qual, name)
    case NEW =>
      reader.readByte()
      val cls = readTypeTree
      New(cls)
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
    case MATCH =>
      reader.readByte()
      val end = reader.readEnd()
      if (reader.nextByte == IMPLICIT) {
        reader.readByte()
        new InlineMatch(EmptyTree, reader.until(end)(readCaseDef))
      } else if (reader.nextByte == INLINE) {
        reader.readByte()
        new InlineMatch(readTerm, reader.until(end)(readCaseDef))
      } else Match(readTerm, reader.until(end)(readCaseDef))
    case ALTERNATIVE =>
      reader.readByte()
      val end = reader.readEnd()
      Alternative(reader.until(end)(readTerm))
    case WHILE =>
      reader.readByte()
      reader.readEnd()
      While(readTerm, readTerm)
    // type trees
    case IDENTtpt =>
      reader.readByte()
      val typeName = readName.toTypeName
      val typ      = readType
      // TODO: assign type
      Ident(typeName)
    // paths
    case TERMREFpkg =>
      DummyTree(readType, "TermRef into tree")
    case TERMREFdirect =>
      val sym = readSymRef()
      // TODO: assign type
      Ident(sym.name)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm
    case _ => Literal(readConstant())
  }

  def readCaseDef: CaseDef = {
    assert(reader.readByte() == CASEDEF)
    val end     = reader.readEnd()
    val pattern = readTerm
    val body    = readTerm
    CaseDef(pattern, reader.ifBefore(end)(readTerm, EmptyTree), body)
  }

  def readSymRef(): Symbol = {
    // TODO: return the symbol of the term at this address
    reader.readAddr()
    DummySymbol
  }

  def readType: Type = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readType, name)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readType
    case TERMREFpkg =>
      reader.readByte()
      val name = readName
      TermRef(DummyType, name)
  }

  def readTypeTree: Tree = reader.nextByte match {
    case tag if isTypeTreeTag(tag) => readTerm
    case SHAREDterm =>
      reader.readByte()
      forkAt(reader.readAddr()).readTerm
    case _ => TypeTree(readType)
  }

  def readConstant(): Constant = reader.readByte() match {
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
  def skipModifiers(end: Addr): Unit = {
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
