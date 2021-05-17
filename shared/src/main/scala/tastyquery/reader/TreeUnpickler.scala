package tastyquery.reader

import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer

import tastyquery.ast.Names._
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{DummyType, TermRef, Type, TypeRef}
import tastyquery.ast.Symbols.Symbol
import tastyquery.reader.TastyUnpickler.NameTable

import dotty.tools.tasty.{TastyBuffer, TastyFormat, TastyReader}, TastyBuffer._, TastyFormat._

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

  def readParams: List[ValDef] = {
    var acc = new ListBuffer[ValDef]()
    while (reader.nextByte == PARAM) {
      acc += readValOrDefDef.asInstanceOf[ValDef]
    }
    if (reader.nextByte == SPLITCLAUSE) {
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
  }

  def readType: Type = reader.nextByte match {
    case TYPEREF =>
      reader.readByte()
      val name = readName.toTypeName
      TypeRef(readType, name)
    case TERMREFpkg =>
      reader.readByte()
      val name = readName
      TermRef(DummyType, name)
    case SHAREDtype =>
      reader.readByte()
      forkAt(reader.readAddr()).readType
  }

  def readTypeTree: Tree = reader.nextByte match {
    case tag if isTypeTreeTag(tag) => readTerm
    case _                         => TypeTree(readType)
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
