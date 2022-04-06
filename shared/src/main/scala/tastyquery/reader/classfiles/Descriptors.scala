package tastyquery.reader.classfiles

import tastyquery.Contexts.{BaseContext, baseCtx}
import tastyquery.ast.Types
import tastyquery.ast.Types.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Flags
import tastyquery.reader.classfiles.ClassfileReader.ReadException
import tastyquery.ast.Names.termName
import tastyquery.util.syntax.chaining.given

import scala.annotation.switch

object Descriptors:

  @throws[ReadException]
  def parseDescriptor(member: Symbol, desc: String)(using BaseContext): Type =
    // TODO: once we support inner classes, decide if we merge with parseSignature
    var offset = 0
    var end = desc.length
    val isMethod = member.flags.is(Flags.Method)

    def available = end - offset

    def peek = desc.charAt(offset)

    def consume(char: Char): Boolean =
      if available >= 1 && peek == char then true andThen { offset += 1 }
      else false

    def charsUntil(char: Char): String =
      val old = offset
      while available > 0 && peek != char do offset += 1
      if available == 0 then abort
      else desc.slice(old, offset) andThen { offset += 1 } // skip char

    def commitSimple[T](len: Int, t: T): T =
      offset += len
      t

    def baseType: Option[Type] =
      if available >= 1 then
        (peek: @switch) match
          case 'B' => commitSimple(1, Some(Types.ByteType))
          case 'C' => commitSimple(1, Some(Types.CharType))
          case 'D' => commitSimple(1, Some(Types.DoubleType))
          case 'F' => commitSimple(1, Some(Types.FloatType))
          case 'I' => commitSimple(1, Some(Types.IntType))
          case 'J' => commitSimple(1, Some(Types.LongType))
          case 'S' => commitSimple(1, Some(Types.ShortType))
          case 'Z' => commitSimple(1, Some(Types.BooleanType))
          case _   => None
      else None

    def objectType: Option[Type] =
      if consume('L') then // has 'L', ';', and class name
        val chars = charsUntil(';') // consume until ';', skip ';'
        val cls = chars.replace('/', '.').nn
        baseCtx.getClassIfDefined(cls) match
          case Right(ref) => Some(ref.accessibleThisType) // TODO: turn into applied type if raw type
          case Left(err)  =>
            // TODO: inner classes
            throw err
      else None

    def arrayType: Option[Type] =
      if consume('[') then
        val tpe = fieldDescriptor
        Some(Types.ArrayTypeOf(tpe))
      else None

    def fieldDescriptor: Type =
      baseType.orElse(objectType).orElse(arrayType).getOrElse(abort)

    def returnDescriptor: Type =
      if consume('V') then Types.UnitType
      else fieldDescriptor

    def methodDescriptor: Type =
      if consume('(') then // must have '(', ')', and return type
        def paramDescriptors(acc: List[Type]): List[Type] =
          if consume(')') then acc.reverse
          else paramDescriptors(fieldDescriptor :: acc)
        val params = paramDescriptors(Nil)
        val ret = returnDescriptor
        MethodType((0 until params.size).map(i => termName(s"x$$$i")).toList, params, ret)
      else abort

    def unconsumed: Nothing =
      throw ReadException(
        s"Expected end of descriptor but found $"${desc.slice(offset, end)}$", [is method? $isMethod]"
      )

    def abort: Nothing =
      val msg =
        if available == 0 then "Unexpected end of descriptor"
        else s"Unexpected characted '$peek' in descriptor"
      throw ReadException(s"$msg of $member, original: `$desc` [is method? $isMethod]")

    (if isMethod then methodDescriptor else ExprType(fieldDescriptor)) andThen { if available > 0 then unconsumed }

  end parseDescriptor
end Descriptors
