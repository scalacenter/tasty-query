package tastyquery.reader.classfiles

import scala.annotation.switch

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Types.*
import tastyquery.Symbols.*
import tastyquery.Flags

import ClassfileParser.*

private[classfiles] object Descriptors:

  def parseSupers(cls: ClassSymbol, superClass: Option[SimpleName], interfaces: IArray[SimpleName])(
    using Context,
    InnerClasses,
    Resolver
  ): List[Type] =
    cls.withTypeParams(Nil)
    // !!! Cannot access `defn.ObjectClass` here, because that's a cycle when initializing defn.ObjectClass itself
    if cls.owner == defn.javaLangPackage && cls.name == tpnme.Object then defn.AnyType :: defn.MatchableType :: Nil
    else
      val superRef = superClass.map(classRef).getOrElse(defn.ObjectType)
      superRef :: interfaces.map(classRef).toList

  def classRef(binaryName: SimpleName)(using Context, InnerClasses, Resolver): TypeRef =
    resolver.resolve(binaryName)

  @throws[ClassfileFormatException]
  def parseDescriptor(member: Symbol, desc: String)(using Context, InnerClasses, Resolver): Type =
    // TODO: once we support inner classes, decide if we merge with parseSignature
    var offset = 0
    var end = desc.length
    val isMethod = member.flags.is(Flags.Method)

    def available = end - offset

    def peek = desc.charAt(offset)

    def consume(char: Char): Boolean =
      if available >= 1 && peek == char then
        offset += 1
        true
      else false

    def charsUntil(char: Char): String =
      val old = offset
      while available > 0 && peek != char do offset += 1
      if available == 0 then abort
      else
        val result = desc.slice(old, offset)
        offset += 1 // skip char
        result

    def commitSimple[T](len: Int, t: T): T =
      offset += len
      t

    def baseType: Option[Type] =
      if available >= 1 then
        (peek: @switch) match
          case 'B' => commitSimple(1, Some(defn.ByteType))
          case 'C' => commitSimple(1, Some(defn.CharType))
          case 'D' => commitSimple(1, Some(defn.DoubleType))
          case 'F' => commitSimple(1, Some(defn.FloatType))
          case 'I' => commitSimple(1, Some(defn.IntType))
          case 'J' => commitSimple(1, Some(defn.LongType))
          case 'S' => commitSimple(1, Some(defn.ShortType))
          case 'Z' => commitSimple(1, Some(defn.BooleanType))
          case _   => None
      else None

    def objectType: Option[Type] =
      if consume('L') then // has 'L', ';', and class name
        val binaryName = termName(charsUntil(';')) // consume until ';', skip ';'
        Some(classRef(binaryName))
      else None

    def arrayType: Option[Type] =
      if consume('[') then
        val tpe = fieldDescriptor
        Some(defn.ArrayTypeOf(tpe))
      else None

    def fieldDescriptor: Type =
      baseType.orElse(objectType).orElse(arrayType).getOrElse(abort)

    def returnDescriptor: Type =
      if consume('V') then defn.UnitType
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
      throw ClassfileFormatException(
        s"Expected end of descriptor but found $"${desc.slice(offset, end)}$", [is method? $isMethod]"
      )

    def abort: Nothing =
      val msg =
        if available == 0 then "Unexpected end of descriptor"
        else s"Unexpected characted '$peek' in descriptor"
      throw ClassfileFormatException(s"$msg of $member, original: `$desc` [is method? $isMethod]")

    val parsedDescriptor =
      if isMethod then methodDescriptor
      else ExprType(fieldDescriptor)

    if available > 0 then unconsumed

    parsedDescriptor
  end parseDescriptor
end Descriptors
