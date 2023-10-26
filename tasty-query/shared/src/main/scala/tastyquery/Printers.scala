package tastyquery

import java.io.{StringWriter, Writer}

import dotty.tools.tasty.TastyFormat.NameTags

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
        print(tpe.args.head)
        for arg <- tpe.args.tail do
          print(", ")
          print(arg)
        print("]")
      case tpe: ByNameType =>
        print("=> ")
        print(tpe.resultType)
      case tpe: TypeLambda =>
        print("([")
        print(tpe.typeLambdaParams.head)
        for tparam <- tpe.typeLambdaParams.tail do
          print(", ")
          print(tparam)
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
        if !isSyntacticAny(tpe.bound) then
          print(" <: ")
          print(tpe.bound)
        print(" match { ")
        var first = true
        for caze <- tpe.cases do
          if first then first = false
          else print("; ")
          print("case ")
          print(caze.pattern)
          print(" => ")
          print(caze.result)
        print(" })")
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
        var first = true
        for (argName, argType) <- tpe.paramNames.lazyZip(tpe.paramTypes) do
          if first then first = false
          else print(", ")
          print(argName)
          print(": ")
          print(argType)
        print(")")
        print(tpe.resultType)
      case tpe: PolyType =>
        print("[")
        var first = true
        for (argName, argBounds) <- tpe.paramNames.lazyZip(tpe.paramTypeBounds) do
          if first then first = false
          else print(", ")
          print(argName)
          print(argBounds)
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
      print("@<annot>") // TODO Improve this

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
