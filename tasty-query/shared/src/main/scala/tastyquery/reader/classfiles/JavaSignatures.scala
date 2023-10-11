package tastyquery.reader.classfiles

import scala.annotation.switch

import scala.collection.mutable
import scala.collection.mutable.Growable

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Types.*
import tastyquery.Symbols.*

import tastyquery.reader.ReaderContext
import tastyquery.reader.ReaderContext.rctx

import ClassfileParser.{InnerClasses, Resolver}

private[classfiles] object JavaSignatures:

  private type JavaSignature = Null | Binders | Map[TypeName, ClassTypeParamSymbol] | mutable.ListBuffer[TypeName]

  @throws[ClassfileFormatException]
  def parseSignature(member: Symbol { val owner: Symbol }, signature: String, allRegisteredSymbols: Growable[Symbol])(
    using ReaderContext,
    InnerClasses,
    Resolver
  ): TypeOrMethodic =
    var offset = 0
    var end = signature.length
    val isClass = member.isClass
    val isMethod = member.isTerm && member.asTerm.isMethod

    lazy val someEmptyType = Some(rctx.AnyType)
    lazy val emptyTypeBounds = rctx.NothingAnyBounds

    extension (env: JavaSignature)

      def tparamRef(tname: TypeName): Some[Type] =
        def lookupTParam(scope: Symbol): Some[Type] =
          if scope.isPackage then cookFailure(tname, "no enclosing scope declares it")
          else if scope.isClass then
            scope.asClass.typeParams.find(_.name == tname) match
              case Some(ref) => Some(TypeRef(ref.owner.thisType, ref))
              case _         => lookupTParam(scope.asClass.owner)
          else cookFailure(tname, "unexpected non-class scope")
        if env == null then lookupTParam(member.owner)
        else
          env match
            case map: Map[t, s] =>
              map.asInstanceOf[Map[TypeName, ClassTypeParamSymbol]].get(tname) match
                case Some(sym) => Some(TypeRef(sym.owner.thisType, sym))
                case None      => lookupTParam(member.owner)
            case pt: TypeBinders =>
              pt.lookupRef(tname) match
                case ref @ Some(_) => ref
                case _             => lookupTParam(member.owner)
            case _ => someEmptyType // we are capturing type parameter names, we will throw away the result here.

      def withAddedParam(tname: TypeName): Boolean = env match
        case env: mutable.ListBuffer[t] =>
          env.asInstanceOf[mutable.ListBuffer[TypeName]].addOne(tname)
          true
        case _ => false

    end extension

    def lookahead[T](op: => T): T =
      val oldOffset = offset
      val oldEnd = end
      val res = op
      offset = oldOffset
      end = oldEnd
      res

    def available = end - offset

    def peek = signature.charAt(offset)

    def consume(char: Char): Boolean =
      if available >= 1 && peek == char then
        offset += 1
        true
      else false

    def expect(char: Char): Unit =
      if available >= 1 && peek == char then offset += 1
      else abort

    def commitSimple[T](len: Int, t: T): T =
      offset += len
      t

    def commit[T](len: Int)(t: => T): T =
      offset += len
      t

    inline def accumulate[T](inline accWhile: Boolean, inline cond: Boolean)(inline op: T): List[T] =
      def rec(acc: mutable.ListBuffer[T]): List[T] =
        inline if accWhile then
          if cond then rec(acc.addOne(op))
          else acc.toList
        else if cond then acc.toList
        else rec(acc.addOne(op))
      rec(mutable.ListBuffer())

    inline def readUntil[T](char: Char, inline op: T): List[T] =
      accumulate(accWhile = false, consume(char))(op)

    inline def readWhile[T](char: Char, inline op: T): List[T] =
      accumulate(accWhile = true, consume(char))(op)

    inline def charsWhile(inline f: Char => Boolean): SimpleName =
      val old = offset
      while available > 0 && f(peek) do offset += 1
      if available == 0 then abort
      else termName(signature.slice(old, offset))

    def identifier(): SimpleName =
      charsWhile({
        case '.' | ';' | '[' | '/' | '<' | '>' | ':' => false
        case _                                       => true
      })

    /** same as [[identifier]], except includes '/' */
    def binaryName(): SimpleName =
      charsWhile({
        case '.' | ';' | '[' | '<' | '>' | ':' => false
        case _                                 => true
      })

    def baseType: Option[Type] =
      if available >= 1 then
        (peek: @switch) match
          case 'B' => commitSimple(1, Some(rctx.ByteType))
          case 'C' => commitSimple(1, Some(rctx.CharType))
          case 'D' => commitSimple(1, Some(rctx.DoubleType))
          case 'F' => commitSimple(1, Some(rctx.FloatType))
          case 'I' => commitSimple(1, Some(rctx.IntType))
          case 'J' => commitSimple(1, Some(rctx.LongType))
          case 'S' => commitSimple(1, Some(rctx.ShortType))
          case 'Z' => commitSimple(1, Some(rctx.BooleanType))
          case _   => None
      else None

    def typeVariableSignature(env: JavaSignature): Option[Type] =
      if consume('T') then
        val tname = identifier().toTypeName
        expect(';')
        env.tparamRef(tname)
      else None

    def classTypeSignature(env: JavaSignature): Option[Type] =

      def simpleClassTypeSignature(clsTpe: TypeRef): Type =
        if consume('<') then // must have '<', '>', and class type
          AppliedType(clsTpe, typeArgumentsRest(env))
        else clsTpe

      def classTypeSignatureRest(pre: Type): Type =
        if consume('.') then // must have '.', identifier, and class type
          val rawClass = TypeRef(pre, identifier().toTypeName)
          val clsTpe = simpleClassTypeSignature(rawClass)
          classTypeSignatureRest(clsTpe)
        else
          expect(';')
          pre
      end classTypeSignatureRest

      if consume('L') then // must have 'L', identifier, and ';'.
        val pre = simpleClassTypeSignature(Descriptors.classRef(binaryName()))
        Some(classTypeSignatureRest(pre))
      else None
    end classTypeSignature

    def typeArgument(env: JavaSignature): TypeOrWildcard =
      if available >= 1 then
        (peek: @switch) match
          case '*' =>
            commitSimple(1, WildcardTypeArg(rctx.NothingAnyBounds))
          case '+' =>
            commit(1) {
              val upper = referenceType(env)
              WildcardTypeArg(RealTypeBounds(rctx.NothingType, upper))
            }
          case '-' =>
            commit(1) {
              val lower = referenceType(env)
              WildcardTypeArg(RealTypeBounds(lower, rctx.FromJavaObjectType))
            }
          case _ =>
            referenceType(env)
      else abort

    def typeArgumentsRest(env: JavaSignature): List[TypeOrWildcard] =
      readUntil('>', typeArgument(env))

    def typeParameter(env: JavaSignature): TypeBounds =
      val tname = identifier().toTypeName
      val classBound =
        expect(':')
        referenceTypeSignature(env).toList
      val interfaceBounds = readWhile(':', referenceType(env))
      if env.withAddedParam(tname) then emptyTypeBounds // shortcut as we will throw away the bounds
      else
        val allBounds = classBound ::: interfaceBounds
        val bound = if allBounds.isEmpty then rctx.AnyType else allBounds.reduceLeft(AndType(_, _))
        RealTypeBounds(rctx.NothingType, bound)

    def typeParamsRest(env: JavaSignature): List[TypeBounds] =
      readUntil('>', typeParameter(env))

    def lookaheadTypeParamNames: List[TypeName] =
      val tparamNameBuf = mutable.ListBuffer[TypeName]()
      val _ = lookahead(typeParamsRest(tparamNameBuf)) // lookahead to capture type param names
      tparamNameBuf.toList

    def arrayType(env: JavaSignature): Option[Type] =
      if consume('[') then
        val tpe = javaTypeSignature(env)
        Some(rctx.ArrayTypeOf(tpe))
      else None

    def result(env: JavaSignature): Type =
      if consume('V') then rctx.UnitType
      else javaTypeSignature(env)

    def referenceType(env: JavaSignature): Type =
      referenceTypeSignature(env).getOrElse(abort)

    def referenceTypeSignature(env: JavaSignature): Option[Type] =
      classTypeSignature(env).orElse(typeVariableSignature(env)).orElse(arrayType(env))

    def throwsSignatureRest(env: JavaSignature): Type =
      classTypeSignature(env).orElse(typeVariableSignature(env)).getOrElse(abort)

    def classType(env: JavaSignature): Type =
      classTypeSignature(env).getOrElse(abort)

    def javaTypeSignature(env: JavaSignature): Type =
      referenceTypeSignature(env).orElse(baseType).getOrElse(abort)

    def termParamsRest(env: JavaSignature): List[Type] =
      readUntil(')', javaTypeSignature(env))

    def methodSignature: MethodicType =
      def methodRest(env: JavaSignature): MethodType =
        if consume('(') then // must have '(', ')', and return type
          val params = termParamsRest(env)
          val ret = result(env)
          val _ = readWhile('^', throwsSignatureRest(env)) // ignore throws clauses
          MethodType((0 until params.size).map(i => termName(s"x$$$i")).toList, params, ret)
        else abort
      if consume('<') then
        PolyType(lookaheadTypeParamNames)(
          pt => typeParamsRest(pt), // now we know the type parameters, resolve them
          pt => methodRest(pt)
        )
      else methodRest(null)

    def classSignature(cls: ClassSymbol): Type =
      def classRest(env: JavaSignature): Type =
        def interfaces(env: JavaSignature, acc: mutable.ListBuffer[Type]): Type =
          if available >= 1 && peek == 'L' then interfaces(env, acc.addOne(classType(env)))
          else acc.toList.reduce(AndType(_, _))
        val superTpe = classType(env)
        interfaces(env, mutable.ListBuffer(superTpe))
      if consume('<') then
        val tparamNames = lookaheadTypeParamNames
        val tparams = tparamNames.map { tname =>
          val paramSym = ClassTypeParamSymbol.create(tname, cls)
          allRegisteredSymbols += paramSym
          paramSym.withFlags(ClassTypeParam | JavaDefined, None).setAnnotations(Nil)
          paramSym
        }
        val lookup = tparamNames.lazyZip(tparams).toMap
        val tparamBounds = typeParamsRest(lookup)
        tparams.lazyZip(tparamBounds).foreach((tparam, bounds) => tparam.setDeclaredBounds(bounds))
        cls.withTypeParams(tparams)
        classRest(lookup)
      else
        cls.withTypeParams(Nil)
        classRest(null)

    def fieldSignature: Type =
      referenceType(null)

    def cookFailure(tname: TypeName, reason: String): Nothing =
      val path = if !isClass then s"${member.owner.fullName}#${member.name}" else member.fullName
      throw ClassfileFormatException(
        s"could not resolve type parameter `$tname` in signature `$signature` of $path because $reason"
      )

    def unconsumed: Nothing =
      throw ClassfileFormatException(
        s"Expected end of descriptor but found $"${signature.slice(offset, end)}$", original: `$signature` [is method? $isMethod]"
      )

    def abort: Nothing =
      val msg =
        if available == 0 then "Unexpected end of descriptor"
        else s"Unexpected character '$peek' at $offset in descriptor (remaining: `${signature.slice(offset, end)}`)"
      throw ClassfileFormatException(s"$msg of $member, original: `$signature` [is method? $isMethod]")

    val parsedSignature =
      if isMethod then methodSignature
      else if isClass then classSignature(member.asClass)
      else fieldSignature

    if available > 0 then unconsumed

    parsedSignature
  end parseSignature
end JavaSignatures
