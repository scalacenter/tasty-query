package tastyquery.reader.classfiles

import tastyquery.Contexts.{ClassContext, clsCtx}
import tastyquery.ast.Types
import tastyquery.ast.Types.*
import tastyquery.ast.Symbols.*
import tastyquery.ast.Flags
import tastyquery.ast.Names.{SimpleName, TypeName, termName, nme}
import tastyquery.util.syntax.chaining.given

import scala.annotation.switch
import scala.collection.mutable

import ClassfileReader.ReadException

object JavaSignatures:

  private type JavaSignature = Null | Binders | Map[TypeName, RegularSymbol] | mutable.ListBuffer[TypeName]

  @throws[ReadException]
  def parseSignature(member: Symbol, signature: String)(using ClassContext): Type =
    var offset = 0
    var end = signature.length
    val isClass = member.isClass
    val isMethod = member.flags.is(Flags.Method)

    lazy val someEmptyType = Some(NoType)
    lazy val emptyTypeBounds = RealTypeBounds(NoType, NoType)

    extension (env: JavaSignature)

      def tparamRef(tname: TypeName): Some[Type] =
        def lookupTParam(scope: Symbol): Some[Type] =
          if scope.isPackage then cookFailure(tname, "no enclosing scope declares it")
          else if scope.isClass then
            ClassSymbolFactory.castSymbol(scope).typeParamSymsNoInitialize.find(_.name == tname) match
              case Some(ref) => Some(TypeRef(NoPrefix, ref))
              case _         => lookupTParam(scope.outer)
          else cookFailure(tname, "unexpected non-class scope")
        if env == null then lookupTParam(member.outer)
        else
          env match
            case map: Map[t, s] =>
              map.asInstanceOf[Map[TypeName, RegularSymbol]].get(tname) match
                case Some(sym) => Some(TypeRef(NoPrefix, sym))
                case None      => lookupTParam(member.outer)
            case pt: TypeBinders =>
              pt.lookupRef(tname) match
                case ref @ Some(_) => ref
                case _             => lookupTParam(member.outer)
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
      if available >= 1 && peek == char then true andThen { offset += 1 }
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

    def identifier: SimpleName =
      val old = offset
      while available > 0
        && (peek: @switch).match
          case '.' | ';' | '[' | '/' | '<' | '>' | ':' => false
          case _                                       => true
      do offset += 1
      if available == 0 then abort
      else termName(signature.slice(old, offset))

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

    def typeVariableSignature(env: JavaSignature): Option[Type] =
      if consume('T') then
        val tname = identifier.toTypeName
        expect(';')
        env.tparamRef(tname)
      else None

    def classTypeSignature(env: JavaSignature): Option[Type] =

      def findRawTopLevelClass: ClassSymbol =
        // lookup will not force anything new as all packages and top-level classes are known,
        // will fail fast if not on classpath.

        def packageSpecifiers(acc: PackageClassSymbol): ClassSymbol =
          val next = identifier
          if consume('/') then // must have '/', identifier, and terminal char.
            acc.getDecl(next) match
              case Some(pkg: PackageClassSymbol) =>
                packageSpecifiers(pkg)
              case res =>
                sys.error(s"found $res in operation $acc lookup $next")
                abort
          else
            acc.getDecl(next.toTypeName) match // TODO: encoded names?
              case Some(cls: ClassSymbol) =>
                cls
              case res =>
                sys.error(s"found $res in operation $acc lookup $next")
                abort
        end packageSpecifiers

        val firstIdent = identifier
        if consume('/') then // must have '/', identifier, and terminal char.
          val init = PackageRef(firstIdent)
          packageSpecifiers(init.resolveToSymbol)
        else
          val emptyPkg = PackageRef(nme.EmptyPackageName).resolveToSymbol
          emptyPkg.getDecl(firstIdent.toTypeName) match
            case Some(cls: ClassSymbol) => cls // TODO: encoded names?
            case _                      => abort
      end findRawTopLevelClass

      def simpleClassTypeSignature(cls: ClassSymbol): Type =
        val clsTpe = cls.accessibleThisType
        if consume('<') then // must have '<', '>', and class type
          AppliedType(clsTpe, typeArgumentsRest(env))
        else
          val rawArgs = Descriptors.rawTypeArguments(cls)
          if rawArgs.nonEmpty then AppliedType(clsTpe, rawArgs)
          else clsTpe
      end simpleClassTypeSignature

      if consume('L') then // must have 'L', identifier, and ';'.
        val rawTopLevelClass = findRawTopLevelClass
        val clsTpe = simpleClassTypeSignature(rawTopLevelClass)
        if consume(';') then Some(clsTpe)
        else None // TODO: read type arguments, inner classes
      else None
    end classTypeSignature

    def typeArgument(env: JavaSignature): Type =
      if available >= 1 then
        (peek: @switch) match
          case '*' =>
            commitSimple(1, WildcardTypeBounds(RealTypeBounds(NothingType, AnyType)))
          case '+' =>
            commit(1) { val upper = referenceType(env); WildcardTypeBounds(RealTypeBounds(NothingType, upper)) }
          case '-' =>
            commit(1) { val lower = referenceType(env); WildcardTypeBounds(RealTypeBounds(lower, AnyType)) }
          case _ =>
            referenceType(env)
      else abort

    def typeArgumentsRest(env: JavaSignature): List[Type] =
      readUntil('>', typeArgument(env))

    def typeParameter(env: JavaSignature): TypeBounds =
      val tname = identifier.toTypeName
      val classBound =
        expect(':')
        referenceTypeSignature(env) match
          case Some(tpe) => tpe
          case _         => AnyType
      val interfaceBounds = readWhile(':', referenceType(env))
      if env.withAddedParam(tname) then emptyTypeBounds // shortcut as we will throw away the bounds
      else RealTypeBounds(NothingType, interfaceBounds.foldLeft(classBound)(AndType(_, _)))

    def typeParamsRest(env: JavaSignature): List[TypeBounds] =
      readUntil('>', typeParameter(env))

    def lookaheadTypeParamNames: List[TypeName] =
      val tparamNameBuf = mutable.ListBuffer[TypeName]()
      val _ = lookahead(typeParamsRest(tparamNameBuf)) // lookahead to capture type param names
      tparamNameBuf.toList

    def arrayType(env: JavaSignature): Option[Type] =
      if consume('[') then
        val tpe = javaTypeSignature(env)
        Some(Types.ArrayTypeOf(tpe))
      else None

    def result(env: JavaSignature): Type =
      if consume('V') then Types.UnitType
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

    def methodSignature: Type =
      def methodRest(env: JavaSignature): Type =
        if consume('(') then // must have '(', ')', and return type
          val params = termParamsRest(env)
          val ret = result(env)
          if consume('^') then
            val _ = throwsSignatureRest(env) // ignored
          MethodType((0 until params.size).map(i => termName(s"x$$$i")).toList, params, ret)
        else abort
      if consume('<') then
        PolyType.rec(lookaheadTypeParamNames)(
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
        val tparams = tparamNames.map(tname => RegularSymbolFactory.createSymbol(tname, cls))
        val lookup = tparamNames.lazyZip(tparams).toMap
        cls.withTypeParams(tparams, typeParamsRest(lookup))
        classRest(lookup)
      else
        cls.withTypeParams(Nil, Nil)
        classRest(null)

    def fieldSignature: Type =
      ExprType(referenceType(null))

    def cookFailure(tname: TypeName, reason: String): Nothing =
      val path = if !isClass then s"${member.outer.erasedName}#${member.name}" else member.erasedName
      throw ReadException(
        s"could not resolve type parameter `$tname` in signature `$signature` of $path because $reason"
      )

    def unconsumed: Nothing =
      throw ReadException(
        s"Expected end of descriptor but found $"${signature.slice(offset, end)}$", [is method? $isMethod]"
      )

    def abort: Nothing =
      val msg =
        if available == 0 then "Unexpected end of descriptor"
        else s"Unexpected character '$peek' at $offset in descriptor (remaining: `${signature.slice(offset, end)}`)"
      throw ReadException(s"$msg of $member, original: `$signature` [is method? $isMethod]")

    (if isMethod then methodSignature
     else if isClass then classSignature(ClassSymbolFactory.castSymbol(member))
     else fieldSignature) andThen { if available > 0 then unconsumed }
  end parseSignature
end JavaSignatures
