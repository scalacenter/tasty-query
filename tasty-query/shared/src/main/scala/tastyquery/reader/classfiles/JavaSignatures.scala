package tastyquery.reader.classfiles

import scala.annotation.switch

import scala.collection.mutable

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Types.*
import tastyquery.Symbols.*

private[classfiles] object JavaSignatures:

  private type JavaSignature = Null | Binders | Map[TypeName, ClassTypeParamSymbol] | mutable.ListBuffer[TypeName]

  @throws[ClassfileFormatException]
  def parseSignature(member: Symbol { val owner: Symbol }, signature: String)(using Context): Type =
    var offset = 0
    var end = signature.length
    val isClass = member.isClass
    val isMethod = member.flags.is(Method)

    lazy val someEmptyType = Some(NoType)
    lazy val emptyTypeBounds = RealTypeBounds(NoType, NoType)

    extension (env: JavaSignature)

      def tparamRef(tname: TypeName): Some[Type] =
        def lookupTParam(scope: Symbol): Some[Type] =
          if scope.isPackage then cookFailure(tname, "no enclosing scope declares it")
          else if scope.isClass then
            scope.asClass.typeParamSymsNoInitialize.find(_.name == tname) match
              case Some(ref) => Some(TypeRef(NoPrefix, ref))
              case _         => lookupTParam(scope.asClass.owner)
          else cookFailure(tname, "unexpected non-class scope")
        if env == null then lookupTParam(member.owner)
        else
          env match
            case map: Map[t, s] =>
              map.asInstanceOf[Map[TypeName, ClassTypeParamSymbol]].get(tname) match
                case Some(sym) => Some(TypeRef(NoPrefix, sym))
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

    def typeVariableSignature(env: JavaSignature): Option[Type] =
      if consume('T') then
        val tname = identifier.toTypeName
        expect(';')
        env.tparamRef(tname)
      else None

    def classTypeSignature(env: JavaSignature): Option[Type] =
      def readSimpleClassType: TypeRef =
        def followPackages(acc: PackageSymbol): TypeRef =
          val next = identifier
          if consume('/') then // must have '/', identifier, and terminal char.
            acc.getPackageDecl(next) match
              case Some(pkg) =>
                followPackages(pkg)
              case res =>
                sys.error(s"cannot find package $next in $acc")
          else TypeRef(PackageRef(acc), next.toTypeName)
        end followPackages

        val firstIdent = identifier
        if consume('/') then // must have '/', identifier, and terminal char.
          val firstPackage = defn.RootPackage.getPackageDecl(firstIdent).getOrElse {
            sys.error(s"cannot find package $firstIdent in ${defn.RootPackage}")
          }
          followPackages(firstPackage)
        else TypeRef(PackageRef(FullyQualifiedName.emptyPackageName), firstIdent.toTypeName)
      end readSimpleClassType

      def simpleClassTypeSignature(clsTpe: TypeRef): Type =
        if consume('<') then // must have '<', '>', and class type
          AppliedType(clsTpe, typeArgumentsRest(env))
        else clsTpe
      end simpleClassTypeSignature

      if consume('L') then // must have 'L', identifier, and ';'.
        val clsTpe = simpleClassTypeSignature(readSimpleClassType)
        if consume(';') then Some(clsTpe)
        else None // TODO: read type arguments, inner classes
      else None
    end classTypeSignature

    def typeArgument(env: JavaSignature): Type =
      if available >= 1 then
        (peek: @switch) match
          case '*' =>
            commitSimple(1, WildcardTypeBounds(defn.NothingAnyBounds))
          case '+' =>
            commit(1) { val upper = referenceType(env); WildcardTypeBounds(RealTypeBounds(defn.NothingType, upper)) }
          case '-' =>
            commit(1) { val lower = referenceType(env); WildcardTypeBounds(RealTypeBounds(lower, defn.AnyType)) }
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
          case _         => defn.AnyType
      val interfaceBounds = readWhile(':', referenceType(env))
      if env.withAddedParam(tname) then emptyTypeBounds // shortcut as we will throw away the bounds
      else RealTypeBounds(defn.NothingType, interfaceBounds.foldLeft(classBound)(AndType(_, _)))

    def typeParamsRest(env: JavaSignature): List[TypeBounds] =
      readUntil('>', typeParameter(env))

    def lookaheadTypeParamNames: List[TypeName] =
      val tparamNameBuf = mutable.ListBuffer[TypeName]()
      val _ = lookahead(typeParamsRest(tparamNameBuf)) // lookahead to capture type param names
      tparamNameBuf.toList

    def arrayType(env: JavaSignature): Option[Type] =
      if consume('[') then
        val tpe = javaTypeSignature(env)
        Some(defn.ArrayTypeOf(tpe))
      else None

    def result(env: JavaSignature): Type =
      if consume('V') then defn.UnitType
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
        val tparams = tparamNames.map(tname => ClassTypeParamSymbol.create(tname, cls))
        val lookup = tparamNames.lazyZip(tparams).toMap
        cls.withTypeParams(tparams, typeParamsRest(lookup))
        classRest(lookup)
      else
        cls.withTypeParams(Nil, Nil)
        classRest(null)

    def fieldSignature: Type =
      ExprType(referenceType(null))

    def cookFailure(tname: TypeName, reason: String): Nothing =
      val path = if !isClass then s"${member.owner.erasedName}#${member.name}" else member.erasedName
      throw ClassfileFormatException(
        s"could not resolve type parameter `$tname` in signature `$signature` of $path because $reason"
      )

    def unconsumed: Nothing =
      throw ClassfileFormatException(
        s"Expected end of descriptor but found $"${signature.slice(offset, end)}$", [is method? $isMethod]"
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
