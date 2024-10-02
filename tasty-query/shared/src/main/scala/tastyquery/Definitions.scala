package tastyquery

import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

final class Definitions private[tastyquery] (
  ctxRestricted: Context,
  rootPackage: PackageSymbol,
  emptyPackage: PackageSymbol
):
  /** Use the restricted context for an op.
    *
    * !!! ONLY use from the initialization code of `lazy val`s.
    *
    * Well ... `def FunctionNClass` also uses it, for compatibility reasons, but it's fine.
    */
  private inline def withRestrictedContext[A](op: Context ?=> A): A =
    op(using ctxRestricted)

  // Core packages

  val RootPackage = rootPackage
  val EmptyPackage = emptyPackage

  val specialOpsPackage = RootPackage.getPackageDeclOrCreate(nme.specialOpsPackageName)

  val scalaPackage = RootPackage.getPackageDeclOrCreate(nme.scalaPackageName)
  private val javaPackage = RootPackage.getPackageDeclOrCreate(nme.javaPackageName)
  val javaLangPackage = javaPackage.getPackageDeclOrCreate(nme.langPackageName)
  private[tastyquery] val javaLangInvokePackage = javaLangPackage.getPackageDeclOrCreate(termName("invoke"))

  private val scalaAnnotationPackage =
    scalaPackage.getPackageDeclOrCreate(termName("annotation"))
  private[tastyquery] val scalaAnnotationInternalPackage =
    scalaAnnotationPackage.getPackageDeclOrCreate(termName("internal"))
  private val scalaCollectionPackage =
    scalaPackage.getPackageDeclOrCreate(termName("collection"))
  private[tastyquery] val scalaCompiletimePackage =
    scalaPackage.getPackageDeclOrCreate(termName("compiletime"))
  private val scalaCollectionImmutablePackage =
    scalaCollectionPackage.getPackageDeclOrCreate(termName("immutable"))
  private val scalaQuotedPackage =
    scalaPackage.getPackageDeclOrCreate(termName("quoted"))
  private val scalaRuntimePackage =
    scalaPackage.getPackageDeclOrCreate(termName("runtime"))

  // Special types

  val AnyKindType: AnyKindType = new AnyKindType()
  val NothingType: NothingType = new NothingType()

  // Cached TypeRef's for core types

  val SyntacticAnyKindType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("AnyKind"))
  val SyntacticNothingType: TypeRef = TypeRef(scalaPackage.packageRef, tpnme.Nothing)

  val AnyType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Any"))
  val MatchableType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Matchable"))
  val AnyRefType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("AnyRef"))
  val AnyValType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("AnyVal"))

  val NullType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Null"))

  val ObjectType: TypeRef = TypeRef(javaLangPackage.packageRef, typeName("Object"))

  val ArrayTypeUnapplied: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Array"))
  def ArrayTypeOf(tpe: TypeOrWildcard): AppliedType = AppliedType(ArrayTypeUnapplied, List(tpe))

  val SeqTypeUnapplied: TypeRef = TypeRef(scalaCollectionImmutablePackage.packageRef, typeName("Seq"))
  def SeqTypeOf(tpe: TypeOrWildcard): AppliedType = AppliedType(SeqTypeUnapplied, List(tpe))

  val IntType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Int"))
  val LongType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Long"))
  val FloatType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Float"))
  val DoubleType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Double"))
  val BooleanType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Boolean"))
  val ByteType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Byte"))
  val ShortType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Short"))
  val CharType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Char"))
  val UnitType: TypeRef = TypeRef(scalaPackage.packageRef, typeName("Unit"))

  val StringType: TypeRef = TypeRef(javaLangPackage.packageRef, typeName("String"))

  val UnappliedClassType: TypeRef = TypeRef(javaLangPackage.packageRef, typeName("Class"))
  def ClassTypeOf(tpe: TypeOrWildcard): AppliedType = AppliedType(UnappliedClassType, List(tpe))

  val ThrowableType: TypeRef = TypeRef(javaLangPackage.packageRef, typeName("Throwable"))

  val TupleType: TypeRef = TypeRef(scalaPackage.packageRef, tpnme.Tuple)

  val EmptyTupleType: TermRef =
    TermRef(TermRef(scalaPackage.packageRef, termName("Tuple$package")), nme.EmptyTuple)

  val NonEmptyTupleType: TypeRef = TypeRef(scalaPackage.packageRef, tpnme.NonEmptyTuple)

  val TupleConsTypeUnapplied: TypeRef = TypeRef(scalaPackage.packageRef, tpnme.TupleCons)
  def TupleConsTypeOf(head: TypeOrWildcard, tail: TypeOrWildcard): AppliedType =
    AppliedType(TupleConsTypeUnapplied, List(head, tail))

  def GenericTupleTypeOf(elementTypes: List[TypeOrWildcard]): Type =
    elementTypes.foldRight[Type](EmptyTupleType)(TupleConsTypeOf(_, _))

  /** The `scala.annotation.Annotation` class type. */
  val AnnotationType: TypeRef = TypeRef(scalaAnnotationPackage.packageRef, typeName("Annotation"))

  // Magic symbols that are not found on the classpath, but rather created by hand

  private def createSpecialClass(name: SimpleTypeName, parents: List[Type], flags: FlagSet): ClassSymbol =
    val cls = ClassSymbol.create(name, scalaPackage)
    cls.setTypeParams(Nil)
    cls.setParentsDirect(parents)
    cls.setGivenSelfType(None)
    cls.setFlags(flags, None)
    cls.setAnnotations(Nil)
    cls.checkCompleted()
    cls

  private def createSpecialMethod(
    owner: ClassSymbol,
    name: UnsignedTermName,
    tpe: TypeOrMethodic,
    flags: FlagSet = EmptyFlagSet,
    termParamFlags: FlagSet = EmptyFlagSet
  ): TermSymbol =
    val sym = TermSymbol
      .create(name, owner)
      .setFlags(Method | flags, privateWithin = None)
      .setDeclaredType(tpe)
      .setAnnotations(Nil)
      .autoFillParamSymss(termParamFlags)
    sym.paramSymss.foreach(_.merge.foreach(_.setAnnotations(Nil)))
    sym.checkCompleted()
    sym
  end createSpecialMethod

  val AnyClass = createSpecialClass(tpnme.Any, Nil, Abstract)

  val MatchableClass = createSpecialClass(tpnme.Matchable, AnyClass.topLevelRef :: Nil, Trait)

  val NullClass =
    createSpecialClass(tpnme.Null, AnyClass.topLevelRef :: MatchableClass.topLevelRef :: Nil, Abstract | Final)

  val SingletonClass = createSpecialClass(tpnme.Singleton, AnyClass.topLevelRef :: Nil, Final)

  val NothingAnyBounds = AbstractTypeBounds(SyntacticNothingType, AnyClass.topLevelRef)

  // See `case noRef: NoExternalSymbolRef` in PickleReader
  private[tastyquery] val scala2FakeOwner: TermSymbol =
    TermSymbol
      .createNotDeclaration(termName("<nosymbol>"), scalaPackage)
      .setFlags(Synthetic, None)
      .setDeclaredType(AnyType)
      .setAnnotations(Nil)
      .checkCompleted()
  end scala2FakeOwner

  private[tastyquery] val scala2MacroInfoFakeMethod: TermSymbol =
    TermSymbol
      .createNotDeclaration(nme.m_macro, scalaPackage)
      .setFlags(Synthetic, None)
      .setDeclaredType(NothingType)
      .setAnnotations(Nil)
      .checkCompleted()
  end scala2MacroInfoFakeMethod

  private def createSpecialTypeAlias(
    name: TypeName,
    owner: DeclaringSymbol,
    flags: FlagSet,
    alias: Type
  ): TypeMemberSymbol =
    val sym = TypeMemberSymbol.create(name, owner)
    sym.setFlags(flags, None)
    sym.setDefinition(TypeMemberDefinition.TypeAlias(alias))
    sym.setAnnotations(Nil)
    sym.checkCompleted()
    sym
  end createSpecialTypeAlias

  locally {
    createSpecialTypeAlias(tpnme.Nothing, scalaPackage, EmptyFlagSet, NothingType)
    createSpecialTypeAlias(typeName("AnyKind"), scalaPackage, EmptyFlagSet, AnyKindType)
  }

  locally {
    val andOrParamNames = List(typeName("A"), typeName("B"))

    val andTypeAlias = TypeMemberSymbol.create(typeName("&"), scalaPackage)
    andTypeAlias.setFlags(EmptyFlagSet, None)
    andTypeAlias.setDefinition(
      TypeMemberDefinition.TypeAlias(
        TypeLambda(andOrParamNames)(
          pt => List(NothingAnyBounds, NothingAnyBounds),
          pt => AndType(pt.paramRefs(0), pt.paramRefs(1))
        )
      )
    )
    andTypeAlias.setAnnotations(Nil)
    andTypeAlias.checkCompleted()

    val orTypeAlias = TypeMemberSymbol.create(typeName("|"), scalaPackage)
    orTypeAlias.setFlags(EmptyFlagSet, None)
    orTypeAlias.setDefinition(
      TypeMemberDefinition.TypeAlias(
        TypeLambda(andOrParamNames)(
          pt => List(NothingAnyBounds, NothingAnyBounds),
          pt => OrType(pt.paramRefs(0), pt.paramRefs(1))
        )
      )
    )
    orTypeAlias.setAnnotations(Nil)
    orTypeAlias.checkCompleted()

    createSpecialTypeAlias(typeName("AnyRef"), scalaPackage, EmptyFlagSet, ObjectType)

    // See `case NOtpe` in `PickleReader.scala`
    createSpecialTypeAlias(typeName("<notype>"), scalaPackage, Synthetic, NothingType)
  }

  /** A type alias of Object used to represent any reference to Object in a Java signature.
    *
    * The secret sauce is that subtype checking treats it specially:
    *
    *   tp <:< FromJavaObject
    *
    * is equivalent to:
    *
    *   tp <:< Any
    *
    * For more details, see the comment on `FromJavaObjectSymbol` in the
    * compiler's `Definitions.scala` file.
    */
  val FromJavaObjectAlias: TypeMemberSymbol =
    createSpecialTypeAlias(tpnme.FromJavaObjectAliasMagic, specialOpsPackage, JavaDefined, ObjectType)

  val FromJavaObjectType: TypeRef = TypeRef(specialOpsPackage.packageRef, FromJavaObjectAlias)

  private def equalityMethodType: MethodType =
    MethodType(List(termName("that")), List(AnyType), BooleanType)

  private def instanceTestPolyType(resultType: PolyType => Type): PolyType =
    PolyType(List(typeName("A")))(_ => List(NothingAnyBounds), resultType)

  private def stringConcatMethodType: MethodType =
    MethodType(List(termName("that")), List(AnyType), StringType)

  val Any_== = createSpecialMethod(AnyClass, nme.m_==, equalityMethodType, Final)
  val Any_!= = createSpecialMethod(AnyClass, nme.m_!=, equalityMethodType, Final)
  val Any_## = createSpecialMethod(AnyClass, nme.m_##, IntType, Final)

  val Any_equals = createSpecialMethod(AnyClass, nme.m_equals, equalityMethodType)
  val Any_hashCode = createSpecialMethod(AnyClass, nme.m_hashCode, MethodType(Nil, Nil, IntType))

  val Any_toString = createSpecialMethod(AnyClass, nme.m_toString, MethodType(Nil, Nil, StringType))

  val Any_isInstanceOf =
    createSpecialMethod(AnyClass, nme.m_isInstanceOf, instanceTestPolyType(_ => BooleanType), Final)
  val Any_asInstanceOf =
    createSpecialMethod(AnyClass, nme.m_asInstanceOf, instanceTestPolyType(_.paramRefs.head), Final)

  val Any_typeTest =
    createSpecialMethod(
      AnyClass,
      termName("$isInstanceOf$"),
      instanceTestPolyType(_ => BooleanType),
      Final | Synthetic | Artifact
    )
  val Any_typeCast =
    createSpecialMethod(
      AnyClass,
      termName("$asInstanceOf$"),
      instanceTestPolyType(_.paramRefs.head),
      Final | Synthetic | Artifact
    )

  val Any_getClass =
    // def getClass[A >: this.type](): Class[? <: A]
    val tpe = PolyType(List(typeName("A")))(
      pt => List(AbstractTypeBounds(AnyClass.thisType, AnyType)),
      pt => MethodType(Nil, Nil, ClassTypeOf(WildcardTypeArg(AbstractTypeBounds(NothingType, pt.paramRefs.head))))
    )
    createSpecialMethod(AnyClass, nme.m_getClass, tpe, Final)
  end Any_getClass

  private[tastyquery] def createObjectMagicMethods(cls: ClassSymbol): Unit =
    createSpecialMethod(cls, nme.m_eq, equalityMethodType, Final)
    createSpecialMethod(cls, nme.m_ne, equalityMethodType, Final)

    val synchronizedTpe = PolyType(List(typeName("A")))(
      pt => List(NothingAnyBounds),
      pt => MethodType(List(termName("x")), List(pt.paramRefs.head), pt.paramRefs.head)
    )
    createSpecialMethod(cls, nme.m_synchronized, synchronizedTpe)
  end createObjectMagicMethods

  lazy val Object_eq: TermSymbol = withRestrictedContext(ObjectClass.findNonOverloadedDecl(nme.m_eq))
  lazy val Object_ne: TermSymbol = withRestrictedContext(ObjectClass.findNonOverloadedDecl(nme.m_ne))

  lazy val Object_synchronized: TermSymbol =
    withRestrictedContext(ObjectClass.findNonOverloadedDecl(nme.m_synchronized))

  private[tastyquery] def createStringMagicMethods(cls: ClassSymbol): Unit =
    createSpecialMethod(cls, nme.m_+, stringConcatMethodType, Final)
  end createStringMagicMethods

  lazy val String_+ : TermSymbol = withRestrictedContext(StringClass.findNonOverloadedDecl(nme.m_+))

  private[tastyquery] def createEnumMagicMethods(cls: ClassSymbol): Unit =
    val ctorTpe = PolyType(List(typeName("E")), List(NothingAnyBounds), MethodType(Nil, Nil, UnitType))
    createSpecialMethod(cls, nme.Constructor, ctorTpe)
  end createEnumMagicMethods

  /** Creates the members that are patched from stdLibPatches on Predef.
    *
    * dotc does that generically, but it does not really work for us, as we
    * cannot read other files while loading one file.
    */
  private[tastyquery] def createPredefMagicMethods(cls: ClassSymbol): Unit =
    val TNameList = List(typeName("T"))
    val xNameList = List(termName("x"))
    val yNameList = List(termName("y"))

    val NothingAnyBoundsList = List(NothingAnyBounds)

    // assert
    val assertMethodType1 = MethodType(List(termName("assertion")), List(BooleanType), UnitType)
    val assertMethodType2 =
      MethodType(List(termName("assertion"), termName("message")), List(BooleanType, ByNameType(AnyType)), UnitType)
    for assertMethodType <- List(assertMethodType1, assertMethodType2) do
      createSpecialMethod(
        cls,
        termName("assert"),
        assertMethodType,
        Transparent | Inline | Final,
        termParamFlags = Inline
      )

    // valueOf
    val valueOfMethodType = PolyType(TNameList)(_ => NothingAnyBoundsList, pt => pt.paramRefs(0))
    createSpecialMethod(cls, termName("valueOf"), valueOfMethodType, Inline | Final)

    // summon
    val summonMethodType = PolyType(TNameList)(
      _ => NothingAnyBoundsList,
      pt => MethodType(xNameList)(_ => pt.paramRefs, mt => mt.paramRefs(0))
    )
    createSpecialMethod(cls, termName("summon"), summonMethodType, Transparent | Inline | Final, termParamFlags = Given)

    // nn
    val nnMethodType = PolyType(TNameList)(
      _ => NothingAnyBoundsList,
      pt => MethodType(xNameList)(_ => List(pt.paramRefs(0)), mt => AndType(mt.paramRefs(0), pt.paramRefs(0)))
    )
    createSpecialMethod(cls, termName("nn"), nnMethodType, Inline | Final | Extension)

    // eq and ne
    val anyRefOrNull = OrType(AnyRefType, NullType)
    val eqNeMethodType =
      MethodType(xNameList, List(anyRefOrNull), MethodType(yNameList, List(anyRefOrNull), BooleanType))
    createSpecialMethod(cls, termName("eq"), eqNeMethodType, Inline | Final | Extension, termParamFlags = Inline)
    createSpecialMethod(cls, termName("ne"), eqNeMethodType, Inline | Final | Extension, termParamFlags = Inline)
  end createPredefMagicMethods

  /** Creates one of the `ContextFunctionNClass` classes.
    *
    * There are of the form:
    *
    * ```scala
    * trait ContextFunctionN[-T0,...,-T{N-1}, +R] extends Object {
    *   def apply(using $x0: T0, ..., $x{N_1}: T{N-1}): R
    * }
    * ```
    */
  private def createContextFunctionNClass(n: Int): ClassSymbol =
    val name = typeName("ContextFunction" + n)
    val cls = ClassSymbol.create(name, scalaPackage)

    cls.setFlags(Trait | NoInitsInterface, None)
    cls.setParentsDirect(ObjectType :: Nil)
    cls.setAnnotations(Nil)
    cls.setGivenSelfType(None)

    val inputTypeParams = List.tabulate(n) { i =>
      ClassTypeParamSymbol
        .create(typeName("T" + i), cls)
        .setFlags(Contravariant, None)
        .setDeclaredBounds(NothingAnyBounds)
        .setAnnotations(Nil)
    }
    val resultTypeParam =
      ClassTypeParamSymbol
        .create(typeName("R"), cls)
        .setFlags(Covariant, None)
        .setDeclaredBounds(NothingAnyBounds)
        .setAnnotations(Nil)

    val allTypeParams = inputTypeParams :+ resultTypeParam
    allTypeParams.foreach(_.checkCompleted())
    cls.setTypeParams(allTypeParams)

    val applyMethod = TermSymbol.create(termName("apply"), cls)
    applyMethod.setFlags(Method | Abstract, None)
    applyMethod.setDeclaredType(
      MethodType(List.tabulate(n)(i => termName("x" + i)))(
        mt => inputTypeParams.map(_.localRef),
        mt => resultTypeParam.localRef
      )
    )
    applyMethod.autoFillParamSymss()
    applyMethod.setAnnotations(Nil)
    applyMethod.paramSymss.foreach(_.merge.foreach(_.setAnnotations(Nil)))
    applyMethod.checkCompleted()

    cls.checkCompleted()
    cls
  end createContextFunctionNClass

  locally {
    for (n <- 0 to 22)
      createContextFunctionNClass(n)
  }

  // Derived symbols, found on the classpath

  extension (pkg: PackageSymbol)
    private def requiredClass(name: String): ClassSymbol =
      withRestrictedContext(pkg.getDecl(typeName(name)).get.asClass)

    private def optionalClass(name: String): Option[ClassSymbol] =
      withRestrictedContext(pkg.getDecl(typeName(name)).map(_.asClass))
  end extension

  lazy val ObjectClass = javaLangPackage.requiredClass("Object")

  lazy val AnyValClass = scalaPackage.requiredClass("AnyVal")
  lazy val ArrayClass = scalaPackage.requiredClass("Array")
  lazy val SeqClass = scalaCollectionImmutablePackage.requiredClass("Seq")
  lazy val Function0Class = scalaPackage.requiredClass("Function0")

  private[tastyquery] lazy val ContextFunction1Class = scalaPackage.requiredClass("ContextFunction1")

  def FunctionNClass(n: Int): ClassSymbol =
    withRestrictedContext(scalaPackage.findDecl(typeName(s"Function$n")).asClass)

  lazy val IntClass = scalaPackage.requiredClass("Int")
  lazy val LongClass = scalaPackage.requiredClass("Long")
  lazy val FloatClass = scalaPackage.requiredClass("Float")
  lazy val DoubleClass = scalaPackage.requiredClass("Double")
  lazy val BooleanClass = scalaPackage.requiredClass("Boolean")
  lazy val ByteClass = scalaPackage.requiredClass("Byte")
  lazy val ShortClass = scalaPackage.requiredClass("Short")
  lazy val CharClass = scalaPackage.requiredClass("Char")
  lazy val UnitClass = scalaPackage.requiredClass("Unit")

  private[tastyquery] lazy val BoxedBooleanClass = javaLangPackage.requiredClass("Boolean")
  private[tastyquery] lazy val BoxedCharClass = javaLangPackage.requiredClass("Character")
  private[tastyquery] lazy val BoxedByteClass = javaLangPackage.requiredClass("Byte")
  private[tastyquery] lazy val BoxedShortClass = javaLangPackage.requiredClass("Short")
  private[tastyquery] lazy val BoxedIntClass = javaLangPackage.requiredClass("Integer")
  private[tastyquery] lazy val BoxedLongClass = javaLangPackage.requiredClass("Long")
  private[tastyquery] lazy val BoxedFloatClass = javaLangPackage.requiredClass("Float")
  private[tastyquery] lazy val BoxedDoubleClass = javaLangPackage.requiredClass("Double")

  lazy val StringClass = javaLangPackage.requiredClass("String")

  lazy val ProductClass = scalaPackage.requiredClass("Product")

  lazy val ErasedNothingClass = scalaRuntimePackage.requiredClass("Nothing$")
  lazy val ErasedBoxedUnitClass = scalaRuntimePackage.requiredClass("BoxedUnit")

  private[tastyquery] lazy val targetNameAnnotClass = scalaAnnotationPackage.optionalClass("targetName")

  private[tastyquery] lazy val internalChildAnnotClass = scalaAnnotationInternalPackage.optionalClass("Child")

  private[tastyquery] lazy val internalRepeatedAnnotClass = scalaAnnotationInternalPackage.optionalClass("Repeated")

  private[tastyquery] lazy val PrimitiveValueClasses: Set[ClassSymbol] =
    Set(UnitClass, BooleanClass, CharClass, ByteClass, ShortClass, IntClass, LongClass, FloatClass, DoubleClass)
  end PrimitiveValueClasses

  private[tastyquery] lazy val TupleNClasses = (1 to 22).map(n => scalaPackage.requiredClass(s"Tuple$n")).toSet

  private[tastyquery] lazy val PolyFunctionClass = scalaPackage.optionalClass("PolyFunction")

  private[tastyquery] lazy val QuotedExprClass = scalaQuotedPackage.requiredClass("Expr")
  private[tastyquery] lazy val QuotesClass = scalaQuotedPackage.requiredClass("Quotes")

  private[tastyquery] def isPolyFunctionSub(tpe: Type)(using Context): Boolean =
    PolyFunctionClass.exists(cls => tpe.baseType(cls).isDefined)

  private[tastyquery] def isPolyFunctionSub(prefix: Prefix)(using Context): Boolean = prefix match
    case tpe: Type => isPolyFunctionSub(tpe)
    case _         => false

  private[tastyquery] object PolyFunctionType:
    def unapply(tpe: TermRefinement)(using Context): Option[MethodicType] =
      PolyFunctionClass match
        case None =>
          None
        case Some(polyFunctionClass) =>
          if tpe.refinedName != nme.m_apply then None
          else
            tpe.refinedType match
              case methodic: MethodicType =>
                if tpe.parent.baseType(polyFunctionClass).isDefined then Some(methodic)
                else None
              case _: Type =>
                None
    end unapply

    private[tastyquery] def functionClassOf(mt: MethodicType)(using Context): ClassSymbol = mt match
      case mt: PolyType =>
        mt.resultType match
          case resultType: MethodicType =>
            functionClassOf(resultType)
          case resultType: Type =>
            throw InvalidProgramStructureException(s"Invalid PolyFunction type ${mt.showBasic}")
      case mt: MethodType =>
        FunctionNClass(mt.paramNames.size)
    end functionClassOf
  end PolyFunctionType

  lazy val hasGenericTuples = withRestrictedContext(ctx.hasGenericTuples)

  lazy val uninitializedMethod: Option[TermSymbol] =
    withRestrictedContext {
      scalaCompiletimePackage.getDecl(moduleClassName("package$package")).flatMap { packageObjectClass =>
        packageObjectClass.asClass.getDecl(termName("uninitialized"))
      }
    }
  end uninitializedMethod

  private[tastyquery] lazy val uninitializedMethodTermRef: TermRef =
    TermRef(TermRef(scalaCompiletimePackage.packageRef, termName("package$package")), termName("uninitialized"))

end Definitions
