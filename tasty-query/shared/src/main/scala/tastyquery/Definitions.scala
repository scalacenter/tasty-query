package tastyquery

import tastyquery.Contexts.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Types.*

final class Definitions private[tastyquery] (ctx: Context, rootPackage: PackageSymbol, emptyPackage: PackageSymbol):
  private given Context = ctx

  // Core packages

  val RootPackage = rootPackage
  val EmptyPackage = emptyPackage

  val specialOpsPackage = RootPackage.getPackageDeclOrCreate(nme.specialOpsPackageName)

  val scalaPackage = RootPackage.getPackageDeclOrCreate(nme.scalaPackageName)
  private val javaPackage = RootPackage.getPackageDeclOrCreate(nme.javaPackageName)
  val javaLangPackage = javaPackage.getPackageDeclOrCreate(nme.langPackageName)

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

  val RepeatedTypeUnapplied: TypeRef = TypeRef(scalaPackage.packageRef, tpnme.RepeatedParamClassMagic)
  def RepeatedTypeOf(tpe: TypeOrWildcard): AppliedType = AppliedType(RepeatedTypeUnapplied, List(tpe))

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

  // Magic symbols that are not found on the classpath, but rather created by hand

  private def createSpecialClass(name: TypeName, parents: List[Type], flags: FlagSet): ClassSymbol =
    val cls = ClassSymbol.create(name, scalaPackage)
    cls.withTypeParams(Nil)
    cls.withParentsDirect(parents)
    cls.withGivenSelfType(None)
    cls.withFlags(flags, None)
    cls.setAnnotations(Nil)
    cls.checkCompleted()
    cls

  private def createSpecialMethod(
    owner: ClassSymbol,
    name: TermName,
    tpe: TypeOrMethodic,
    flags: FlagSet = EmptyFlagSet
  ): TermSymbol =
    val sym = TermSymbol
      .create(name, owner)
      .withFlags(Method | flags, privateWithin = None)
      .withDeclaredType(tpe)
      .setAnnotations(Nil)
    sym.checkCompleted()
    sym
  end createSpecialMethod

  val AnyClass = createSpecialClass(typeName("Any"), Nil, Abstract)
    .withSpecialErasure(() => ErasedTypeRef.ClassRef(ObjectClass))

  val MatchableClass = createSpecialClass(typeName("Matchable"), AnyClass.topLevelRef :: Nil, Trait)
    .withSpecialErasure(() => ErasedTypeRef.ClassRef(ObjectClass))

  val NullClass =
    createSpecialClass(typeName("Null"), AnyClass.topLevelRef :: MatchableClass.topLevelRef :: Nil, Abstract | Final)

  val NothingAnyBounds = RealTypeBounds(SyntacticNothingType, AnyClass.topLevelRef)

  private def createSpecialTypeAlias(
    name: TypeName,
    owner: DeclaringSymbol,
    flags: FlagSet,
    alias: Type
  ): TypeMemberSymbol =
    val sym = TypeMemberSymbol.create(name, owner)
    sym.withFlags(flags, None)
    sym.withDefinition(TypeMemberDefinition.TypeAlias(alias))
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
    andTypeAlias.withFlags(EmptyFlagSet, None)
    andTypeAlias.withDefinition(
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
    orTypeAlias.withFlags(EmptyFlagSet, None)
    orTypeAlias.withDefinition(
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
      pt => List(RealTypeBounds(AnyClass.thisType, AnyType)),
      pt => MethodType(Nil, Nil, ClassTypeOf(WildcardTypeArg(RealTypeBounds(NothingType, pt.paramRefs.head))))
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

  lazy val Object_eq: TermSymbol = ObjectClass.findNonOverloadedDecl(nme.m_eq)
  lazy val Object_ne: TermSymbol = ObjectClass.findNonOverloadedDecl(nme.m_ne)
  lazy val Object_synchronized: TermSymbol = ObjectClass.findNonOverloadedDecl(nme.m_synchronized)

  private[tastyquery] def createStringMagicMethods(cls: ClassSymbol): Unit =
    createSpecialMethod(cls, nme.m_+, stringConcatMethodType, Final)
  end createStringMagicMethods

  lazy val String_+ : TermSymbol = StringClass.findNonOverloadedDecl(nme.m_+)

  private def createSpecialPolyClass(
    name: TypeName,
    paramFlags: FlagSet,
    parentConstrs: Type => List[Type]
  ): ClassSymbol =
    val cls = ClassSymbol.create(name, scalaPackage)

    val tparam = ClassTypeParamSymbol.create(typeName("T"), cls)
    tparam.withFlags(ClassTypeParam | paramFlags, None)
    tparam.setDeclaredBounds(NothingAnyBounds)
    tparam.setAnnotations(Nil)
    tparam.checkCompleted()

    cls.withTypeParams(tparam :: Nil)
    cls.withFlags(EmptyFlagSet | Artifact, None)

    val parents = parentConstrs(TypeRef(cls.thisType, tparam))
    cls.withParentsDirect(parents)
    cls
  end createSpecialPolyClass

  val ByNameParamClass2x: ClassSymbol =
    createSpecialPolyClass(tpnme.ByNameParamClassMagic, Covariant, _ => List(AnyType))
      .withSpecialErasure(() => ErasedTypeRef.ClassRef(Function0Class))

  val RepeatedParamClass: ClassSymbol =
    createSpecialPolyClass(tpnme.RepeatedParamClassMagic, Covariant, tp => List(ObjectType, SeqTypeOf(tp)))
      .withSpecialErasure(() => ErasedTypeRef.ClassRef(SeqClass))

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

    cls.withFlags(Trait | NoInitsInterface, None)
    cls.withParentsDirect(ObjectType :: Nil)
    cls.setAnnotations(Nil)
    cls.withGivenSelfType(None)

    cls.withSpecialErasure { () =>
      ErasedTypeRef.ClassRef(scalaPackage.requiredClass("Function" + n))
    }

    val inputTypeParams = List.tabulate(n) { i =>
      ClassTypeParamSymbol
        .create(typeName("T" + i), cls)
        .withFlags(ClassTypeParam | Contravariant, None)
        .setDeclaredBounds(NothingAnyBounds)
        .setAnnotations(Nil)
    }
    val resultTypeParam =
      ClassTypeParamSymbol
        .create(typeName("R"), cls)
        .withFlags(ClassTypeParam | Covariant, None)
        .setDeclaredBounds(NothingAnyBounds)
        .setAnnotations(Nil)

    val allTypeParams = inputTypeParams :+ resultTypeParam
    allTypeParams.foreach(_.checkCompleted())
    cls.withTypeParams(allTypeParams)

    val applyMethod = TermSymbol.create(termName("apply"), cls)
    applyMethod.withFlags(Method | Abstract, None)
    applyMethod.withDeclaredType(
      MethodType(List.tabulate(n)(i => termName("x" + i)))(
        mt => inputTypeParams.map(_.localRef),
        mt => resultTypeParam.localRef
      )
    )
    applyMethod.setAnnotations(Nil)
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
    private def requiredClass(name: String): ClassSymbol = pkg.getDecl(typeName(name)).get.asClass
    private def optionalClass(name: String): Option[ClassSymbol] = pkg.getDecl(typeName(name)).map(_.asClass)

  lazy val ObjectClass = javaLangPackage.requiredClass("Object")

  lazy val AnyValClass = scalaPackage.requiredClass("AnyVal")
  lazy val ArrayClass = scalaPackage.requiredClass("Array")
  lazy val SeqClass = scalaCollectionImmutablePackage.requiredClass("Seq")
  lazy val Function0Class = scalaPackage.requiredClass("Function0")

  def FunctionNClass(n: Int): ClassSymbol =
    scalaPackage.requiredClass(s"Function$n")

  lazy val IntClass = scalaPackage.requiredClass("Int")
  lazy val LongClass = scalaPackage.requiredClass("Long")
  lazy val FloatClass = scalaPackage.requiredClass("Float")
  lazy val DoubleClass = scalaPackage.requiredClass("Double")
  lazy val BooleanClass = scalaPackage.requiredClass("Boolean")
  lazy val ByteClass = scalaPackage.requiredClass("Byte")
  lazy val ShortClass = scalaPackage.requiredClass("Short")
  lazy val CharClass = scalaPackage.requiredClass("Char")
  lazy val UnitClass = scalaPackage.requiredClass("Unit")

  lazy val StringClass = javaLangPackage.requiredClass("String")

  lazy val ProductClass = scalaPackage.requiredClass("Product")

  lazy val ErasedNothingClass = scalaRuntimePackage.requiredClass("Nothing$")

  private[tastyquery] lazy val targetNameAnnotClass = scalaAnnotationPackage.optionalClass("targetName")

  private[tastyquery] lazy val internalChildAnnotClass = scalaAnnotationInternalPackage.optionalClass("Child")

  private[tastyquery] lazy val internalRepeatedAnnotClass = scalaAnnotationInternalPackage.optionalClass("Repeated")

  def isPrimitiveValueClass(sym: ClassSymbol): Boolean =
    sym == IntClass || sym == LongClass || sym == FloatClass || sym == DoubleClass ||
      sym == BooleanClass || sym == ByteClass || sym == ShortClass || sym == CharClass ||
      sym == UnitClass

  private lazy val TupleNClasses = (1 to 22).map(n => scalaPackage.requiredClass(s"Tuple$n")).toSet

  def isTupleNClass(sym: ClassSymbol): Boolean =
    sym.owner == scalaPackage && TupleNClasses.contains(sym)

  lazy val hasGenericTuples = scalaPackage.getDecl(tpnme.TupleCons).isDefined

  lazy val uninitializedMethod: Option[TermSymbol] =
    scalaCompiletimePackage.getDecl(moduleClassName("package$package")).flatMap { packageObjectClass =>
      packageObjectClass.asClass.getDecl(termName("uninitialized"))
    }
  end uninitializedMethod

  private[tastyquery] lazy val uninitializedMethodTermRef: TermRef =
    TermRef(TermRef(defn.scalaCompiletimePackage.packageRef, termName("package$package")), termName("uninitialized"))

end Definitions
