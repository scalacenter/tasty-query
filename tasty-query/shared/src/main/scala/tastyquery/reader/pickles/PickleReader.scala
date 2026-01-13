package tastyquery.reader.pickles

import scala.annotation.switch

import scala.collection.mutable
import scala.reflect.NameTransformer

import tastyquery.Annotations.*
import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Modifiers.*
import tastyquery.Names.*
import tastyquery.SourcePosition
import tastyquery.Substituters
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

import tastyquery.reader.{ReaderContext, UTF8Utils}
import tastyquery.reader.ReaderContext.rctx

import PickleReader.*
import PickleFormat.*

private[pickles] class PickleReader {
  opaque type Entries = Array[AnyRef | Null]
  opaque type Index = IArray[Int]

  private var frozenSymbols: Boolean = false

  /** The map from created local symbols to the address of their info, until it gets read. */
  private val localSymbolInfoRefs = mutable.HashMap.empty[TermOrTypeSymbol, Int]

  private val localClassGivenSelfTypeRefs = mutable.HashMap.empty[ClassSymbol, Int]

  final class Structure(using val myEntries: Entries, val myIndex: Index):
    def allRegisteredSymbols: Iterator[TermOrTypeSymbol] =
      myEntries.iterator.collect { case sym: TermOrTypeSymbol =>
        sym
      }
  end Structure

  extension (i: Index)
    inline def loopWithIndices(inline op: (Int, Int) => Unit): Unit = {
      val limit = i.length
      var j = 0
      while j < limit do {
        op(i(j), j)
        j += 1
      }
    }

  def readStructure()(using PklStream): Structure = {
    checkVersion()
    val index = pkl.readIndex()
    val entries = new Array[AnyRef | Null](index.length)

    given Index = index
    given Entries = entries

    Structure()
  }

  private def checkVersion()(using PklStream): Unit = {
    val major = pkl.readNat()
    val minor = pkl.readNat()
    if (major != MajorVersion || minor > MinorVersion)
      throw Scala2PickleFormatException(
        s"Bad pickles version, expected: $MajorVersion.$MinorVersion, found: $major.$minor"
      )
  }

  def errorBadSignature(msg: String): Nothing =
    throw Scala2PickleFormatException(msg)

  private def at[T <: AnyRef](i: Int)(op: PklStream ?=> T)(using PklStream, Entries, Index): T = {
    val tOpt = entries(i).asInstanceOf[T | Null]
    if tOpt == null then {
      val res = pkl.unsafeFork(index(i))(op)
      val existingEntry = entries(i).asInstanceOf[T | Null]
      if existingEntry == null then
        entries(i) = res
        res
      else
        // Sometimes, Types get recomputed; I don't know why. We return the existing one.
        assert((existingEntry eq res) || res.isInstanceOf[TypeOrWildcard], s"$res != $existingEntry")
        existingEntry
    } else tOpt.asInstanceOf[T] // temp hack for expression evaluator
  }

  def readTermNameRef()(using PklStream, Entries, Index): SimpleName = readNameRef().asInstanceOf[SimpleName]

  def readTypeNameRef()(using PklStream, Entries, Index): SimpleTypeName = readNameRef().asInstanceOf[SimpleTypeName]

  def readNameRef()(using PklStream, Entries, Index): SimpleName | SimpleTypeName = at(pkl.readNat())(readName())

  def readName()(using PklStream): SimpleName | SimpleTypeName = {
    val tag = pkl.readByte()
    val len = pkl.readNat()
    tag match {
      case TERMname => pkl.readTermName(len)
      case TYPEname => pkl.readTypeName(len)
      case _        => errorBadSignature("bad name tag: " + tag)
    }
  }

  private def decodeName(name: SimpleName | SimpleTypeName): SimpleName | SimpleTypeName = name match
    case name: SimpleName     => termName(NameTransformer.decode(name.name))
    case name: SimpleTypeName => typeName(NameTransformer.decode(name.name))
  end decodeName

  def readLocalSymbolRef()(using ReaderContext, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolRef() match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readLocalSymbolAt(i: Int)(using ReaderContext, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolAt(i) match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readMaybeExternalSymbolRef()(using ReaderContext, PklStream, Entries, Index): MaybeExternalSymbol =
    readMaybeExternalSymbolAt(pkl.readNat())

  def readMaybeExternalSymbolAt(i: Int)(using ReaderContext, PklStream, Entries, Index): MaybeExternalSymbol =
    at(i)(readMaybeExternalSymbol())

  def readMaybeExternalSymbol()(using ReaderContext, PklStream, Entries, Index): MaybeExternalSymbol = {
    // val start = indexCoord(readIndex) // no need yet to record the position of symbols
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    def atEnd(using PklStream) = pkl.atOffset(end)

    def readExtSymbol(): MaybeExternalSymbol =
      val name = decodeName(readNameRef())
      val owner = if (atEnd) rctx.RootPackage else readMaybeExternalSymbolRef()
      name match
        case nme.RootName | nme.UserLandRootPackageName =>
          rctx.RootPackage
        case _ =>
          def defaultRef = ExternalSymbolRef(owner, name)
          owner match
            case owner: PackageSymbol =>
              name match
                case packageName: SimpleName =>
                  // Eagerly follow packages, but nothing else
                  owner.getPackageDecl(packageName).getOrElse {
                    defaultRef
                  }
                case _ => defaultRef
            case _: NoExternalSymbolRef =>
              throw Scala2PickleFormatException(s"unexpected external owner NoSymbol for name $name")
            case _ =>
              defaultRef

    tag match {
      case NONEsym                 => return NoExternalSymbolRef.instance
      case EXTref | EXTMODCLASSref => return readExtSymbol()
      case _                       =>
    }

    // symbols that were pickled with Pickler.writeSymInfo

    val name1: SimpleTypeName | SimpleName = decodeName(readNameRef())

    assert(!frozenSymbols, s"Trying to create symbol named ${name1.toDebugString} after symbols are frozen")

    val owner = readMaybeExternalSymbolRef() match
      case sym: Symbol =>
        sym
      case noRef: NoExternalSymbolRef if tag == TYPEsym || tag == VALsym =>
        /* Sometimes, Scala 2 pickles `TYPEsym` and `VALsym` symbols whose owner references `NONEsym`.
         * This seems to happen in METHODtpe and POLYtpe that are not for declared methods
         * (but for type lambdas, or in annotations), for their parameter symbols.
         * Our system does not have a notion of "no symbol". Instead, we use one fake
         * owner to host these "orphan" symbols.
         */
        rctx.scala2FakeOwner
      case external =>
        errorBadSignature(
          s"expected local symbol reference but found $external for owner of ${name1.toDebugString} with tag $tag"
        )

    val pickleFlags = readPickleFlags(name1.isInstanceOf[TypeName])
    val flags0 = pickleFlagsToFlags(pickleFlags)

    val (privateWithin, infoRef) = {
      val ref = pkl.readNat()
      if (!isSymbolRef(ref)) (None, ref)
      else {
        val pw = readLocalSymbolAt(ref) match
          case pw: DeclaringSymbol => pw
          case pw                  => errorBadSignature(s"invalid privateWithin $pw for $owner.$name1")
        (Some(pw), pkl.readNat())
      }
    }

    val sym: TermOrTypeSymbol = tag match {
      case TYPEsym | ALIASsym =>
        val name = name1.asInstanceOf[SimpleTypeName]
        val flags = flags0

        val sym: TypeSymbolWithBounds =
          if pickleFlags.isParam then
            if owner.isClass then ClassTypeParamSymbol.create(name, owner.asClass)
            else LocalTypeParamSymbol.create(name, owner)
          else if pickleFlags.isExistential then TypeMemberSymbol.createNotDeclaration(name, owner)
          else TypeMemberSymbol.create(name, owner)
        sym.setFlags(flags, privateWithin)

      case CLASSsym if name1 == tpnme.RefinedClassMagic =>
        // return to by-pass the addition to localSymbolInfoRefs
        return ClassSymbol.createRefinedClassSymbol(owner, rctx.ObjectType, Scala2Defined)

      case CLASSsym =>
        val name2 = name1.asInstanceOf[SimpleTypeName]
        val name: ClassTypeName =
          if flags0.is(Module) then name2.withObjectSuffix
          else name2

        val flags = flags0

        val cls =
          if name == tpnme.scala2LocalChild then ClassSymbol.createNotDeclaration(name, owner)
          else ClassSymbol.create(name, owner)

        if !atEnd then localClassGivenSelfTypeRefs(cls) = pkl.readNat()

        if cls.owner == rctx.scalaPackage && name == tpnme.PredefModule then rctx.createPredefMagicMethods(cls)
        cls.setFlags(flags, privateWithin)

      case MODULEsym | VALsym =>
        val name2 = name1.asInstanceOf[SimpleName]
        val nameString = name2.name

        val name: UnsignedTermName =
          if pickleFlags.isMethod then
            name2 match
              case Scala2Constructor | Scala2TraitConstructor =>
                nme.Constructor
              case SimpleName(MangledDefaultGetterNameRegex(underlyingStr, indexStr)) =>
                DefaultGetterName(termName(underlyingStr.nn), indexStr.nn.toInt - 1)
              case _ =>
                name2
          else name2
        end name

        // Adapt the flags of getters so they become like vals/vars instead
        val flags =
          if flags0.isAllOf(Method | Accessor) && !nameString.endsWith("_=") then
            val flags1 = flags0 &~ (Method | Accessor)
            if flags1.is(StableRealizable) then flags1
            else flags1 | Mutable
          else flags0
        end flags

        /* Discard symbols that should not be seen from a Scala 3 point of view:
         * - private fields generated for vals/vars (with a trailing ' ' in their name)
         * - `$extension` methods
         * - the `getClass()` method of primitive value classes
         */
        val forceNotDeclaration =
          if flags.is(Method) then
            nameString.endsWith("$extension")
            || (name2 == nme.m_getClass && owner.isClass && owner.asClass.isPrimitiveValueClass)
          else flags.isAllOf(Private | Local) && nameString.endsWith(" ")

        val sym =
          if pickleFlags.isExistential || forceNotDeclaration then TermSymbol.createNotDeclaration(name, owner)
          else TermSymbol.create(name, owner)
        sym.setFlags(flags, privateWithin)

      case _ =>
        errorBadSignature("bad symbol tag: " + tag)
    }

    localSymbolInfoRefs(sym) = infoRef
    sym
  }

  def completeAllSymbolTypes(structure: Structure)(using ReaderContext, PklStream, Entries, Index): Unit =
    frozenSymbols = true
    for sym <- structure.allRegisteredSymbols do completeSymbolType(sym)

  private def completeSymbolType(sym: TermOrTypeSymbol)(using ReaderContext, PklStream, Entries, Index): Unit =
    localSymbolInfoRefs.remove(sym) match
      case None =>
        // If it is not there, it means it was already computed and assigned, or is being computed
        ()

      case Some(infoRef) =>
        val tpe =
          try at(infoRef)(readTypeMappable())
          catch
            case t: Throwable =>
              throw new Scala2PickleFormatException(s"error while unpickling the type of $sym", t)

        sym match
          case sym: TypeSymbolWithBounds =>
            val bounds = tpe match
              case tpe: TypeOrWildcard => translateTempPolyForTypeMember(tpe)
              case _ => throw Scala2PickleFormatException(s"Type or type bounds expected for $sym gut found $tpe")
            sym match
              case sym: TypeMemberSymbol =>
                sym.setDefinition(bounds match
                  case bounds: AbstractTypeBounds => TypeMemberDefinition.AbstractType(bounds)
                  case TypeAlias(alias)           => TypeMemberDefinition.TypeAlias(alias)
                )
              case sym: TypeParamSymbol =>
                sym.setDeclaredBounds(bounds)

          case cls: ClassSymbol =>
            assert(!cls.isRefinementClass, s"refinement class $cls should not have stored the type $tpe")

            val (typeParams, scala2ParentTypes) = tpe match
              case TempPolyType(tparams, restpe: TempClassInfoType) =>
                (tparams.map(_.asInstanceOf[ClassTypeParamSymbol]), restpe.parentTypes)
              case tpe: TempClassInfoType =>
                (Nil, tpe.parentTypes)
              case tpe =>
                throw Scala2PickleFormatException(s"unexpected type $tpe for $cls, owner is ${cls.owner}")

            cls.setTypeParams(typeParams)

            val parentTypes =
              if cls.isAnyVal then
                // Patch the superclasses of AnyVal to contain Matchable
                scala2ParentTypes :+ rctx.MatchableType
              else if cls.isTupleNClass && rctx.hasGenericTuples then
                // Patch the superclass of TupleN classes to inherit from *:
                rctx.GenericTupleTypeOf(typeParams.map(_.localRef)) :: scala2ParentTypes.tail
              else scala2ParentTypes
            cls.setParentsDirect(parentTypes)

            val givenSelfType = localClassGivenSelfTypeRefs.remove(cls).map(addr => at(addr)(readTrueType()))
            cls.setGivenSelfType(givenSelfType)

          case sym: TermSymbol =>
            val storedType = tpe match
              case storedType: Type => storedType
              case storedType => throw Scala2PickleFormatException(s"Type expected for $sym but found $storedType")

            val paramSymss = paramSymssOf(storedType)
            val unwrappedTpe: TypeOrMethodic = translateTempMethodAndPolyForMethod(storedType)

            if sym.isMethod && sym.name == nme.Constructor then
              val cls = sym.owner.asClass
              completeSymbolType(cls)
              for typeParam <- cls.typeParams do completeSymbolType(typeParam)
              sym.setDeclaredType(patchConstructorType(cls, unwrappedTpe))
              sym.setParamSymss(patchConstructorParamSymss(sym, paramSymss))
            else
              sym.setDeclaredType(unwrappedTpe)
              sym.setParamSymss(paramSymss)
  end completeSymbolType

  private def paramSymssOf(storedType: Type): List[ParamSymbolsClause] = storedType match
    case TempMethodType(paramSyms, resType) =>
      Left(paramSyms) :: paramSymssOf(resType.requireType)
    case TempPolyType(paramSyms, resType) =>
      Right(paramSyms.map(_.asInstanceOf[LocalTypeParamSymbol])) :: paramSymssOf(resType.requireType)
    case _ =>
      Nil
  end paramSymssOf

  private def patchConstructorType(cls: ClassSymbol, tpe: TypeOrMethodic)(using ReaderContext): TypeOrMethodic =
    def resultToUnit(tpe: TypeOrMethodic): TypeOrMethodic =
      tpe match
        case tpe: PolyType =>
          tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypeBounds, resultToUnit(tpe.resultType))
        case tpe: MethodType =>
          tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypes, resultToUnit(tpe.resultType))
        case _: Type =>
          rctx.UnitType

    val tpe1 = resultToUnit(tpe)
    cls.makePolyConstructorType(tpe1)
  end patchConstructorType

  private def patchConstructorParamSymss(
    ctor: TermSymbol,
    paramSymss: List[ParamSymbolsClause]
  ): List[ParamSymbolsClause] =
    val cls = ctor.owner.asClass
    val clsTypeParams = cls.typeParams

    if clsTypeParams.isEmpty then paramSymss
    else
      // Create the symbols; don't assign bounds yet
      val ctorTypeParams = clsTypeParams.map { clsTypeParam =>
        LocalTypeParamSymbol
          .create(clsTypeParam.name, ctor)
          .setFlags(EmptyFlagSet, privateWithin = None)
          .setAnnotations(Nil)
      }

      val ctorTypeParamRefs = ctorTypeParams.map(_.localRef)
      def subst(tpe: TypeMappable): tpe.ThisTypeMappableType =
        Substituters.substLocalThisClassTypeParams(tpe, clsTypeParams, ctorTypeParamRefs)

      // Assign the bounds; when they refer to each other we need to substitute for the new local refs
      for (clsTypeParam, ctorTypeParam) <- clsTypeParams.lazyZip(ctorTypeParams) do
        ctorTypeParam.setDeclaredBounds(subst(clsTypeParam.declaredBounds))

      // Overwrite the types of the existing param syms to refer to the new local refs as well
      for
        case Left(paramSyms) <- paramSymss
        paramSym <- paramSyms
      do paramSym.overwriteDeclaredType(subst(paramSym.declaredType))

      Right(ctorTypeParams) :: paramSymss
    end if
  end patchConstructorParamSymss

  def readChildren()(using ReaderContext, PklStream, Entries, Index): Unit =
    val tag = pkl.readByte()
    assert(tag == CHILDREN)
    val end = pkl.readEnd()
    val target = readLocalSymbolRef().asClass
    val children: List[Symbol | Scala2ExternalSymRef] =
      pkl.until(
        end,
        () =>
          readMaybeExternalSymbolRef() match
            case sym: ClassSymbol if sym.name == tpnme.scala2LocalChild => target
            case sym: Symbol                                            => sym
            case external: ExternalSymbolRef                            => external.toScala2ExternalSymRef
            case _: NoExternalSymbolRef =>
              throw errorBadSignature(s"illegal NoSymbol as sealed child of $target")
      )
    target.setScala2SealedChildren(children)
  end readChildren

  private def readPickleFlags(isType: Boolean)(using PklStream): PickleFlagSet =
    PickleFlagSet(pkl.readLongNat(), isType)

  private def pickleFlagsToFlags(pickleFlags: PickleFlagSet): FlagSet = {
    var flags: FlagSet = Scala2Defined

    if pickleFlags.isProtected then flags |= Protected
    if pickleFlags.isOverride then flags |= Override
    if pickleFlags.isPrivate then flags |= Private
    if pickleFlags.isAbstract || pickleFlags.isDeferred then flags |= Abstract
    if pickleFlags.isFinal then flags |= Final
    if pickleFlags.isMethod then flags |= Method
    if pickleFlags.isInterface then flags |= NoInitsInterface
    if pickleFlags.isModule then
      flags |= Module
      if pickleFlags.isType then flags |= ModuleClassCreationFlags
      else flags |= ModuleValCreationFlags
    if pickleFlags.isImplicit then flags |= Implicit
    if pickleFlags.isSealed then flags |= Sealed
    if pickleFlags.isCase then flags |= Case
    if pickleFlags.isMutable then flags |= Mutable
    // if pickleFlags.isParam then flags |= Param
    // if pickleFlags.isPackage then flags |= Package
    if pickleFlags.isMacro then flags |= Macro
    if pickleFlags.isCovariant then flags |= Covariant
    // if pickleFlags.isByNameParam then flags |= ByNameParam
    if pickleFlags.isContravariant then flags |= Contravariant
    // if pickleFlags.isLabel then flags |= Label
    if pickleFlags.isAbstractOverride then flags |= AbsOverride
    if pickleFlags.isLocal then flags |= Local
    // if pickleFlags.isJava then flags |= JavaDefined
    if pickleFlags.isSynthetic then flags |= Synthetic
    if pickleFlags.isStable then flags |= StableRealizable
    if pickleFlags.isStatic then flags |= Static
    if pickleFlags.isCaseAccessor then flags |= CaseAccessor
    if pickleFlags.hasDefault then flags |= HasDefault
    if pickleFlags.isTrait then flags |= Trait
    // if pickleFlags.isBridge then flags |= Bridge
    if pickleFlags.isAccessor then flags |= Accessor
    // if pickleFlags.isSuperAccessor then flags |= Scala2SuperAccessor
    if pickleFlags.isParamAccessor then flags |= ParamAccessor
    // if pickleFlags.isModuleVar then flags |= Scala2ModuleVar
    if pickleFlags.isLazy then flags |= Lazy
    // if pickleFlags.isMixedIn then flags |= MixedIn
    // if pickleFlags.isExistential then flags |= Scala2Existential
    // if pickleFlags.isExpandedName then flags |= Scala2ExpandedName
    // if pickleFlags.isSpecialized then flags |= Specialized
    // if pickleFlags.isVBridge then flags |= EmptyFlagSet
    // if pickleFlags.isJavaVarargs then flags |= JavaVarargs
    if pickleFlags.isEnum then flags |= Enum

    flags
  }

  def missingSymbolEntry(index: Int)(using PklStream, Entries, Index): Boolean =
    missingEntry(index) && isSymbolEntry(index)

  def missingEntry(index: Int)(using Entries): Boolean =
    entries(index) == null

  def isSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean = {
    val tag = pkl.bytes(index(i)).toInt
    (firstSymTag <= tag && tag <= lastSymTag)
  }

  def isRefinementSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    pkl.unsafeFork(index(i)) {
      val tag = pkl.readByte().toInt
      assert(tag == CLASSsym)
      pkl.readNat() // read length
      val result = readNameRef() == tpnme.RefinedClassMagic
      result
    }

  /** Does entry represent a symbol annotation? */
  def isSymbolAnnotationEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    val tag = pkl.bytes(index(i))
    tag == SYMANNOT

  def isChildrenEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    val tag = pkl.bytes(index(i))
    tag == CHILDREN

  private def isNameEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    val tag = pkl.bytes(index(i))
    tag == TERMname || tag == TYPEname

  def isSymbolRef(i: Int)(using PklStream, Index): Boolean = {
    val tag = pkl.bytes(index(i))
    (firstSymTag <= tag && tag <= lastExtSymTag)
  }

  private def readPrefixRef()(using ReaderContext, PklStream, Entries, Index): Prefix =
    readTypeMappableRef() match
      case tpe: Prefix => tpe
      case tpe         => errorBadSignature(s"expected a prefix but got $tpe")

  private def readTrueTypeRef()(using ReaderContext, PklStream, Entries, Index): Type =
    readTypeMappableRef() match
      case tpe: Type => tpe
      case tpe       => errorBadSignature(s"expected a type but got $tpe")

  /** Read a type */
  private def readTrueType()(using ReaderContext, PklStream, Entries, Index): Type =
    readTypeMappable() match
      case tpe: Type => tpe
      case tpe       => errorBadSignature(s"expected a type but got $tpe")

  private def readTypeOrWildcardRef()(using ReaderContext, PklStream, Entries, Index): TypeOrWildcard =
    readTypeMappableRef() match
      case tpe: TypeOrWildcard => tpe
      case tpe                 => errorBadSignature(s"expected a type argument but got $tpe")

  private def readTypeOrMethodicRef()(using ReaderContext, PklStream, Entries, Index): TypeOrMethodic =
    readTypeMappableRef() match
      case tpe: TypeOrMethodic => tpe
      case tpe                 => errorBadSignature(s"expected a type or methodic type but got $tpe")

  private def readTypeMappableRef()(using ReaderContext, PklStream, Entries, Index): TypeMappable =
    at(pkl.readNat())(readTypeMappable())

  private def readTypeMappable()(using ReaderContext, PklStream, Entries, Index): TypeMappable = {
    assert(frozenSymbols, s"Trying to read a type but symbols have not been frozen yet")

    def select(pre: Prefix, sym: TermOrTypeSymbol): Type =
      // structural members need to be selected by name, their symbols are only
      // valid in the synthetic refinement class that defines them.
      /*TODO if !pre.isInstanceOf[ThisType] && isRefinementClass(sym.owner) then pre.select(sym.name)
      else*/ NamedType(pre, sym)

    val tag = pkl.readByte()
    val end = pkl.readEnd()
    (tag: @switch) match {
      case NOtpe =>
        /* This should not happen, but it seems to surface in complicated
         * refinement types, such as the one in the constructor of
         * `scala.collection.MapView`.
         * Since we do not have a `NoType` in our model, we replace it with a
         * reference to a fake alias of `Nothing`. This allows us not to crash,
         * while still being able to detect these erroneous types if we really
         * want to.
         */
        TypeRef(rctx.scalaPackage.packageRef, typeName("<notype>"))
      case NOPREFIXtpe =>
        NoPrefix
      case THIStpe =>
        readMaybeExternalSymbolRef() match
          case sym: ClassSymbol =>
            sym.thisType
          case sym: PackageSymbol =>
            sym.packageRef
          case sym: Symbol =>
            throw Scala2PickleFormatException(s"cannot construct a THIStpe for $sym")
          case external: ExternalSymbolRef =>
            external.toNamedType(NoPrefix) match
              case termRef: TermRef => termRef // necessary for package refs?
              case typeRef: TypeRef => ThisType(typeRef)
          case _: NoExternalSymbolRef =>
            throw Scala2PickleFormatException("cannot construct a THIStpe for NoSymbol")
      case SINGLEtpe =>
        val pre = readPrefixRef()
        val designator = readMaybeExternalSymbolRef()
        designator match
          case sym: PackageSymbol          => sym.packageRef
          case sym: TermOrTypeSymbol       => NamedType(pre, sym)
          case external: ExternalSymbolRef => external.toNamedType(pre)
          case _: NoExternalSymbolRef      => throw Scala2PickleFormatException("SINGLEtpe references NoSymbol")
      case SUPERtpe =>
        val thistpe = readTrueTypeRef() match
          case thistpe: ThisType => thistpe
          case thistpe           => throw Scala2PickleFormatException(s"Unexpected this type for SuperType: $thistpe")
        val supertpe = readTrueTypeRef()
        SuperType(thistpe, Some(supertpe))
      case CONSTANTtpe =>
        readConstantRef() match
          case c: Constant => ConstantType(c)
          case tp: TermRef => tp
      case TYPEREFtpe =>
        val originalPrefix = readPrefixRef()
        val designator = readMaybeExternalSymbolRef()
        val prefix = originalPrefix match
          /*case thispre: ThisType =>
            // The problem is that class references super.C get pickled as
            // this.C. Dereferencing the member might then get an overriding class
            // instance. The problem arises for instance for LinkedHashMap#MapValues
            // and also for the inner Transform class in all views. We fix it by
            // replacing the this with the appropriate super.
            if (sym.owner != thispre.cls) {
              val overriding = thispre.cls.info.decls.asClass.getDecl(sym.name)
              if (overriding.exists && overriding != sym) {
                val base = pre.baseType(sym.owner)
                assert(base.exists)
                pre = SuperType(thispre, base)
              }
            }*/
          case NoPrefix if designator.isInstanceOf[ClassTypeParamSymbol] =>
            /* Scala 2 pickles references to class type parameters of enclosing
             * classes with NoPrefix, but the Scala 3 type system and tasty-query
             * demand that it be `ThisType` of the enclosing class instead.
             */
            designator.asInstanceOf[ClassTypeParamSymbol].owner.thisType
          case _ =>
            originalPrefix
        end prefix
        //val tycon = select(pre, sym)
        val tycon = designator match
          case sym: PackageSymbol          => sym.packageRef
          case sym: TermOrTypeSymbol       => select(prefix, sym)
          case external: ExternalSymbolRef => external.toNamedType(prefix)
          case _: NoExternalSymbolRef      => throw Scala2PickleFormatException("TYPEREFtpe references NoSymbol")
        val args = pkl.until(end, () => readTypeOrWildcardRef())
        /*if (sym == defn.ByNameParamClass2x) ByNameType(args.head)
        else if (ctx.settings.scalajs.value && args.length == 2 &&
            sym.owner == JSDefinitions.jsdefn.ScalaJSJSPackageClass && sym == JSDefinitions.jsdefn.PseudoUnionClass) {
          // Treat Scala.js pseudo-unions as real unions, this requires a
          // special-case in erasure, see TypeErasure#eraseInfo.
          OrType(args(0), args(1))
        }
        else if (args.nonEmpty) tycon.safeAppliedTo(EtaExpandIfHK(sym.typeParams, args.map(translateTempPoly)))
        else if (sym.typeParams.nonEmpty) tycon.EtaExpand(sym.typeParams)
        else tycon*/
        def isMagicClass(tpe: Type, magicName: SimpleTypeName): Boolean = tpe match
          case tpe: TypeRef if tpe.name == magicName =>
            tpe.prefix match
              case prefix: PackageRef => prefix.symbol.isScalaPackage
              case _                  => false
          case _ =>
            false
        end isMagicClass
        if args.isEmpty then tycon
        else
          val tyconType = tycon.requireType
          if isMagicClass(tyconType, tpnme.scala2ByName) then ByNameType(args.head.requireType)
          else if isMagicClass(tyconType, tpnme.RepeatedParamClassMagic) then RepeatedType(args.head.requireType)
          else AppliedType(tyconType, args.map(translateTempPolyForTypeArg(_)))
      case TYPEBOUNDStpe =>
        val lo = readTrueTypeRef()
        val hi = readTrueTypeRef()
        // TODO? createNullableTypeBounds(lo, hi)
        WildcardTypeArg(AbstractTypeBounds(lo, hi))
      case REFINEDtpe =>
        val clazzIndex = pkl.readNat()
        val clazz = readLocalSymbolAt(clazzIndex).asClass
        val parents = pkl.until(end, () => readTrueTypeRef())
        val parent = parents.reduceLeft(AndType(_, _))
        val decls = clazz.declarationsOfClass
        if decls.isEmpty then parent
        else
          val refined = decls.toList.foldLeft(parent) { (parent, sym) =>
            completeSymbolType(sym)
            sym match
              case sym: TypeMemberSymbol =>
                TypeRefinement(parent, sym.name, sym.declaredBounds)
              case sym: TermSymbol =>
                TermRefinement(parent, sym.kind == TermSymbolKind.Val, sym.name, sym.declaredType)
              case _: TypeParamSymbol | _: ClassSymbol =>
                errorBadSignature(s"invalid symbol in refinement class: $sym of type ${sym.getClass()}")
          }
          RecType.fromRefinedClassDecls(refined, clazz)
      case CLASSINFOtpe =>
        val clazz = readLocalSymbolRef()
        TempClassInfoType(pkl.until(end, () => readTrueTypeRef()))
      case METHODtpe | IMPLICITMETHODtpe =>
        val restpe = readTypeOrMethodicRef()
        val params = pkl.until(end, () => readLocalSymbolRef().asTerm)
        params.foreach(completeSymbolType(_))
        TempMethodType(params, restpe)
      case POLYtpe =>
        // create PolyType
        //   - PT => register at index
        val restpe = readTypeMappableRef()
        val typeParams = pkl.until(end, () => readLocalSymbolRef().asInstanceOf[TypeParamSymbol])
        if typeParams.nonEmpty then
          typeParams.foreach(completeSymbolType(_))
          TempPolyType(typeParams, restpe)
        else restpe
      case EXISTENTIALtpe =>
        val restpe = readTrueTypeRef()
        // TODO Should these be LocalTypeParamSymbols?
        val boundSyms = pkl.until(end, () => readLocalSymbolRef().asInstanceOf[TypeMemberSymbol])
        for boundSym <- boundSyms do completeSymbolType(boundSym)
        elimExistentials(boundSyms, restpe)
      case ANNOTATEDtpe =>
        val underlying = readTrueTypeRef()
        val annots = pkl.until(end, () => readTypeAnnotationRef())
        annots.foldLeft(underlying)(AnnotatedType(_, _))
      case _ =>
        noSuchTypeTag(tag, end)
    }
  }

  private def readTypeParams()(using ReaderContext, PklStream, Entries, Index): List[ClassTypeParamSymbol] = {
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    if (tag == POLYtpe) {
      val unusedRestperef = pkl.readNat()
      pkl.until(end, () => readLocalSymbolRef().asInstanceOf[ClassTypeParamSymbol])
    } else Nil
  }

  /** Convert temp poly type to TypeLambda and leave other types alone. */
  private def translateTempPolyForTypeArg(tp: TypeOrWildcard)(using ReaderContext): TypeOrWildcard =
    translateTempPolyForTypeMember(tp) match
      case TypeAlias(alias)           => alias
      case bounds: AbstractTypeBounds => WildcardTypeArg(bounds)
  end translateTempPolyForTypeArg

  /** Convert temp poly type to TypeLambda and leave other types alone. */
  private def translateTempPolyForTypeMember(tp: TypeOrWildcard)(using ReaderContext): TypeBounds = tp match
    case tp: WildcardTypeArg =>
      def rec(bound: Type): Type =
        translateTempPolyForTypeMember(bound).asInstanceOf[TypeAlias].alias
      AbstractTypeBounds(rec(tp.bounds.low), rec(tp.bounds.high))

    case TempPolyType(tparams, restpe) =>
      val localTParams = tparams.asInstanceOf[List[LocalTypeParamSymbol]] // no class type params in type lambdas
      restpe match
        case restpe: WildcardTypeArg =>
          val low =
            if restpe.bounds.low.isExactlyNothing then restpe.bounds.low
            else TypeLambda.fromParams(localTParams, restpe.bounds.low)
          val high = TypeLambda.fromParams(localTParams, restpe.bounds.high)
          AbstractTypeBounds(low, high)
        case restpe: Type =>
          val alias = TypeLambda.fromParams(localTParams, restpe)
          TypeAlias(alias)
        case _ =>
          throw Scala2PickleFormatException(s"Invalid result type of type lambda: $restpe")

    case tp: Type =>
      TypeAlias(tp)
  end translateTempPolyForTypeMember

  /** Convert temp poly type to PolyType and leave other types alone. */
  private def translateTempMethodAndPolyForMethod(tp: TypeOrMethodic)(using ReaderContext): TypeOrMethodic = tp match
    case TempMethodType(paramSyms, resType) =>
      resType match
        case resType: TypeOrMethodic =>
          MethodType.fromSymbols(paramSyms, translateTempMethodAndPolyForMethod(resType))
        case _ =>
          throw Scala2PickleFormatException(s"Invalid type for method: $tp")

    case TempPolyType(tparams, restpe) =>
      val localTParams = tparams.asInstanceOf[List[LocalTypeParamSymbol]] // no class type params in methods
      restpe match
        case restpe: TypeOrMethodic =>
          PolyType.fromParams(localTParams, translateTempMethodAndPolyForMethod(restpe))
        case _ =>
          throw Scala2PickleFormatException(s"Invalid type for method: $tp")

    case tp =>
      tp
  end translateTempMethodAndPolyForMethod

  private def noSuchTypeTag(tag: Int, end: Int): Nothing =
    errorBadSignature("bad type tag: " + tag)

  // --- Annotations ---

  def readSymbolAnnotation()(using ReaderContext, PklStream, Entries, Index): (TermOrTypeSymbol, Annotation) =
    val tag = pkl.readByte()
    if tag != SYMANNOT then errorBadSignature("symbol annotation expected (" + tag + ")")
    val end = pkl.readEnd()
    val target = readLocalSymbolRef() match
      case target: TermOrTypeSymbol => target
      case target: PackageSymbol    => errorBadSignature(s"found unexpected annotation for package symbol $target")
    val annotation = readAnnotationContents(end)
    (target, annotation)
  end readSymbolAnnotation

  private def readTypeAnnotationRef()(using ReaderContext, PklStream, Entries, Index): Annotation =
    at(pkl.readNat())(readTypeAnnotation())

  private def readTypeAnnotation()(using ReaderContext, PklStream, Entries, Index): Annotation =
    val tag = pkl.readByte()
    if tag != ANNOTINFO then errorBadSignature("annotation expected (" + tag + ")")
    val end = pkl.readEnd()
    readAnnotationContents(end)
  end readTypeAnnotation

  private def readAnnotationContents(end: Int)(using ReaderContext, PklStream, Entries, Index): Annotation =
    val pos = SourcePosition.NoPosition

    val annotationType = readTrueTypeRef()

    val args: List[TermTree] = pkl.until(
      end,
      { () =>
        val argref = pkl.readNat()
        if isNameEntry(argref) then
          val name = at(argref)(readName())
          val arg = readClassfileAnnotArg(pkl.readNat())
          NamedArg(name.asInstanceOf[SimpleName], arg)(pos)
        else readAnnotArg(argref)
      }
    )

    Annotation.fromAnnotTypeAndArgs(annotationType, args)
  end readAnnotationContents

  private def readClassfileAnnotArg(i: Int)(using ReaderContext, PklStream, Entries, Index): TermTree =
    pkl.bytes(index(i)) match
      case ANNOTINFO     => at(i)(readAnnotInfoArg())
      case ANNOTARGARRAY => at(i)(readArrayAnnotArg())
      case _             => readAnnotArg(i)
  end readClassfileAnnotArg

  private def readAnnotInfoArg()(using ReaderContext, PklStream, Entries, Index): TermTree =
    pkl.readByte() // skip the `ANNOTINFO` tag
    val end = pkl.readEnd()
    readAnnotationContents(end).tree
  end readAnnotInfoArg

  /** Read a ClassfileAnnotArg (argument to a classfile annotation). */
  private def readArrayAnnotArg()(using ReaderContext, PklStream, Entries, Index): TermTree =
    val pos = SourcePosition.NoPosition

    pkl.readByte() // skip the `annotargarray` tag
    val end = pkl.readEnd()
    // array elements are trees representing instances of scala.annotation.Annotation
    val elems = pkl.until(end, () => readClassfileAnnotArg(pkl.readNat()))
    SeqLiteral(elems, TypeWrapper(rctx.AnnotationType)(pos))(pos)
  end readArrayAnnotArg

  /** Read an annotation argument, which is pickled either as a Constant or a Tree. */
  private def readAnnotArg(i: Int)(using ReaderContext, PklStream, Entries, Index): TermTree =
    pkl.bytes(index(i)) match
      case TREE =>
        at(i)(guardedReadTermTree())
      case _ =>
        val const = at(i)(readConstant())
        val pos = SourcePosition.NoPosition
        const match
          case c: Constant => Literal(c)(pos)
          case tp: TermRef => Ident(tp.name.asInstanceOf[UnsignedTermName])(tp)(pos)
  end readAnnotArg

  private def guardedReadTermTree()(using ReaderContext, PklStream, Entries, Index): TermTree =
    try readTermTree()
    catch
      case _: UnsupportedTreeInAnnotationException =>
        val termRef = rctx.uninitializedMethodTermRef
        Ident(termRef.name.asInstanceOf[UnsignedTermName])(termRef)(SourcePosition.NoPosition)
  end guardedReadTermTree

  // --- Trees ---

  private def readTermTreeRef()(using ReaderContext, PklStream, Entries, Index): TermTree =
    at(pkl.readNat())(readTermTree())

  private def readTermTree()(using ReaderContext, PklStream, Entries, Index): TermTree =
    readOptTree().get.asInstanceOf[TermTree]

  private def readTypeTreeRef()(using ReaderContext, PklStream, Entries, Index): TypeTree =
    at(pkl.readNat())(readTypeTree())

  private def readTypeTree()(using ReaderContext, PklStream, Entries, Index): TypeTree =
    readOptTree().get.asInstanceOf[TypeTree]

  private def readAnyTreeRef()(using ReaderContext, PklStream, Entries, Index): Tree =
    at(pkl.readNat())(readAnyTree())

  private def readAnyTree()(using ReaderContext, PklStream, Entries, Index): Tree =
    readOptTree().get

  private def readOptTreeRef()(using ReaderContext, PklStream, Entries, Index): Option[Tree] =
    at(pkl.readNat())(readOptTree())

  private def readOptTree()(using ReaderContext, PklStream, Entries, Index): Option[Tree] =
    val treeTag = pkl.readByte()
    if treeTag != TREE then errorBadSignature(s"unexpected non-tree tag $treeTag")

    val end = pkl.readEnd()
    val tag = pkl.readByte()

    if tag == EMPTYtree then None
    else Some(readNonEmptyTreeImpl(tag, end))
  end readOptTree

  private def readNonEmptyTreeImpl(tag: Int, end: Int)(using ReaderContext, PklStream, Entries, Index): Tree =
    val pos = SourcePosition.NoPosition

    val tpe = readTypeMappableRef()

    (tag: @switch) match
      case BLOCKtree =>
        val expr = readTermTreeRef()
        val stats = pkl.until(end, () => readAnyTreeRef()).map(_.asInstanceOf[StatementTree])
        Block(stats, expr)(pos)

      case ASSIGNtree =>
        val lhs = readTermTreeRef()
        val rhs = readTermTreeRef()
        Assign(lhs, rhs)(pos)

      case IFtree =>
        val cond = readTermTreeRef()
        val thenp = readTermTreeRef()
        val elsep = readTermTreeRef()
        If(cond, thenp, elsep)(pos)

      case THROWtree =>
        Throw(readTermTreeRef())(pos)

      case NEWtree =>
        New(readTypeTreeRef())(pos)

      case TYPEDtree =>
        val expr = readTermTreeRef()
        val tpt = readTypeTreeRef()
        Typed(expr, tpt)(pos)

      case TYPEAPPLYtree =>
        val fun = readTermTreeRef()
        val args = pkl.until(end, () => readTypeTreeRef())
        TypeApply(fun, args)(pos)

      case APPLYtree =>
        // this is going to have an unsigned reference, which is not going to be good; dotc does not do any better
        val fun = readTermTreeRef()
        val args = pkl.until(end, () => readTermTreeRef())
        Apply(fun, args)(pos)

      case THIStree =>
        val symbol = readLocalSymbolRef()
        val name = readTypeNameRef()
        symbol match
          case symbol: ClassSymbol   => This(TypeIdent(symbol.name)(symbol.localRef)(pos))(pos)
          case symbol: PackageSymbol => Ident(symbol.name)(symbol.packageRef)(pos)
          case _                     => errorBadSignature(s"illegal THIStree of $symbol")

      case SELECTtree =>
        val designator = readMaybeExternalSymbolRef()
        val qualifier = readTermTreeRef()
        val name = readTermNameRef()
        Select(qualifier, name)(None)(pos)

      case IDENTtree =>
        val designator = readMaybeExternalSymbolRef()
        val name = readTermNameRef()
        val tpe: TermReferenceType = designator match
          case sym: TermSymbol                               => sym.localRef
          case sym: PackageSymbol                            => sym.packageRef
          case external: ExternalSymbolRef                   => external.toTermRef(NoPrefix)
          case _: NoExternalSymbolRef if name == nme.m_macro => rctx.scala2MacroInfoFakeMethod.localRef
          case _ =>
            errorBadSignature(s"illegal $designator for IDENTtree (name '$name')")
        Ident(name)(tpe)(pos)

      case LITERALtree =>
        readConstantRef() match
          case c: Constant => Literal(c)(pos)
          case tp: TermRef => Ident(tp.name.asInstanceOf[UnsignedTermName])(tp)(pos)

      case TYPEtree =>
        TypeWrapper(tpe.asInstanceOf[NonEmptyPrefix])(pos)

      case ANNOTATEDtree =>
        val annot = readTermTreeRef()
        val tpt = readTypeTreeRef()
        AnnotatedTypeTree(tpt, annot)(pos)

      case SINGLETONTYPEtree =>
        SingletonTypeTree(readTermTreeRef())(pos)

      case SELECTFROMTYPEtree =>
        val qualifier = readTypeTreeRef()
        val selector = readTypeNameRef()
        SelectTypeTree(qualifier, selector)(pos)

      case COMPOUNDTYPEtree =>
        readOptTreeRef()
        TypeWrapper(tpe.requireType)(pos)

      case APPLIEDTYPEtree =>
        val tpt = readTypeTreeRef()
        val args = pkl.until(end, () => readAnyTreeRef()).map {
          case tpt: TypeArgTree => tpt
          case tpt              => errorBadSignature(s"illegal type argument $tpt")
        }
        AppliedTypeTree(tpt, args)(pos)

      case TYPEBOUNDStree =>
        val lo = readTypeTreeRef()
        val hi = readTypeTreeRef()
        ExplicitTypeBoundsTree(lo, hi)(pos)

      case EXISTENTIALTYPEtree =>
        readOptTreeRef()
        pkl.until(end, () => readOptTreeRef())
        TypeWrapper(tpe.requireType)(pos)

      case _ =>
        throw UnsupportedTreeInAnnotationException(s"unsupported tree in annotation with tag $tag")
  end readNonEmptyTreeImpl

  // --- Constants ---

  private def readConstantRef()(using ReaderContext, PklStream, Entries, Index): Constant | TermRef =
    at(pkl.readNat())(readConstant())

  /** Read a constant */
  private def readConstant()(using ReaderContext, PklStream, Entries, Index): Constant | TermRef = {
    import java.lang.Float.intBitsToFloat
    import java.lang.Double.longBitsToDouble

    val tag = pkl.readByte().toInt
    val len = pkl.readNat()
    (tag: @switch) match {
      case LITERALunit    => Constant(())
      case LITERALboolean => Constant(pkl.readLong(len) != 0L)
      case LITERALbyte    => Constant(pkl.readLong(len).toByte)
      case LITERALshort   => Constant(pkl.readLong(len).toShort)
      case LITERALchar    => Constant(pkl.readLong(len).toChar)
      case LITERALint     => Constant(pkl.readLong(len).toInt)
      case LITERALlong    => Constant(pkl.readLong(len))
      case LITERALfloat   => Constant(intBitsToFloat(pkl.readLong(len).toInt))
      case LITERALdouble  => Constant(longBitsToDouble(pkl.readLong(len)))
      case LITERALstring  => Constant(readNameRef().toString)
      case LITERALnull    => Constant(null)
      case LITERALclass   => Constant(readTrueTypeRef())
      case LITERALenum =>
        readMaybeExternalSymbolRef() match
          case sym: TermSymbol             => TermRef(NoPrefix, sym)
          case sym: Symbol                 => errorBadSignature(s"unexpected literal enum reference $sym")
          case external: ExternalSymbolRef => external.toTermRef(NoPrefix)
          case _: NoExternalSymbolRef      => errorBadSignature("unexpected literal enum reference with NoSymbol")
      case _ => noSuchConstantTag(tag, len)
    }
  }

  private def noSuchConstantTag(tag: Int, len: Int): Nothing =
    errorBadSignature("bad constant tag: " + tag)

  /** Convert
    *   tp { type name = sym } forSome { sym >: L <: H }
    * to
    *   tp { name >: L <: H }
    * and
    *   tp { name: sym } forSome { sym <: T with Singleton }
    * to
    *   tp { name: T }
    */
  private def elimExistentials(boundSyms: List[TypeMemberSymbol], tp: Type)(using ReaderContext): Type =
    // Need to be careful not to run into cyclic references here (observed when
    // compiling t247.scala). That's why we avoid taking `symbol` of a TypeRef
    // unless names match up.
    def boundSymOf(tp: Type): Option[TypeMemberSymbol] =
      def refersTo(tp: Type, sym: TypeMemberSymbol): Boolean = tp match {
        case tp: TypeRef => tp.isLocalRef(sym)
        /*case tp: TypeVar => refersTo(tp.underlying, sym)
        case tp : LazyRef => refersTo(tp.ref, sym)*/
        case _ => false
      }
      boundSyms.find(refersTo(tp, _))
    end boundSymOf
    // Cannot use standard `existsPart` method because it calls `lookupRefined`
    // which can cause CyclicReference errors.
    /*val isBoundAccumulator = new ExistsAccumulator(isBound, StopAt.Static, forceLazy = true):
      override def foldOver(x: Boolean, tp: Type): Boolean = tp match
        case tp: TypeRef => applyToPrefix(x, tp)
        case _ => super.foldOver(x, tp)*/

    /*def removeSingleton(tp: Type): Type =
      if (tp isRef defn.SingletonClass) defn.AnyType else tp*/
    def mapArg(arg: TypeOrWildcard): TypeOrWildcard = arg match {
      case arg: TypeRef =>
        boundSymOf(arg) match
          case Some(sym) => WildcardTypeArg(sym.declaredBounds)
          case None      => arg
      case _ =>
        arg
    }
    def elim(tp: Type): Type = tp match {
      /*case tp @ RefinedType(parent, name, rinfo) =>
        val parent1 = elim(tp.parent)
        rinfo match {
          case TypeAlias(info: TypeRef) if isBound(info) =>
            RefinedType(parent1, name, info.symbol.info)
          case info: TypeRef if isBound(info) =>
            val info1 = info.symbol.info
            assert(info1.isSubClass(defn.SingletonClass))
            RefinedType(parent1, name, info1.mapReduceAnd(removeSingleton)(_ & _))
          case info =>
            tp.derivedRefinedType(parent1, name, info)
        }*/
      case tp: AppliedType =>
        /*val tycon1 = tycon tycon.safeDealias
        if (tycon1 ne tycon) elim(tycon1.appliedTo(args))
        else*/
        tp.derivedAppliedType(tp.tycon, tp.args.map(mapArg))
      /*case tp: AndOrType =>
        // scalajs.js.|.UnionOps has a type parameter upper-bounded by `_ | _`
        tp.derivedAndOrType(mapArg(tp.tp1).bounds.hi, mapArg(tp.tp2).bounds.hi)*/
      case _ =>
        tp
    }
    val tp1 = elim(tp)
    /*if (isBoundAccumulator(false, tp1)) {
      val anyTypes = boundSyms map (_ => defn.AnyType)
      val boundBounds = boundSyms map (_.info.bounds.hi)
      val tp2 = tp1.subst(boundSyms, boundBounds).subst(boundSyms, anyTypes)
      report.warning(FailureToEliminateExistential(tp, tp1, tp2, boundSyms, classRoot.symbol))
      tp2
    }
    else*/
    tp1
  end elimExistentials
}

private[reader] object PickleReader {

  private val MangledDefaultGetterNameRegex = "^(.+)\\$default\\$([0-9]+)$".r

  def pkl(using pkl: PklStream): pkl.type = pkl
  def index[I <: PickleReader#Index & Singleton](using index: I): index.type = index
  def entries[E <: PickleReader#Entries & Singleton](using entries: E): entries.type = entries

  private val alwaysTrue: Any => Boolean = _ => true

  object PklStream {
    def read[T](bytes: IArray[Byte])(op: PklStream ?=> T): T =
      op(using PklStream(PickleBuffer(bytes, from = 0)))
  }

  final class PklStream private (in: PickleBuffer) {
    export in.readByte
    export in.readNat
    export in.readLong
    export in.readLongNat
    export in.until
    export in.createIndex as readIndex
    export in.readIndex as currentOffset
    export in.bytes

    def readEnd(): Int = readNat() + in.readIndex
    def atOffset(offset: Int): Boolean = in.readIndex == offset

    def readTermName(length: Int): SimpleName =
      termName(UTF8Utils.decode(in.bytes, in.readIndex, length))

    def readTypeName(length: Int): SimpleTypeName =
      typeName(UTF8Utils.decode(in.bytes, in.readIndex, length))

    final inline def unsafeFork[T](offset: Int)(inline op: PklStream ?=> T): T = {
      val saved = in.readIndex
      try {
        in.readIndex = offset
        op(using this)
      } finally in.readIndex = saved
    }

  }

  final class ExternalSymbolRef(owner: MaybeExternalSymbol, name: Name) {
    def toTypeRef(pre: Prefix)(using ReaderContext): TypeRef =
      toNamedType(pre).asInstanceOf[TypeRef]

    def toTermRef(pre: Prefix)(using ReaderContext): TermRef =
      toNamedType(pre).asInstanceOf[TermRef]

    def toNamedType(pre: Prefix)(using ReaderContext): NamedType =
      NamedType(pre, toScala2ExternalSymRef)

    def toScala2ExternalSymRef: Scala2ExternalSymRef =
      owner match
        case owner: Symbol =>
          Scala2ExternalSymRef(owner, name :: Nil)
        case owner: ExternalSymbolRef =>
          val Scala2ExternalSymRef(ownerOwner, ownerPath) = owner.toScala2ExternalSymRef
          Scala2ExternalSymRef(ownerOwner, ownerPath :+ name)
        case _: NoExternalSymbolRef =>
          // This is already caught when builing the ExternalSymbolRef
          throw AssertionError(s"Illegal ExternalSymbolRef(NoSymbol, $name)")
  }

  // This is a final class with a single instance instead of an `object` to behave better within the union type below
  final class NoExternalSymbolRef private ():
    override def toString(): String = "NoSymbol"
  end NoExternalSymbolRef

  object NoExternalSymbolRef:
    val instance = new NoExternalSymbolRef
  end NoExternalSymbolRef

  type MaybeExternalSymbol = Symbol | ExternalSymbolRef | NoExternalSymbolRef

  private val Scala2Constructor: SimpleName = termName("this")
  private val Scala2TraitConstructor: SimpleName = termName("$init$")

  private final class UnsupportedTreeInAnnotationException(message: String) extends Exception(message)

  private[tastyquery] case class TempMethodType(paramSyms: List[TermSymbol], resType: TypeMappable)
      extends CustomTransientGroundType

  private[tastyquery] case class TempPolyType(paramSyms: List[TypeParamSymbol], resType: TypeMappable)
      extends CustomTransientGroundType

  /** Temporary type for classinfos, will be decomposed on completion of the class */
  private[tastyquery] case class TempClassInfoType(parentTypes: List[Type]) extends CustomTransientGroundType

}
