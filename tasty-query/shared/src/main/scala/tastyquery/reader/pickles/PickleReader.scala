package tastyquery.reader.pickles

import scala.annotation.switch
import scala.collection.mutable

import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.Names.*
import tastyquery.Substituters
import tastyquery.Symbols.*
import tastyquery.Types.*

import tastyquery.reader.UTF8Utils

import PickleReader.*
import PickleFormat.*

private[pickles] class PickleReader {
  opaque type Entries = Array[AnyRef | Null]
  opaque type Index = IArray[Int]

  final class Structure(using val myEntries: Entries, val myIndex: Index):
    def allRegisteredSymbols: Iterator[Symbol] =
      myEntries.iterator.collect { case sym: Symbol =>
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
        assert((existingEntry eq res) || res.isInstanceOf[Type], s"$res != $existingEntry")
        existingEntry
    } else tOpt.asInstanceOf[T] // temp hack for expression evaluator
  }

  private def atNoCache[T <: AnyRef](i: Int)(op: PklStream ?=> T)(using PklStream, Entries, Index): T =
    pkl.unsafeFork(index(i))(op)

  def readNameRef()(using PklStream, Entries, Index): Name = at(pkl.readNat())(readName())

  def readName()(using PklStream): Name = {
    val tag = pkl.readByte()
    val len = pkl.readNat()
    tag match {
      case TERMname => pkl.readTermName(len)
      case TYPEname => pkl.readTypeName(len)
      case _        => errorBadSignature("bad name tag: " + tag)
    }
  }

  def readLocalSymbolRef()(using Context, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolRef() match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readLocalSymbolAt(i: Int)(using Context, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolAt(i) match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readMaybeExternalSymbolRef()(using Context, PklStream, Entries, Index): MaybeExternalSymbol =
    readMaybeExternalSymbolAt(pkl.readNat())

  def ensureReadAllLocalDeclsOfRefinement(ownerIndex: Int)(using Context, PklStream, Entries, Index): Unit =
    index.loopWithIndices { (offset, i) =>
      val idx = index(i)
      val tag = pkl.bytes(idx).toInt
      if tag >= firstSymTag && tag <= lastSymTag then
        val include = pkl.unsafeFork(idx) {
          pkl.readByte() // tag
          pkl.readNat() // length
          pkl.readNat() // name
          val ownerRef = pkl.readNat()
          ownerRef == ownerIndex
        }
        if include then readLocalSymbolAt(i).asInstanceOf[TermOrTypeSymbol]
    }
  end ensureReadAllLocalDeclsOfRefinement

  def readMaybeExternalSymbolAt(i: Int)(using Context, PklStream, Entries, Index): MaybeExternalSymbol =
    // Similar to at(), but sometimes readMaybeExternalSymbol stores the result itself in entries
    val tOpt = entries(i).asInstanceOf[MaybeExternalSymbol | Null]
    if tOpt == null then {
      val res = pkl.unsafeFork(index(i)) {
        readMaybeExternalSymbol(i)
      }
      val existingEntry = entries(i)
      if existingEntry == null then entries(i) = res
      else assert(res eq existingEntry, s"$res <-> $existingEntry}")
      res
    } else tOpt

  def readMaybeExternalSymbol(storeInEntriesAt: Int)(using Context, PklStream, Entries, Index): MaybeExternalSymbol = {
    // val start = indexCoord(readIndex) // no need yet to record the position of symbols
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    def atEnd(using PklStream) = pkl.atOffset(end)

    def storeResultInEntries(result: MaybeExternalSymbol): Unit =
      assert(entries(storeInEntriesAt) == null, entries(storeInEntriesAt))
      entries(storeInEntriesAt) = result

    def readExtSymbol(): MaybeExternalSymbol =
      val name = readNameRef().decode
      val owner = if (atEnd) ctx.defn.RootPackage else readMaybeExternalSymbolRef()
      name match
        case nme.RootName | nme.RootPackageName =>
          ctx.defn.RootPackage
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
    val nameref = pkl.readNat()
    val name0 = at(nameref)(readName())

    val name1 = name0.decode match
      case SimpleName(MangledDefaultGetterNameRegex(underlyingStr, indexStr)) =>
        DefaultGetterName(termName(underlyingStr), indexStr.toInt - 1)
      case decoded =>
        decoded

    assert(entries(storeInEntriesAt) == null, entries(storeInEntriesAt))
    val owner = readMaybeExternalSymbolRef() match
      case sym: Symbol =>
        sym
      case noRef: NoExternalSymbolRef if tag == TYPEsym =>
        /* For some reason, Scala 2 pickles `TYPEsym` symbols whose owner references `NONEsym`.
         * However, they do not appear to be referenced *themselves* from anywhere. They
         * only appear in the table, and hence get read from the loop in `Unpickler.run`.
         * We ignore these entries here by replacing them with `NONEsym`. If they end up
         * being actually referenced somewhere, then that somewhere will then crash with
         * an unexpected reference to `NONEsym`, which would provide us with more context
         * to perhaps solve this at a deeper level.
         * If someone wants to investigate, there is a case of this in `scala.collection.Iterator`.
         */
        return NoExternalSymbolRef.instance
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

    if name1 == nme.m_getClass && owner.owner == defn.scalaPackage && HasProblematicGetClass.contains(owner.name) then
      return NoExternalSymbolRef.instance

    /* In some situations, notably involving EXISTENTIALtpe, reading the
     * reference to the owner may re-try to read this very symbol. In that
     * case, the entries(storeInEntriesAt) will have been filled while reading
     * the owner, and we must immediately return what was already stored.
     */
    val storedWhileReadingOwner = entries(storeInEntriesAt)
    if storedWhileReadingOwner != null then return storedWhileReadingOwner.asInstanceOf[MaybeExternalSymbol]

    val pickleFlags = readPickleFlags(name1.isTypeName)
    val flags = pickleFlagsToFlags(pickleFlags)
    val name =
      if pickleFlags.isType && flags.is(Module) then name1.toTermName.withObjectSuffix.toTypeName
      else if flags.is(Method) && (name1 == Scala2Constructor || name1 == Scala2TraitConstructor) then nme.Constructor
      else name1

    val (privateWithin, infoRef) = {
      val ref = pkl.readNat()
      if (!isSymbolRef(ref)) (None, ref)
      else {
        val pw = readLocalSymbolAt(ref)
        (Some(pw), pkl.readNat())
      }
    }

    def readSymType(): Type =
      try at(infoRef)(readType())
      catch
        case t: Throwable =>
          throw new Scala2PickleFormatException(s"error while unpickling the type of $owner.$name", t)

    val sym: Symbol = tag match {
      case TYPEsym | ALIASsym =>
        var name1 = name.toTypeName
        val sym: TypeSymbolWithBounds =
          if pickleFlags.isParam then
            if owner.isClass then ClassTypeParamSymbol.create(name1, owner.asClass)
            else LocalTypeParamSymbol.create(name1, owner)
          else TypeMemberSymbol.create(name1, owner)
        storeResultInEntries(sym)
        val tpe = readSymType()
        val bounds = translateTempPolyForTypeMember(tpe)
        sym match
          case sym: TypeMemberSymbol =>
            sym.withDefinition(bounds match
              case bounds: RealTypeBounds => TypeMemberDefinition.AbstractType(bounds)
              case TypeAlias(alias)       => TypeMemberDefinition.TypeAlias(alias)
            )
          case sym: TypeParamSymbol =>
            sym.setBounds(bounds)
        sym
      case CLASSsym =>
        val tname = name.toTypeName
        val cls =
          if tname == tpnme.RefinedClassMagic then ClassSymbol.createRefinedClassSymbol(owner, Scala2Defined)
          else if tname == tpnme.scala2LocalChild then ClassSymbol.createNotDeclaration(tname, owner)
          else ClassSymbol.create(tname, owner)
        storeResultInEntries(cls)
        val tpe = readSymType()
        val typeParams = atNoCache(infoRef)(readTypeParams())
        if isRefinementClass(cls) then return cls // by-pass further assignments, including Flags
        cls.withTypeParams(typeParams)
        val scala2ParentTypes = tpe match
          case TempPolyType(tparams, restpe: TempClassInfoType) =>
            assert(tparams.corresponds(typeParams)(_ eq _)) // should reuse the class type params
            restpe.parentTypes
          case tpe: TempClassInfoType => tpe.parentTypes
          case tpe =>
            throw AssertionError(s"unexpected type $tpe for $cls, owner is $owner")
        val parentTypes =
          if cls.owner == defn.scalaPackage && tname == tpnme.AnyVal then
            // Patch the superclasses of AnyVal to contain Matchable
            scala2ParentTypes :+ defn.MatchableType
          else if cls.owner == defn.scalaPackage && isTupleClassName(tname) && defn.hasGenericTuples then
            // Patch the superclass of TupleN classes to inherit from *:
            defn.GenericTupleTypeOf(typeParams.map(_.typeRef)) :: scala2ParentTypes.tail
          else scala2ParentTypes
        val givenSelfType = if atEnd then None else Some(readTypeRef())
        cls.withParentsDirect(parentTypes)
        cls.withGivenSelfType(givenSelfType)
        cls
      case VALsym =>
        // Discard `$extension` methods, as they should not be seen from a Scala 3 point of view
        val forceNotDeclaration = name1 match
          case SimpleName(str) => flags.is(Method) && str.endsWith("$extension")
          case _               => false
        val sym =
          if forceNotDeclaration then TermSymbol.createNotDeclaration(name.toTermName, owner)
          else TermSymbol.create(name.toTermName, owner)
        storeResultInEntries(sym) // Store the symbol before reading its type, to avoid cycles
        val tpe = readSymType()
        val unwrappedTpe = translateTempPolyForMethod(tpe)
        val ctorPatchedTpe =
          if flags.is(Method) && name == nme.Constructor then patchConstructorType(sym.owner.asClass, unwrappedTpe)
          else unwrappedTpe
        sym.withDeclaredType(ctorPatchedTpe)
      case MODULEsym =>
        val sym = TermSymbol.create(name.toTermName, owner)
        storeResultInEntries(sym)
        val ownerPrefix = owner.asInstanceOf[DeclaringSymbol] match
          case owner: PackageSymbol => owner.packageRef
          case owner: ClassSymbol   => owner.thisType
        sym.withDeclaredType(TypeRef(ownerPrefix, sym.name.withObjectSuffix.toTypeName))
        sym
      case _ =>
        errorBadSignature("bad symbol tag: " + tag)
    }
    sym.withFlags(flags, privateWithin)
    sym.setAnnotations(Nil) // TODO Read Scala 2 annotations
    sym
  }

  private def patchConstructorType(cls: ClassSymbol, tpe: Type)(using Context): Type =
    def resultToUnit(tpe: Type): Type =
      tpe match
        case tpe: PolyType =>
          tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypeBounds, resultToUnit(tpe.resultType))
        case tpe: MethodType =>
          tpe.derivedLambdaType(tpe.paramNames, tpe.paramTypes, resultToUnit(tpe.resultType))
        case _ =>
          defn.UnitType

    val tpe1 = resultToUnit(tpe)

    val typeParams = cls.typeParams
    if typeParams.isEmpty then tpe1
    else
      /* Make a PolyType with the same type parameters as the class, and
       * subsitute references to them of the form `C.this.T` by the
       * corresponding `paramRefs` of the `PolyType`.
       */
      PolyType(typeParams.map(_.name))(
        pt => typeParams.map(p => Substituters.substLocalThisClassTypeParams(p.bounds, typeParams, pt.paramRefs)),
        pt => Substituters.substLocalThisClassTypeParams(tpe1, typeParams, pt.paramRefs)
      )
  end patchConstructorType

  def readChildren()(using Context, PklStream, Entries, Index): Unit =
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
    // if pickleFlags.hasDefault then flags |= HasDefault
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

  def addEntry[A <: AnyRef](index: Int, ref: A)(using Entries): Unit =
    entries(index) = ref

  def isSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean = {
    val tag = pkl.bytes(index(i)).toInt
    (firstSymTag <= tag && tag <= lastSymTag &&
    (tag != CLASSsym || !isRefinementSymbolEntry(i)))
  }

  def isRefinementSymbolEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    pkl.unsafeFork(index(i)) {
      val tag = pkl.readByte().toInt
      assert(tag == CLASSsym)
      pkl.readNat() // read length
      val result = readNameRef() == nme.RefinementClass
      result
    }

  def isChildrenEntry(i: Int)(using PklStream, Entries, Index): Boolean =
    val tag = pkl.bytes(index(i))
    tag == CHILDREN

  protected def isRefinementClass(sym: Symbol)(using Context): Boolean =
    sym.name == tpnme.RefinedClassMagic

  def isSymbolRef(i: Int)(using PklStream, Index): Boolean = {
    val tag = pkl.bytes(index(i))
    (firstSymTag <= tag && tag <= lastExtSymTag)
  }

  /** Read type ref, mapping a TypeRef to a package to the package's ThisType
    *  Package references should be TermRefs or ThisTypes but it was observed that
    *  nsc sometimes pickles them as TypeRefs instead.
    */
  private def readPrefixRef()(using Context, PklStream, Entries, Index): Prefix =
    at(pkl.readNat())(readTypeOrPrefix()) match
      //case pre: TypeRef if pre.symbol.is(Package) => pre.symbol.thisType
      case pre => pre
  end readPrefixRef

  private def readTypeRef()(using Context, PklStream, Entries, Index): Type =
    at(pkl.readNat())(readType())

  /** Read a type
    *
    *  @param forceProperType is used to ease the transition to NullaryMethodTypes (commentmarker: NMT_TRANSITION)
    *        the flag say that a type of kind * is expected, so that PolyType(tps, restpe) can be disambiguated to PolyType(tps, NullaryMethodType(restpe))
    *        (if restpe is not a ClassInfoType, a MethodType or a NullaryMethodType, which leaves TypeRef/SingletonType -- the latter would make the polytype a type constructor)
    */
  private def readType()(using Context, PklStream, Entries, Index): Type =
    readTypeOrPrefix() match
      case tpe: Type => tpe
      case NoPrefix  => errorBadSignature("unexpected NoPrefix")

  private def readTypeOrPrefix()(using Context, PklStream, Entries, Index): Prefix = {
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
        TypeRef(defn.scalaPackage.packageRef, typeName("<notype>"))
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
        val thistpe = readTypeRef() match
          case thistpe: ThisType => thistpe
          case thistpe           => throw Scala2PickleFormatException(s"Unexpected this type for SuperType: $thistpe")
        val supertpe = readTypeRef()
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
        val args = pkl.until(end, () => readTypeRef())
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
        def isByNameParamClass(tpe: Type): Boolean = tpe match
          case tpe: TypeRef if tpe.name == tpnme.scala2ByName =>
            tpe.prefix match
              case prefix: PackageRef => prefix.symbol == defn.scalaPackage
              case _                  => false
          case _ =>
            false
        end isByNameParamClass
        if args.isEmpty then tycon
        else if isByNameParamClass(tycon) then ByNameType(args.head)
        else AppliedType(tycon, args.map(translateTempPolyForTypeArg(_)))
      case TYPEBOUNDStpe =>
        val lo = readTypeRef()
        val hi = readTypeRef()
        // TODO? createNullableTypeBounds(lo, hi)
        WildcardTypeBounds(RealTypeBounds(lo, hi))
      case REFINEDtpe =>
        val clazzIndex = pkl.readNat()
        val clazz = readLocalSymbolAt(clazzIndex).asClass
        val parents = pkl.until(end, () => readTypeRef())
        val parent = parents.reduceLeft(AndType(_, _))
        ensureReadAllLocalDeclsOfRefinement(clazzIndex)
        val decls = clazz.declarations
        if decls.isEmpty then parent
        else
          val refined = decls.toList.foldLeft(parent) { (parent, sym) =>
            sym match
              case sym: TypeMemberSymbol =>
                TypeRefinement(parent, sym.name, sym.bounds)
              case sym: TermSymbol =>
                TermRefinement(parent, !sym.isAnyOf(Method | Mutable), sym.name, sym.declaredType)
              case _: TypeParamSymbol | _: ClassSymbol =>
                errorBadSignature(s"invalid symbol in refinement class: $sym of type ${sym.getClass()}")
          }
          RecType.fromRefinedClassDecls(refined, clazz)
      case CLASSINFOtpe =>
        val clazz = readLocalSymbolRef()
        TempClassInfoType(pkl.until(end, () => readTypeRef()))
      case METHODtpe | IMPLICITMETHODtpe =>
        val restpe = readTypeRef()
        val params = pkl.until(end, () => readLocalSymbolRef().asTerm)
        val maker = MethodType
        /*val maker = MethodType.companion(
          isImplicit = tag == IMPLICITMETHODtpe || params.nonEmpty && params.head.is(Implicit))*/
        val result = maker.fromSymbols(params, restpe)
        // result.resType match
        //   case restpe1: MethodType if restpe1 ne restpe =>
        //     val prevResParams = caches.paramsOfMethodType.remove(restpe)
        //     if prevResParams != null then
        //       caches.paramsOfMethodType.put(restpe1, prevResParams)
        //   case _ =>
        // if params.nonEmpty then caches.paramsOfMethodType.put(result, params)
        result
      case POLYtpe =>
        // create PolyType
        //   - PT => register at index
        val restpe = readTypeRef()
        val typeParams = pkl.until(end, () => readLocalSymbolRef().asInstanceOf[TypeParamSymbol])
        if typeParams.nonEmpty then TempPolyType(typeParams, restpe)
        else restpe
      case EXISTENTIALtpe =>
        val restpe = readTypeRef()
        // TODO Should these be LocalTypeParamSymbols?
        val boundSyms = pkl.until(end, () => readLocalSymbolRef().asInstanceOf[TypeMemberSymbol])
        elimExistentials(boundSyms, restpe)
      case ANNOTATEDtpe =>
        // TODO AnnotatedType.make(readTypeRef(), pkl.until(end, () => readAnnotationRef()))
        val underlying = readTypeRef()
        // ignore until `end` (annotations)
        underlying
      case _ =>
        noSuchTypeTag(tag, end)
    }
  }

  private def readTypeParams()(using Context, PklStream, Entries, Index): List[ClassTypeParamSymbol] = {
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    if (tag == POLYtpe) {
      val unusedRestperef = pkl.readNat()
      pkl.until(end, () => readLocalSymbolRef().asInstanceOf[ClassTypeParamSymbol])
    } else Nil
  }

  /** Convert temp poly type to TypeLambda and leave other types alone. */
  private def translateTempPolyForTypeArg(tp: Type)(using Context): Type =
    translateTempPolyForTypeMember(tp) match
      case TypeAlias(alias)       => alias
      case bounds: RealTypeBounds => WildcardTypeBounds(bounds)
  end translateTempPolyForTypeArg

  /** Convert temp poly type to TypeLambda and leave other types alone. */
  private def translateTempPolyForTypeMember(tp: Type)(using Context): TypeBounds = tp match
    case tp: WildcardTypeBounds =>
      def rec(bound: Type): Type =
        translateTempPolyForTypeMember(bound).asInstanceOf[TypeAlias].alias
      RealTypeBounds(rec(tp.bounds.low), rec(tp.bounds.high))

    case TempPolyType(tparams, restpe) =>
      val localTParams = tparams.asInstanceOf[List[LocalTypeParamSymbol]] // no class type params in type lambdas
      restpe match
        case restpe: WildcardTypeBounds =>
          val low =
            if restpe.bounds.low.isExactlyNothing then restpe.bounds.low
            else TypeLambda.fromParams(localTParams, restpe.bounds.low)
          val high = TypeLambda.fromParams(localTParams, restpe.bounds.high)
          RealTypeBounds(low, high)
        case restpe: Type =>
          val alias = TypeLambda.fromParams(localTParams, restpe)
          TypeAlias(alias)

    case tp: Type =>
      TypeAlias(tp)
  end translateTempPolyForTypeMember

  /** Convert temp poly type to PolyType and leave other types alone. */
  private def translateTempPolyForMethod(tp: Type)(using Context): Type = tp match
    case TempPolyType(tparams, restpe) =>
      val localTParams = tparams.asInstanceOf[List[LocalTypeParamSymbol]] // no class type params in methods
      PolyType.fromParams(localTParams, restpe)

    case tp =>
      tp
  end translateTempPolyForMethod

  private def noSuchTypeTag(tag: Int, end: Int): Nothing =
    errorBadSignature("bad type tag: " + tag)

  private def readConstantRef()(using Context, PklStream, Entries, Index): Constant | TermRef =
    at(pkl.readNat())(readConstant())

  /** Read a constant */
  private def readConstant()(using Context, PklStream, Entries, Index): Constant | TermRef = {
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
      case LITERALclass   => Constant(readTypeRef())
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
  private def elimExistentials(boundSyms: List[TypeMemberSymbol], tp: Type)(using Context): Type =
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
    def mapArg(arg: Type) = arg match {
      case arg: TypeRef =>
        boundSymOf(arg) match
          case Some(sym) => WildcardTypeBounds(sym.bounds)
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

    def readTermName(length: Int): TermName =
      termName(UTF8Utils.decode(in.bytes, in.readIndex, length))

    def readTypeName(length: Int): TypeName =
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
    def toTypeRef(pre: Prefix)(using Context): TypeRef =
      toNamedType(pre).asInstanceOf[TypeRef]

    def toTermRef(pre: Prefix)(using Context): TermRef =
      toNamedType(pre).asInstanceOf[TermRef]

    def toNamedType(pre: Prefix)(using Context): NamedType =
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
  final class NoExternalSymbolRef private ()
  object NoExternalSymbolRef:
    val instance = new NoExternalSymbolRef
  end NoExternalSymbolRef

  type MaybeExternalSymbol = Symbol | ExternalSymbolRef | NoExternalSymbolRef

  private val Scala2Constructor: SimpleName = termName("this")
  private val Scala2TraitConstructor: SimpleName = termName("$init$")

  private[tastyquery] case class TempPolyType(paramSyms: List[TypeParamSymbol], resType: Type)
      extends CustomTransientGroundType

  /** Temporary type for classinfos, will be decomposed on completion of the class */
  private[tastyquery] case class TempClassInfoType(parentTypes: List[Type]) extends CustomTransientGroundType

  private def isTupleClassName(name: TypeName): Boolean =
    name.toTermName match
      case SimpleName(str) =>
        str.startsWith("Tuple")
          && str.length() > 5
          && str.iterator.drop(5).forall(c => c >= '0' && c <= '9')
      case _ =>
        false
  end isTupleClassName

  private val HasProblematicGetClass: Set[Name] = Set(
    tpnme.Unit,
    tpnme.Boolean,
    tpnme.Char,
    tpnme.Byte,
    tpnme.Short,
    tpnme.Int,
    tpnme.Long,
    tpnme.Float,
    tpnme.Double
  )

}
