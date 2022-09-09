package tastyquery.reader.pickles

import scala.annotation.switch

import tastyquery.ast.Constants.*
import tastyquery.ast.Flags.*
import tastyquery.ast.Names.{TermName, termName, TypeName, typeName, nme}
import tastyquery.ast.Symbols.{Symbol, NoSymbol}
import tastyquery.ast.Types.*
import tastyquery.Contexts.{ClassContext, clsCtx}

import PickleReader.*
import PickleFormat.*
import tastyquery.ast.Names.Name
import tastyquery.ast.Symbols.RegularSymbolFactory
import tastyquery.ast.Symbols.ClassSymbolFactory
import tastyquery.ast.Symbols.ClassSymbol

import tastyquery.util.syntax.chaining.given
import tastyquery.ast.Symbols.DeclaringSymbol
import tastyquery.ast.Symbols.PackageClassSymbol
import tastyquery.ast.Trees.TypeApply
import tastyquery.Contexts.Context
import tastyquery.ast.Names.SimpleName

class PickleReader {
  opaque type Entries = Array[AnyRef | Null]
  opaque type Index = IArray[Int]

  class Structure(using val myEntries: Entries, val myIndex: Index)

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
      throw java.io.IOException(s"Bad pickles version, expected: $MajorVersion.$MinorVersion, found: $major.$minor")
  }

  def errorBadSignature(msg: String): Nothing =
    throw PickleReader.BadSignature(msg)

  private def at[T <: AnyRef](i: Int)(op: PklStream ?=> T)(using PklStream, Entries, Index): T = {
    val tOpt = entries(i).asInstanceOf[T | Null]
    if tOpt == null then {
      val res = pkl.unsafeFork(index(i))(op)
      assert(entries(i) == null, entries(i))
      entries(i) = res
      res
    } else tOpt
  }

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

  def readLocalSymbolRef()(using ClassContext, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolRef() match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readLocalSymbolAt(i: Int)(using ClassContext, PklStream, Entries, Index): Symbol =
    readMaybeExternalSymbolAt(i) match
      case sym: Symbol => sym
      case external =>
        errorBadSignature(s"expected local symbol reference but found $external")

  def readMaybeExternalSymbolRef()(using ClassContext, PklStream, Entries, Index): MaybeExternalSymbol =
    readMaybeExternalSymbolAt(pkl.readNat())

  def readMaybeExternalSymbolAt(i: Int)(using ClassContext, PklStream, Entries, Index): MaybeExternalSymbol =
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

  def readMaybeExternalSymbol(
    storeInEntriesAt: Int
  )(using ClassContext, PklStream, Entries, Index): MaybeExternalSymbol = {
    // val start = indexCoord(readIndex) // no need yet to record the position of symbols
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    def atEnd(using PklStream) = pkl.atOffset(end)

    def storeResultInEntries(result: MaybeExternalSymbol): Unit =
      assert(entries(storeInEntriesAt) == null, entries(storeInEntriesAt))
      entries(storeInEntriesAt) = result

    def readExtSymbol(): MaybeExternalSymbol =
      val name = readNameRef() // TODO .decode
      val owner = if (atEnd) clsCtx.defn.RootPackage else readMaybeExternalSymbolRef()
      name match
        case nme.RootName | nme.RootPackageName =>
          clsCtx.defn.RootPackage
        case _ =>
          def defaultRef = ExternalSymbolRef(owner, name)
          owner match
            case owner: PackageClassSymbol =>
              name match
                case packageName: SimpleName =>
                  owner.getPackageDecl(packageName).getOrElse {
                    //errorBadSignature(s"cannot find symbol $owner.$name")
                    defaultRef
                  }
                case _ => defaultRef
            case _ =>
              defaultRef

    tag match {
      case NONEsym                 => return NoSymbol
      case EXTref | EXTMODCLASSref => return readExtSymbol()
      case _                       =>
    }

    // symbols that were pickled with Pickler.writeSymInfo
    val nameref = pkl.readNat()
    val name0 = at(nameref)(readName())
    val name1 = name0.decode
    val owner = readLocalSymbolRef()

    val flags = readFlags(name1.isTypeName)
    val name = if flags.is(ModuleClass) then name1.toTermName.withObjectSuffix.toTypeName else name1

    val (privateWithin, infoRef) = {
      val ref = pkl.readNat()
      if (!isSymbolRef(ref)) (NoSymbol, ref)
      else {
        val pw = readLocalSymbolAt(ref)
        (pw, pkl.readNat())
      }
    }

    def nameMatches(rootName: Name) = name == rootName
    def isClassRoot = owner == clsCtx.root.pkg && nameMatches(
      clsCtx.root.rootName.toTypeName
    ) //&& (owner == classRoot.owner) && !flags.is(ModuleClass)
    def isModuleClassRoot = owner == clsCtx.root.pkg && nameMatches(
      clsCtx.root.rootName.withObjectSuffix.toTypeName
    ) //&& (owner == moduleClassRoot.owner) && flags.is(Module)
    def isModuleRoot = owner == clsCtx.root.pkg && nameMatches(
      clsCtx.root.rootName
    ) //&& (owner == moduleClassRoot.owner) && flags.is(Module)

    def enterIntoScope(sym: Symbol): Unit =
      sym.outer match {
        case scope: DeclaringSymbol => scope.addDecl(sym)
        case _                      => ()
      }

    def readSymType(): Type =
      try at(infoRef)(readType())
      catch
        case t: Throwable =>
          throw new IllegalStateException(s"error while unpickling the type of $owner.$name", t)

    val sym = tag match {
      case TYPEsym | ALIASsym =>
        var name1 = name.toTypeName
        val sym = RegularSymbolFactory.createSymbol(name1, owner)
        storeResultInEntries(sym)
        val tpe = readSymType()
        sym.withDeclaredType(tpe)
      case CLASSsym =>
        val cls =
          if isClassRoot then clsCtx.classRoot
          else if isModuleClassRoot then clsCtx.moduleClassRoot
          else
            val sym = ClassSymbolFactory.createSymbol(name.toTypeName, owner)
            if name.toTypeName.wrapsObjectName then
              val module = owner
                .asClass
                .getModuleDeclInternal(name.toTermName.stripObjectSuffix)
              module.foreach(m => m.withDeclaredType(sym.typeRef))
            sym
        assert(!cls.initialised, s"attempting to initialize the class $cls a second time")
        cls.initialised = true
        cls
      case VALsym =>
        val sym = RegularSymbolFactory.createSymbol(name.toTermName, owner)
        storeResultInEntries(sym) // Store the symbol before reading its type, to avoid cycles
        val tpe = readSymType()
        sym.withDeclaredType(tpe)
      case MODULEsym =>
        if isModuleRoot then clsCtx.moduleRoot.withDeclaredType(clsCtx.moduleClassRoot.typeRef)
        else
          val moduleClass = owner
            .asInstanceOf[DeclaringSymbol]
            .getDeclInternal(name.toTermName.withObjectSuffix.toTypeName)
          val sym =
            RegularSymbolFactory.createSymbol(name.toTermName, owner)
          moduleClass.foreach(cls => sym.withDeclaredType(cls.asInstanceOf[ClassSymbol].typeRef))
          sym
      case _ =>
        errorBadSignature("bad symbol tag: " + tag)
    }
    enterIntoScope(sym)
    sym
      .withFlags(flags)
      .withPrivateWithin(privateWithin)
  }

  private def readFlags(isType: Boolean)(using PklStream): FlagSet = {
    val pickleFlags = PickleFlagSet(pkl.readLongNat(), isType)
    var flags: FlagSet = EmptyFlagSet

    if pickleFlags.isProtected then flags |= Protected
    if pickleFlags.isOverride then flags |= Override
    if pickleFlags.isPrivate then flags |= Private
    if pickleFlags.isAbstract then flags |= Abstract
    if pickleFlags.isDeferred then flags |= Deferred
    if pickleFlags.isFinal then flags |= Final
    if pickleFlags.isMethod then flags |= Method
    if pickleFlags.isInterface then flags |= NoInitsInterface
    if pickleFlags.isModule then
      flags |= Module
      if isType then flags |= ModuleClassCreationFlags
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

  def isSymbolRef(i: Int)(using PklStream, Index): Boolean = {
    val tag = pkl.bytes(index(i))
    (firstSymTag <= tag && tag <= lastExtSymTag)
  }

  /** Read type ref, mapping a TypeRef to a package to the package's ThisType
    *  Package references should be TermRefs or ThisTypes but it was observed that
    *  nsc sometimes pickles them as TypeRefs instead.
    */
  private def readPrefix()(using ClassContext, PklStream, Entries, Index): Type = readTypeRef() match {
    //case pre: TypeRef if pre.symbol.is(Package) => pre.symbol.thisType
    case pre => pre
  }

  private def readTypeRef()(using ClassContext, PklStream, Entries, Index): Type =
    at(pkl.readNat())(readType())

  /** Read a type
    *
    *  @param forceProperType is used to ease the transition to NullaryMethodTypes (commentmarker: NMT_TRANSITION)
    *        the flag say that a type of kind * is expected, so that PolyType(tps, restpe) can be disambiguated to PolyType(tps, NullaryMethodType(restpe))
    *        (if restpe is not a ClassInfoType, a MethodType or a NullaryMethodType, which leaves TypeRef/SingletonType -- the latter would make the polytype a type constructor)
    */
  private def readType()(using ClassContext, PklStream, Entries, Index): Type = {
    def select(pre: Type, sym: Symbol): Type =
      // structural members need to be selected by name, their symbols are only
      // valid in the synthetic refinement class that defines them.
      /*TODO if !pre.isInstanceOf[ThisType] && isRefinementClass(sym.owner) then pre.select(sym.name)
      else*/ pre.select(sym)

    val tag = pkl.readByte()
    val end = pkl.readEnd()
    (tag: @switch) match {
      case NOtpe =>
        NoType
      case NOPREFIXtpe =>
        NoPrefix
      case THIStpe =>
        readMaybeExternalSymbolRef() match
          case sym: Symbol =>
            sym.asClass.accessibleThisType
          case external: ExternalSymbolRef =>
            external.toNamedType(NoPrefix) match
              case termRef: TermRef => termRef // necessary for package refs?
              case typeRef: TypeRef => ThisType(typeRef)
      case SINGLEtpe =>
        val pre = readPrefix()
        val designator = readMaybeExternalSymbolRef()
        designator match
          case sym: Symbol                 => NamedType(pre, sym)
          case external: ExternalSymbolRef => external.toNamedType(pre)
      /*case SUPERtpe =>
        val thistpe = readTypeRef()
        val supertpe = readTypeRef()
        SuperType(thistpe, supertpe)*/
      case CONSTANTtpe =>
        readConstantRef() match
          case c: Constant => ConstantType(c)
          case tp: TermRef => tp
      case TYPEREFtpe =>
        var pre = readPrefix()
        val designator = readMaybeExternalSymbolRef()
        /*pre match {
          case thispre: ThisType =>
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
            }
          case NoPrefix if sym.is(TypeParam) =>
            pre = sym.owner.thisType
          case _ =>
        }*/
        //val tycon = select(pre, sym)
        val tycon = designator match
          case sym: Symbol                 => select(pre, sym)
          case external: ExternalSymbolRef => external.toTypeRef(pre)
        val args = pkl.until(end, () => readTypeRef())
        /*if (sym == defn.ByNameParamClass2x) ExprType(args.head)
        else if (ctx.settings.scalajs.value && args.length == 2 &&
            sym.owner == JSDefinitions.jsdefn.ScalaJSJSPackageClass && sym == JSDefinitions.jsdefn.PseudoUnionClass) {
          // Treat Scala.js pseudo-unions as real unions, this requires a
          // special-case in erasure, see TypeErasure#eraseInfo.
          OrType(args(0), args(1))
        }
        else if (args.nonEmpty) tycon.safeAppliedTo(EtaExpandIfHK(sym.typeParams, args.map(translateTempPoly)))
        else if (sym.typeParams.nonEmpty) tycon.EtaExpand(sym.typeParams)
        else tycon*/
        if args.isEmpty then tycon
        else AppliedType(tycon, args)
      case TYPEBOUNDStpe =>
        val lo = readTypeRef()
        val hi = readTypeRef()
        // TODO? createNullableTypeBounds(lo, hi)
        WildcardTypeBounds(RealTypeBounds(lo, hi))
      case REFINEDtpe =>
        /*val clazz = readSymbolRef().asClass
        val decls = symScope(clazz)
        symScopes(clazz) = EmptyScope // prevent further additions
        val parents = pkl.until(end, () => readTypeRef())
        val parent = parents.reduceLeft(AndType(_, _))
        if (decls.isEmpty) parent
        else {
          def subst(info: Type, rt: RecType) = info.substThis(clazz.asClass, rt.recThis)
          def addRefinement(tp: Type, sym: Symbol) = RefinedType(tp, sym.name, sym.info)
          val refined = decls.toList.foldLeft(parent)(addRefinement)
          RecType.closeOver(rt => refined.substThis(clazz, rt.recThis))
        }*/
        AnyType
      /*case CLASSINFOtpe =>
        val clazz = readLocalSymbolRef()
        TempClassInfoType(pkl.until(end, () => readTypeRef()), symScope(clazz), clazz)*/
      case METHODtpe | IMPLICITMETHODtpe =>
        val restpe = readTypeRef()
        val params = pkl.until(end, () => readLocalSymbolRef())
        val result = MethodType(params.map(_.name.toTermName), params.map(_.declaredType), restpe)
        /*val maker = MethodType.companion(
          isImplicit = tag == IMPLICITMETHODtpe || params.nonEmpty && params.head.is(Implicit))
        val result = maker.fromSymbols(params, restpe)
        result.resType match
          case restpe1: MethodType if restpe1 ne restpe =>
            val prevResParams = paramsOfMethodType.remove(restpe)
            if prevResParams != null then
              paramsOfMethodType.put(restpe1, prevResParams)
          case _ =>
        if params.nonEmpty then paramsOfMethodType.put(result, params)*/
        result
      case POLYtpe =>
        val restpe = readTypeRef()
        val typeParams = pkl.until(end, () => readLocalSymbolRef())
        if typeParams.nonEmpty then
          //TempPolyType(typeParams.asInstanceOf[List[TypeSymbol]], restpe.widenExpr)
          PolyType(typeParams.map(_.name.toTypeName), typeParams.map(_ => UnconstrainedTypeBounds), restpe)
        else ExprType(restpe)
      case EXISTENTIALtpe =>
        /*val restpe = readTypeRef()
        val boundSyms = pkl.until(end, () => readLocalSymbolRef())
        elimExistentials(boundSyms, restpe)*/
        AnyType
      case ANNOTATEDtpe =>
        // TODO AnnotatedType.make(readTypeRef(), pkl.until(end, () => readAnnotationRef()))
        val underlying = readTypeRef()
        // ignore until `end` (annotations)
        underlying
      case _ =>
        noSuchTypeTag(tag, end)
    }
  }

  private def readTypeParams()(using ClassContext, PklStream, Entries, Index): List[Symbol] = {
    val tag = pkl.readByte()
    val end = pkl.readEnd()
    if (tag == POLYtpe) {
      val unusedRestperef = pkl.readNat()
      pkl.until(end, () => readLocalSymbolRef())
    } else Nil
  }

  private def noSuchTypeTag(tag: Int, end: Int): Nothing =
    errorBadSignature("bad type tag: " + tag)

  private def readConstantRef()(using ClassContext, PklStream, Entries, Index): Constant | TermRef =
    at(pkl.readNat())(readConstant())

  /** Read a constant */
  private def readConstant()(using ClassContext, PklStream, Entries, Index): Constant | TermRef = {
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
          case sym: Symbol                 => TermRef(NoPrefix, sym)
          case external: ExternalSymbolRef => external.toTermRef(NoPrefix)
      case _ => noSuchConstantTag(tag, len)
    }
  }

  private def noSuchConstantTag(tag: Int, len: Int): Nothing =
    errorBadSignature("bad constant tag: " + tag)
}

object PickleReader {

  def pkl(using pkl: PklStream): pkl.type = pkl
  def index[I <: PickleReader#Index & Singleton](using index: I): index.type = index
  def entries[E <: PickleReader#Entries & Singleton](using entries: E): entries.type = entries

  private val alwaysTrue: Any => Boolean = _ => true

  final class BadSignature(message: String) extends Exception(message)

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
      termName(in.bytes, in.readIndex, length)

    def readTypeName(length: Int): TypeName =
      typeName(in.bytes, in.readIndex, length)

    final inline def unsafeFork[T](offset: Int)(inline op: PklStream ?=> T): T = {
      val saved = in.readIndex
      try {
        in.readIndex = offset
        op(using this)
      } finally in.readIndex = saved
    }

  }

  final class ExternalSymbolRef(owner: MaybeExternalSymbol, name: Name) {
    def toTypeRef(pre: Type)(using Context): TypeRef =
      toNamedType(pre).asInstanceOf[TypeRef]

    def toTermRef(pre: Type)(using Context): TermRef =
      toNamedType(pre).asInstanceOf[TermRef]

    def toNamedType(pre: Type)(using Context): NamedType =
      NamedType(pre, toScala2ExternalSymRef)

    private def toScala2ExternalSymRef: Scala2ExternalSymRef =
      owner match
        case owner: Symbol =>
          Scala2ExternalSymRef(owner, name :: Nil)
        case owner: ExternalSymbolRef =>
          val Scala2ExternalSymRef(ownerOwner, ownerPath) = owner.toScala2ExternalSymRef
          Scala2ExternalSymRef(ownerOwner, ownerPath :+ name)
  }

  type MaybeExternalSymbol = Symbol | ExternalSymbolRef

}
