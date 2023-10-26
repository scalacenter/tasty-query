package tastyquery.reader.classfiles

import scala.annotation.switch

import tastyquery.Classpaths.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Flags.*
import tastyquery.Types.*

import tastyquery.reader.pickles.ByteCodecs

import ClassfileReader.*
import ClassfileReader.Access.*
import Constants.*

private[classfiles] final class ClassfileReader private () {

  def acceptHeader(classOwner: DeclaringSymbol, classRoot: ClassData)(using DataStream): Unit = {
    acceptMagicNumber(classOwner, classRoot)
    acceptVersion(classOwner, classRoot)
  }

  private def rootName(classOwner: DeclaringSymbol, classRoot: ClassData): String =
    s"${classOwner.displayFullName}.${classRoot.binaryName}"

  private def acceptMagicNumber(classOwner: DeclaringSymbol, classRoot: ClassData)(using DataStream): Unit = {
    val magic = data.readU4()
    if magic != JavaMagicNumber then
      val root = rootName(classOwner, classRoot)
      throw ClassfileFormatException(
        s"Invalid magic number ${magic.toHexString}, should be ${JavaMagicNumber.toHexString} in $root"
      )
  }

  private def acceptVersion(classOwner: DeclaringSymbol, classRoot: ClassData)(using DataStream): Unit = {
    val minor = data.readU2()
    val major = data.readU2()
    if (major < JavaMajorVersion)
      || (major == JavaMajorVersion && minor < JavaMinorVersion)
    then
      val root = rootName(classOwner, classRoot)
      throw ClassfileFormatException(
        s"Invalid class file version $major.$minor, should be at least $JavaMajorVersion.$JavaMinorVersion in $root"
      )
  }

  def readConstantPool()(using ds: DataStream): ConstantPool = {
    val count = data.readU2()
    val pool = ConstantPool(count)
    var doAdd = true
    while doAdd do doAdd = pool.add(acceptConstantInfo()(using ds, pool))
    pool
  }

  class ConstantPool(count: Int) { pool =>
    import ClassfileReader.Indexing

    private val infos = Array.ofDim[ConstantInfo[this.type]](count)
    private var index = 1

    private var seensigbytes = false

    type Idx = Indexing.Index[this.type]

    def cls(idx: Idx): ConstantInfo.Class[this.type] = infos(idx).asInstanceOf[ConstantInfo.Class[this.type]]

    def utf8(idx: Idx): SimpleName = this.apply(idx) match {
      case ConstantInfo.Utf8(name: SimpleName) => name
      case ConstantInfo.Utf8(forked: Forked[DataStream]) =>
        val name = termName(forked.use(data.readUTF8()))
        infos(idx) = ConstantInfo.Utf8(name)
        name
      case _ =>
        throw ClassfileFormatException(s"Expected UTF8 at index $idx")
    }

    def sigbytes(idx: Idx): IArray[Byte] =
      decodeSigBytes(encodedSigbytes(idx))

    def sigbytes(idxs: IArray[Idx]): IArray[Byte] =
      decodeSigBytes(idxs.flatMap(encodedSigbytes))

    private def encodedSigbytes(idx: Idx): IArray[Byte] = this.apply(idx) match {
      case ConstantInfo.Utf8(forked: Forked[DataStream]) =>
        forked.use(data.readSlice(data.readU2()))
      case _ =>
        throw ClassfileFormatException(s"Expected unforced UTF8 constant at index $idx")
    }

    /** Returns a new IArray with the decoded bytes. */
    private def decodeSigBytes(bytes: IArray[Byte]): IArray[Byte] =
      val buffer = Array.from(bytes)
      val decodedLength = ByteCodecs.decode(buffer)
      IArray.unsafeFromArray(buffer).take(decodedLength)

    private[ClassfileReader] def idx(i: Int): Idx = Indexing.idx(this, i)

    private[ClassfileReader] def add(info: ConstantInfo[this.type]): Boolean = {
      infos(index) = info
      def debug() = {
        // TODO read constant pool info lazily?
        def forced = force(idx(index))
        def doprint = println(s"pool $index: $forced")
        infos(index) match {
          case ConstantInfo.Utf8(_) if !seensigbytes && index > 3 =>
            (force(idx(index - 2)), force(idx(index - 1))) match {
              case (
                    ConstantInfo.Utf8(annot.ScalaLongSignature | annot.ScalaSignature),
                    ConstantInfo.Utf8(SimpleName("bytes"))
                  ) =>
                seensigbytes = true
                println(s"pool $index: Utf8/<ScalaSignatureBytes>")
              case _ => doprint
            }
          case _ => doprint
        }
      }
      //debug()
      val jump = info match {
        case ConstantInfo.Long(_) | ConstantInfo.Double(_) => 2
        case _                                             => 1
      }
      index += jump
      index < count
    }

    def apply(index: Idx): ConstantInfo[this.type] = {
      if (index < 1 || index >= infos.length)
        throw ClassfileFormatException(s"Invalid constant pool index $index")
      infos(index)
    }

    def force(index: Idx): ConstantInfo[this.type] =
      this.apply(index) match {
        case ConstantInfo.Utf8(_) =>
          this.utf8(index) // force name
          infos(index)
        case info => info
      }
  }

  def readAccessFlags()(using DataStream): AccessFlags =
    AccessFlags.read(data.readU2())

  def readThisClass()(using ds: DataStream, pool: ConstantPool): ConstantInfo.Class[pool.type] =
    pool.cls(pool.idx(data.readU2()))

  def readSuperClass()(using ds: DataStream, pool: ConstantPool): Option[ConstantInfo.Class[pool.type]] = {
    val idx = data.readU2()
    val entry =
      if idx == 0 then None
      else Some(pool.cls(pool.idx(idx)))
    entry
  }

  def readInterfaces()(using ds: DataStream, pool: ConstantPool): IArray[ConstantInfo.Class[pool.type]] = {
    val count = data.readU2()
    val interfaces =
      for i <- 0 until count yield pool.cls(pool.idx(data.readU2()))
    IArray.from(interfaces)
  }

  def skipMethods()(using DataStream): Forked[DataStream] = skipMembers()
  def skipFields()(using DataStream): Forked[DataStream] = skipMembers()

  def skipAttributes()(using DataStream): Forked[DataStream] =
    data.forkAndSkip(skipAttributesInternal())

  private def skipAttributesInternal()(using DataStream): Unit = {
    val count = data.readU2()
    loop(count) {
      data.skip(2) // name index
      data.skip(data.readU4()) // attribute length and info
    }
  }

  private def skipMembers()(using DataStream): Forked[DataStream] = {
    val reader = data.fork
    val count = data.readU2()
    loop(count) {
      data.skip(6) // access flags, name index, descriptor index
      skipAttributesInternal()
    }
    reader
  }

  def readFields(op: (SimpleName, SigOrDesc, AccessFlags) => Unit)(using DataStream, ConstantPool): Unit =
    readMembers(isMethod = false, op)

  def readMethods(op: (SimpleName, SigOrDesc, AccessFlags) => Unit)(using DataStream, ConstantPool): Unit =
    readMembers(isMethod = true, op)

  private def readMembers(
    isMethod: Boolean,
    op: (SimpleName, SigOrDesc, AccessFlags) => Unit
  )(using ds: DataStream, pool: ConstantPool): Unit = {
    val count = data.readU2()
    loop(count) {
      val accessFlags = readAccessFlags()
      val nameIdx = pool.idx(data.readU2())
      val name = pool.utf8(nameIdx)
      val descriptorIdx = pool.idx(data.readU2())
      val desc = pool.utf8(descriptorIdx).name
      var sigOrNull: String | Null = null
      scanAttributes {
        case attr.Signature => // optional, only if there are generic type arguments
          data.fork.use {
            sigOrNull = readSignature
          }
          false
        case _ => false
      }
      val sig = sigOrNull
      if !accessFlags.isSynthetic then
        if sig == null then op(name, SigOrDesc.Desc(desc), accessFlags)
        else op(name, SigOrDesc.Sig(sig), accessFlags)
    }
  }

  def readSignature(using ds: DataStream, pool: ConstantPool): String =
    val sigIdx = pool.idx(data.readU2())
    pool.utf8(sigIdx).name

  def scanAttributes(onName: DataStream ?=> SimpleName => Boolean)(using ds: DataStream, pool: ConstantPool): Unit = {
    val count = data.readU2()
    loop(count) {
      val attrNameIdx = pool.idx(data.readU2())
      val attrName = pool.utf8(attrNameIdx)
      val attrLen = data.readU4()
      if onName(attrName) then return ()
      data.skip(attrLen)
    }
  }

  def readAnnotation(
    typeDescriptors: Set[SimpleName]
  )(using ds: DataStream, pool: ConstantPool): Option[Annotation[pool.type]] = {
    // pre: we are already inside the RuntimeVisibleAnnotations attribute

    def skipAnnotationArgument(): Unit = {
      import AnnotationValue.Tags
      val tag = data.readU1().toChar
      tag match {
        case Tags.Byte | Tags.Char | Tags.Double | Tags.Float | Tags.Int | Tags.Long | Tags.Short | Tags.Boolean |
            Tags.String | Tags.Class =>
          data.skip(2)
        case Tags.Enum =>
          data.skip(3)
        case Tags.Annotation =>
          skipAnnotation()
        case Tags.Array =>
          val count = data.readU2()
          loop(count) {
            skipAnnotationArgument()
          }
        case _ =>
          throw ClassfileFormatException(s"Invalid annotation argument tag $tag")
      }
    }

    def skipAnnotation(): Unit = {
      data.skip(2) // type index
      skipAnnotationArgs()
    }

    def skipAnnotationArgs(): Unit = {
      val numPairs = data.readU2()
      loop(numPairs) {
        data.skip(2) // name index
        skipAnnotationArgument()
      }
    }

    def readAnnotationArgument(): AnnotationValue[pool.type] = {
      import AnnotationValue.Tags
      val tag = data.readU1().toChar
      tag match {
        case Tags.Byte | Tags.Char | Tags.Double | Tags.Float | Tags.Int | Tags.Long | Tags.Short | Tags.Boolean |
            Tags.String =>
          AnnotationValue.Const(pool.idx(data.readU2()))
        case Tags.Enum =>
          data.skip(1)
          data.skip(2)
          AnnotationValue.Unknown()
        case Tags.Class =>
          data.skip(2)
          AnnotationValue.Unknown()
        case Tags.Annotation =>
          skipAnnotation()
          AnnotationValue.Unknown()
        case Tags.Array =>
          val count = data.readU2()
          val values = accumulateAnnotValues(count) {
            readAnnotationArgument()
          }
          AnnotationValue.Arr(values)
        case _ =>
          throw ClassfileFormatException(s"Invalid annotation argument tag $tag")
      }
    }

    def readAnnotationArgs(tpe: SimpleName): Annotation[pool.type] = {
      val numPairs = data.readU2()
      val args = accumulateAnnotValues(numPairs) {
        data.skip(2) // name index
        readAnnotationArgument()
      }
      Annotation(tpe, args)
    }

    val numAnnots = data.readU2()
    loop(numAnnots) {
      val typeIdx = pool.idx(data.readU2())
      val typeName = pool.utf8(typeIdx)
      if typeDescriptors.contains(typeName) then {
        return Some(readAnnotationArgs(typeName))
      } else {
        skipAnnotationArgs()
      }
    }
    None
  }

  def readInnerClasses(
    op: (SimpleName, SimpleName, SimpleName, FlagSet) => Unit
  )(using ds: DataStream, pool: ConstantPool): Unit = {
    val numberOfClasses = data.readU2()
    loop(numberOfClasses) {
      val innerClassIdx = pool.idx(data.readU2())
      val outerClassId = data.readU2() // 0 if a local/anonymous class
      val innerNameId = data.readU2() // 0 if anonymous
      val accessFlags = readAccessFlags().toFlags

      // We don't care about local, anonymous or synthetic classes
      if outerClassId != 0 && innerNameId != 0 && !accessFlags.is(Synthetic) then
        val innerClass = pool.utf8(pool.cls(innerClassIdx).nameIdx)
        val innerName = pool.utf8(pool.idx(innerNameId))
        val outerClass = pool.utf8(pool.cls(pool.idx(outerClassId)).nameIdx)
        op(innerName, innerClass, outerClass, accessFlags)
    }
  }

  private def acceptConstantInfo()(using ds: DataStream, pool: ConstantPool): ConstantInfo[pool.type] = {
    import ClassfileReader.ConstantInfo as c
    import pool.idx
    val tag = data.readU1()
    tag match {
      case c.Tags.Class              => c.Class(idx(data.readU2()))
      case c.Tags.Fieldref           => c.Fieldref(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.Methodref          => c.Methodref(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.InterfaceMethodref => c.InterfaceMethodref(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.String             => c.String(idx(data.readU2()))
      case c.Tags.Integer            => c.Integer(data.readU4())
      case c.Tags.Float              => c.Float(data.readU4f())
      case c.Tags.Long               => c.Long(data.readU8())
      case c.Tags.Double             => c.Double(data.readU8f())
      case c.Tags.NameAndType        => c.NameAndType(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.Utf8               => c.Utf8(data.forkAndSkip(data.skip(data.readU2())))
      case c.Tags.MethodHandle       => c.MethodHandle(idx(data.readU1()), idx(data.readU2()))
      case c.Tags.MethodType         => c.MethodType(idx(data.readU2()))
      case c.Tags.Dynamic            => c.Dynamic(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.InvokeDynamic      => c.InvokeDynamic(idx(data.readU2()), idx(data.readU2()))
      case c.Tags.Module             => c.Module(idx(data.readU2()))
      case c.Tags.Package            => c.Package(idx(data.readU2()))
      case _ =>
        throw ClassfileFormatException(s"Invalid constant tag $tag")
    }
  }
}

private[classfiles] object ClassfileReader {
  import Indexing.*
  import Access.*

  inline val JavaMajorVersion = 45
  inline val JavaMinorVersion = 3 // Java 1.1 (needed for `java.rmi.activation.ActivationGroup_Stub` in rt.jar)
  inline val JavaMagicNumber = 0xcafebabe

  private inline def loop(times: Int)(inline op: => Unit): Unit = {
    var i = 0
    while (i < times) {
      op
      i += 1
    }
  }

  private inline def accumulateAnnotValues[P <: ClassfileReader.ConstantPool](
    size: Int
  )(inline op: => AnnotationValue[P]): IArray[AnnotationValue[P]] = {
    val arr = new Array[AnnotationValue[P]](size)
    var i = 0
    while (i < size) {
      arr(i) = op
      i += 1
    }
    IArray.unsafeFromArray(arr)
  }

  enum SigOrDesc:
    case Sig(str: String)
    case Desc(str: String)

  enum SigOrSupers:
    case Sig(str: String)
    case Supers

  type ConstantPool = ClassfileReader#ConstantPool & Singleton

  object Access:
    opaque type AccessFlags = Int

    object AccessFlags:

      def read(raw: Int): AccessFlags = raw

      extension (access: AccessFlags)
        private def isSet(flag: AccessFlags): Boolean = (access & flag) == flag

        def isSynthetic: Boolean = isSet(Tags.Synthetic)

        def isPackagePrivate: Boolean = !isSet(Tags.Protected) && !isSet(Tags.Private) && !isSet(Tags.Public)

        /** Is the corresponding member a Varargs method, *asumming* it is a method in the first place?
          *
          * The `ACC_VARARGS` flag shares its numerical value with `ACC_TRANSIENT` for fields,
          * so this method will return non-sensical results if called for a field member.
          */
        def isVarargsIfMethod: Boolean = isSet(Tags.Varargs)

        def isNativeVarargsIfMethod: Boolean = isVarargsIfMethod && isSet(Tags.Native)

        def toFlags: FlagSet =
          var flags = EmptyFlagSet
          if isSet(Tags.Private) then flags |= Private
          if isSet(Tags.Protected) then flags |= Protected
          if isSet(Tags.Static) then flags |= Static
          if isSet(Tags.Final) then flags |= Final
          if isSet(Tags.Interface) then flags |= Trait
          if isSet(Tags.Abstract) then flags |= Abstract
          if isSet(Tags.Synthetic) then flags |= Synthetic
          if isSet(Tags.Enum) then flags |= Enum
          flags

      object Tags:
        inline val Public = 0x0001
        inline val Private = 0x0002
        inline val Protected = 0x0004
        inline val Static = 0x0008
        inline val Final = 0x0010
        inline val Varargs = 0x0080
        inline val Native = 0x0100
        inline val Interface = 0x0200
        inline val Abstract = 0x0400
        inline val Synthetic = 0x1000
        inline val Annotation = 0x2000
        inline val Enum = 0x4000
      end Tags
    end AccessFlags
  end Access

  object Indexing {
    opaque type Index[C <: ConstantPool] <: Int = Int
    private[ClassfileReader] def idx[C <: ConstantPool](pool: C, index: Int): Index[pool.type] = index
  }

  enum ConstantInfo[C <: ConstantPool] derives CanEqual {
    case Class(nameIdx: Index[C])
    case Fieldref(classIdx: Index[C], nameandtypeIdx: Index[C])
    case Methodref(classIdx: Index[C], nameandtypeIdx: Index[C])
    case InterfaceMethodref(classIdx: Index[C], nameandtypeIdx: Index[C])
    case String(stringIdx: Index[C])
    case Integer(value: Int)
    case Float(value: scala.Float)
    case Long(value: scala.Long)
    case Double(value: scala.Double)
    case NameAndType(nameIdx: Index[C], descriptorIdx: Index[C])
    case Utf8(value: SimpleName | Forked[DataStream])
    case MethodHandle(referenceKind: Index[C], referenceIndex: Index[C])
    case MethodType(descriptorIdx: Index[C])
    case Dynamic(bootstrapMethodAttrIndex: Index[C], nameAndTypeIndex: Index[C])
    case InvokeDynamic(bootstrapMethodAttrIndex: Index[C], nameAndTypeIndex: Index[C])
    case Module(nameIdx: Index[C])
    case Package(nameIdx: Index[C])
  }

  object ConstantInfo {
    object Tags {
      inline val Class = 7
      inline val Fieldref = 9
      inline val Methodref = 10
      inline val InterfaceMethodref = 11
      inline val String = 8
      inline val Integer = 3
      inline val Float = 4
      inline val Long = 5
      inline val Double = 6
      inline val NameAndType = 12
      inline val Utf8 = 1
      inline val MethodHandle = 15
      inline val MethodType = 16
      inline val Dynamic = 17
      inline val InvokeDynamic = 18
      inline val Module = 19
      inline val Package = 20
    }
  }

  enum AnnotationValue[C <: ConstantPool] {
    case Const(valueIdx: Index[C])
    case Arr(values: IArray[AnnotationValue[C]])
    case Unknown()
  }

  object AnnotationValue {
    object Tags {
      inline val Byte = 'B'
      inline val Char = 'C'
      inline val Double = 'D'
      inline val Float = 'F'
      inline val Int = 'I'
      inline val Long = 'J'
      inline val Short = 'S'
      inline val Boolean = 'Z'
      inline val String = 's'
      inline val Enum = 'e'
      inline val Class = 'c'
      inline val Annotation = '@'
      inline val Array = '['
    }
  }

  case class Annotation[P <: ClassfileReader.ConstantPool](tpe: SimpleName, values: IArray[AnnotationValue[P]])

  inline def data(using data: DataStream): data.type = data

  trait DataStream {
    def readU1(): Int
    def readU2(): Int
    def readU4(): Int
    def readU4f(): Float
    def readU8(): Long
    def readU8f(): Double
    def readUTF8(): String
    def readSlice(length: Int): IArray[Byte]
    def skip(bytes: Int): Unit
    def fork: Forked[DataStream]

    inline def forkAndSkip(skipOp: => Unit): Forked[DataStream] =
      val forked = fork
      skipOp
      forked
  }

  def unpickle[T](classRoot: ClassData)(op: ClassfileReader => DataStream ?=> T): T =
    ClassfileBuffer.Root(classRoot.bytes, 0).use { s ?=>
      op(ClassfileReader())
    }
}
