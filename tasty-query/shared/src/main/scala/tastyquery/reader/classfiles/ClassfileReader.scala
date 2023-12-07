package tastyquery.reader.classfiles

import scala.annotation.switch

import scala.collection.immutable.HashMap
import scala.reflect.ClassTag

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

private[reader] object ClassfileReader {
  import Indexing.*
  import Access.*

  inline val JavaMajorVersion = 45
  inline val JavaMinorVersion = 3 // Java 1.1 (needed for `java.rmi.activation.ActivationGroup_Stub` in rt.jar)
  inline val JavaMagicNumber = 0xcafebabe

  def readStructure(classOwner: DeclaringSymbol, classRoot: ClassData): Structure =
    ClassfileReader.unpickle(classRoot) {
      ClassfileReader.acceptHeader(classOwner, classRoot)

      val pool = ClassfileReader.readConstantPool()
      given ConstantPool = pool

      val access = ClassfileReader.readAccessFlags()
      val thisClass = ClassfileReader.readThisClass()
      val supers = data.forkAndSkip {
        data.skip(2) // superclass
        data.skip(2 * data.readU2()) // interfaces
      }
      Structure(
        access = access,
        binaryName = pool.utf8(thisClass.nameIdx),
        supers = supers,
        fields = ClassfileReader.skipFields(),
        methods = ClassfileReader.skipMethods(),
        attributes = ClassfileReader.skipAttributes()
      )
    }
  end readStructure

  private def acceptHeader(classOwner: DeclaringSymbol, classRoot: ClassData)(using DataStream): Unit = {
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

  private def readConstantPool()(using ds: DataStream): ConstantPool = {
    val count = data.readU2()
    val pool = ConstantPool(count)
    var doAdd = true
    while doAdd do doAdd = pool.add(acceptConstantInfo()(using ds, pool))
    pool
  }

  class Structure(
    val access: AccessFlags,
    val binaryName: SimpleName,
    val supers: Forked[DataStream],
    val fields: Forked[DataStream],
    val methods: Forked[DataStream],
    val attributes: Forked[DataStream]
  )(using val pool: ConstantPool)

  class ConstantPool(count: Int) { pool =>
    import ClassfileReader.Indexing.*

    private val infos = Array.ofDim[ConstantInfo](count)
    private var index = 1

    private var seensigbytes = false

    def cls(idx: Index): ConstantInfo.Class = infos(idx).asInstanceOf[ConstantInfo.Class]

    def utf8(idx: Index): SimpleName = this.apply(idx) match {
      case ConstantInfo.Utf8(name: SimpleName) => name
      case ConstantInfo.Utf8(forked: Forked[DataStream]) =>
        val name = termName(forked.use(data.readUTF8()))
        infos(idx) = ConstantInfo.Utf8(name)
        name
      case _ =>
        throw ClassfileFormatException(s"Expected UTF8 at index $idx")
    }

    def integer(idx: Index): Int = this.apply(idx) match
      case ConstantInfo.Integer(value) => value
      case _                           => throw ClassfileFormatException(s"Expected Integer at index $idx")

    def long(idx: Index): Long = this.apply(idx) match
      case ConstantInfo.Long(value) => value
      case _                        => throw ClassfileFormatException(s"Expected Long at index $idx")

    def float(idx: Index): Float = this.apply(idx) match
      case ConstantInfo.Float(value) => value
      case _                         => throw ClassfileFormatException(s"Expected Float at index $idx")

    def double(idx: Index): Double = this.apply(idx) match
      case ConstantInfo.Double(value) => value
      case _                          => throw ClassfileFormatException(s"Expected Double at index $idx")

    def sigbytes(idx: Index): IArray[Byte] =
      decodeSigBytes(encodedSigbytes(idx))

    def sigbytes(idxs: IArray[Index]): IArray[Byte] =
      decodeSigBytes(idxs.flatMap(encodedSigbytes))

    private def encodedSigbytes(idx: Index): IArray[Byte] = this.apply(idx) match {
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

    private[ClassfileReader] def idx(i: Int): Index = Indexing.idx(i)

    /** An `Index` in this constant pool, or `None` if 0. */
    private[ClassfileReader] def optIdx(i: Int): Option[Index] =
      if i == 0 then None
      else Some(idx(i))

    private[ClassfileReader] def add(info: ConstantInfo): Boolean = {
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

    def apply(index: Index): ConstantInfo = {
      if (index < 1 || index >= infos.length)
        throw ClassfileFormatException(s"Invalid constant pool index $index")
      infos(index)
    }

    def force(index: Index): ConstantInfo =
      this.apply(index) match {
        case ConstantInfo.Utf8(_) =>
          this.utf8(index) // force name
          infos(index)
        case info => info
      }
  }

  def readAccessFlags()(using DataStream): AccessFlags =
    AccessFlags.read(data.readU2())

  def readThisClass()(using ds: DataStream, pool: ConstantPool): ConstantInfo.Class =
    pool.cls(pool.idx(data.readU2()))

  def readSuperClass()(using ds: DataStream, pool: ConstantPool): Option[ConstantInfo.Class] = {
    val idx = data.readU2()
    val entry =
      if idx == 0 then None
      else Some(pool.cls(pool.idx(idx)))
    entry
  }

  def readInterfaces()(using ds: DataStream, pool: ConstantPool): IArray[ConstantInfo.Class] = {
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

  def readMembers(
    op: (AccessFlags, SimpleName, String, Map[SimpleName, Forked[DataStream]]) => Unit
  )(using ds: DataStream, pool: ConstantPool): Unit = {
    val count = data.readU2()
    loop(count) {
      val accessFlags = readAccessFlags()
      val nameIdx = pool.idx(data.readU2())
      val name = pool.utf8(nameIdx)
      val descriptorIdx = pool.idx(data.readU2())
      val desc = pool.utf8(descriptorIdx).name
      val attributes = readAttributeMap()
      if !accessFlags.isSynthetic then op(accessFlags, name, desc, attributes)
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

  type AttributeMap = Map[SimpleName, Forked[DataStream]]

  def readAttributeMap()(using ds: DataStream, pool: ConstantPool): AttributeMap =
    val builder = HashMap.newBuilder[SimpleName, Forked[DataStream]]
    scanAttributes { attributeName =>
      builder += attributeName -> data.fork
      false
    }
    builder.result()
  end readAttributeMap

  def readAttribute(attributeName: SimpleName)(using DataStream, ConstantPool): Option[Forked[DataStream]] =
    var result: Option[Forked[DataStream]] = None
    scanAttributes {
      case `attributeName` =>
        result = Some(data.fork)
        true
      case _ =>
        false
    }
    result
  end readAttribute

  def readMethodParameters()(using ds: DataStream, pool: ConstantPool): List[(UnsignedTermName, AccessFlags)] =
    val numParameters = data.readU1()
    val resultBuilder = List.newBuilder[(UnsignedTermName, AccessFlags)]

    var index = 0
    while index != numParameters do
      val nameIndex = data.readU2()
      val name =
        if nameIndex == 0 then UniqueName(termName("x"), "$", index)
        else pool.utf8(pool.idx(nameIndex))
      val accessFlags = AccessFlags.read(data.readU2())
      resultBuilder += ((name, accessFlags))
      index += 1
    end while

    resultBuilder.result()
  end readMethodParameters

  def readAnnotation(typeDescriptors: Set[SimpleName])(using ds: DataStream, pool: ConstantPool): Option[Annotation] = {
    // pre: we are already inside the RuntimeVisibleAnnotations attribute

    def skipAnnotationArgument(): Unit = {
      import AnnotationValue.Tags
      val tag = data.readU1().toChar
      tag match {
        case Tags.Byte | Tags.Char | Tags.Double | Tags.Float | Tags.Int | Tags.Long | Tags.Short | Tags.Boolean |
            Tags.String | Tags.Class =>
          data.skip(2)
        case Tags.Enum =>
          data.skip(4)
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

    val numAnnots = data.readU2()
    loop(numAnnots) {
      val typeIdx = pool.idx(data.readU2())
      val typeName = pool.utf8(typeIdx)
      if typeDescriptors.contains(typeName) then
        val args = readAnnotationArgs()
        return Some(Annotation(typeName, args))
      else skipAnnotationArgs()
    }
    None
  }

  def readAllAnnotations()(using ds: DataStream, pool: ConstantPool): List[Annotation] =
    val numAnnots = data.readU2()
    val resultBuilder = List.newBuilder[Annotation]
    loop(numAnnots) {
      resultBuilder += readAnnotation()
    }
    resultBuilder.result()
  end readAllAnnotations

  def readAllParameterAnnotations()(using ds: DataStream, pool: ConstantPool): List[List[Annotation]] =
    val numParameters = data.readU1()
    val resultBuilder = List.newBuilder[List[Annotation]]
    loop(numParameters) {
      resultBuilder += readAllAnnotations()
    }
    resultBuilder.result()
  end readAllParameterAnnotations

  private def readAnnotation()(using ds: DataStream, pool: ConstantPool): Annotation =
    val typeName = pool.utf8(pool.idx(data.readU2()))
    val args = readAnnotationArgs()
    Annotation(typeName, args)
  end readAnnotation

  private def readAnnotationArgs()(using ds: DataStream, pool: ConstantPool): IArray[(SimpleName, AnnotationValue)] =
    val numPairs = data.readU2()
    accumulateAnnotValues(numPairs) {
      val nameIdx = pool.idx(data.readU2())
      val argName = pool.utf8(nameIdx)
      val value = readAnnotationArgument()
      argName -> value
    }
  end readAnnotationArgs

  private def readAnnotationArgument()(using ds: DataStream, pool: ConstantPool): AnnotationValue =
    import AnnotationValue.Tags

    def readPoolIndex(): Index = pool.idx(data.readU2())

    val tag = data.readU1().toChar
    (tag: @switch) match {
      case Tags.Byte | Tags.Char | Tags.Double | Tags.Float | Tags.Int | Tags.Long | Tags.Short | Tags.Boolean |
          Tags.String =>
        AnnotationValue.Const(tag, readPoolIndex())
      case Tags.Enum =>
        val typeName = pool.utf8(readPoolIndex())
        val constName = pool.utf8(readPoolIndex())
        AnnotationValue.EnumConst(typeName, constName)
      case Tags.Class =>
        val descriptor = pool.utf8(readPoolIndex())
        AnnotationValue.ClassConst(descriptor)
      case Tags.Annotation =>
        val annotation = readAnnotation()
        AnnotationValue.NestedAnnotation(annotation)
      case Tags.Array =>
        val count = data.readU2()
        val values = accumulateAnnotValues(count) {
          readAnnotationArgument()
        }
        AnnotationValue.Arr(values)
      case _ =>
        throw ClassfileFormatException(s"Invalid annotation argument tag $tag")
    }
  end readAnnotationArgument

  /** Reads the content of the `InnerClasses` attribute.
    *
    * Calls `op` for each entry with the following arguments:
    *
    * - `innerBinaryName`: the fully-qualified binary name of the inner class.
    * - `outerBinaryName`: the declaring outer class of the inner class, if
    *   it exists, i.e., if it is not top-level, local, or anymous.
    * - `innerSimpleName`: the simple name of the inner class, as found in the
    *   source code, if it is not anonymous.
    * - `innerAccessFlags`: the access flags of the inner class.
    */
  def readInnerClasses(
    op: (SimpleName, Option[SimpleName], Option[SimpleName], FlagSet) => Unit
  )(using ds: DataStream, pool: ConstantPool): Unit = {
    val numberOfClasses = data.readU2()
    loop(numberOfClasses) {
      val innerClassIdx = pool.idx(data.readU2())
      val outerClassIdx = pool.optIdx(data.readU2()) // 0 if a local/anonymous class
      val innerNameIdx = pool.optIdx(data.readU2()) // 0 if anonymous
      val accessFlags = readAccessFlags().toFlags

      val innerBinaryName = pool.utf8(pool.cls(innerClassIdx).nameIdx)
      val outerBinaryName = outerClassIdx.map(idx => pool.utf8(pool.cls(idx).nameIdx))
      val innerSimpleName = innerNameIdx.map(pool.utf8(_))

      op(innerBinaryName, outerBinaryName, innerSimpleName, accessFlags)
    }
  }

  private def acceptConstantInfo()(using ds: DataStream, pool: ConstantPool): ConstantInfo = {
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

  private inline def loop(times: Int)(inline op: => Unit): Unit = {
    var i = 0
    while (i < times) {
      op
      i += 1
    }
  }

  private inline def accumulateAnnotValues[A: ClassTag](size: Int)(inline op: => A): IArray[A] = {
    val arr = new Array[A](size)
    var i = 0
    while (i < size) {
      arr(i) = op
      i += 1
    }
    IArray.unsafeFromArray(arr)
  }

  type MemberSig = String

  object Access:
    opaque type AccessFlags = Int

    object AccessFlags:

      def read(raw: Int): AccessFlags = raw

      extension (access: AccessFlags)
        private def isSet(flag: AccessFlags): Boolean = (access & flag) == flag

        def isStatic: Boolean = isSet(Tags.Static)

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
    opaque type Index <: Int = Int
    private[ClassfileReader] def idx(index: Int): Index = index
  }

  enum ConstantInfo derives CanEqual {
    case Class(nameIdx: Index)
    case Fieldref(classIdx: Index, nameandtypeIdx: Index)
    case Methodref(classIdx: Index, nameandtypeIdx: Index)
    case InterfaceMethodref(classIdx: Index, nameandtypeIdx: Index)
    case String(stringIdx: Index)
    case Integer(value: Int)
    case Float(value: scala.Float)
    case Long(value: scala.Long)
    case Double(value: scala.Double)
    case NameAndType(nameIdx: Index, descriptorIdx: Index)
    case Utf8(value: SimpleName | Forked[DataStream])
    case MethodHandle(referenceKind: Index, referenceIndex: Index)
    case MethodType(descriptorIdx: Index)
    case Dynamic(bootstrapMethodAttrIndex: Index, nameAndTypeIndex: Index)
    case InvokeDynamic(bootstrapMethodAttrIndex: Index, nameAndTypeIndex: Index)
    case Module(nameIdx: Index)
    case Package(nameIdx: Index)
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

  enum AnnotationValue {
    case Const(tag: Char, valueIdx: Index)
    case EnumConst(descriptor: SimpleName, constName: SimpleName)
    case ClassConst(descriptor: SimpleName)
    case NestedAnnotation(annotation: Annotation)
    case Arr(values: IArray[AnnotationValue])
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

  case class Annotation(tpe: SimpleName, values: IArray[(SimpleName, AnnotationValue)])

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

  def unpickle[T](classRoot: ClassData)(op: DataStream ?=> T): T =
    ClassfileBuffer.Root(classRoot.readClassFileBytes(), 0).use(op)
}
