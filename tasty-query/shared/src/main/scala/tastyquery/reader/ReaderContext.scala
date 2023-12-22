package tastyquery.reader

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.SourceFile
import tastyquery.Symbols.*
import tastyquery.Types.*

/** A restricted Context that is safe to use from the readers.
  *
  * It does not give access to anything that might require reading other files.
  */
private[reader] final class ReaderContext(underlying: Context):
  def RootPackage: PackageSymbol = underlying.defn.RootPackage
  def EmptyPackage: PackageSymbol = underlying.defn.EmptyPackage
  def javaLangPackage: PackageSymbol = underlying.defn.javaLangPackage
  def javaLangInvokePackage: PackageSymbol = underlying.defn.javaLangInvokePackage
  def scalaPackage: PackageSymbol = underlying.defn.scalaPackage

  def NothingType: NothingType = underlying.defn.NothingType
  def AnyType: TypeRef = underlying.defn.AnyType
  def MatchableType: TypeRef = underlying.defn.MatchableType
  def ObjectType: TypeRef = underlying.defn.ObjectType
  def FromJavaObjectType: TypeRef = underlying.defn.FromJavaObjectType

  def IntType: TypeRef = underlying.defn.IntType
  def LongType: TypeRef = underlying.defn.LongType
  def FloatType: TypeRef = underlying.defn.FloatType
  def DoubleType: TypeRef = underlying.defn.DoubleType
  def BooleanType: TypeRef = underlying.defn.BooleanType
  def ByteType: TypeRef = underlying.defn.ByteType
  def ShortType: TypeRef = underlying.defn.ShortType
  def CharType: TypeRef = underlying.defn.CharType
  def UnitType: TypeRef = underlying.defn.UnitType

  def AnnotationType: TypeRef = underlying.defn.AnnotationType

  def ArrayTypeOf(tpe: TypeOrWildcard): AppliedType = underlying.defn.ArrayTypeOf(tpe)

  def GenericTupleTypeOf(elementTypes: List[TypeOrWildcard]): Type = underlying.defn.GenericTupleTypeOf(elementTypes)

  def NothingAnyBounds: AbstractTypeBounds = underlying.defn.NothingAnyBounds

  def uninitializedMethodTermRef: TermRef = underlying.defn.uninitializedMethodTermRef

  def scala2FakeOwner: TermSymbol = underlying.defn.scala2FakeOwner

  def scala2MacroInfoFakeMethod: TermSymbol = underlying.defn.scala2MacroInfoFakeMethod

  def findPackageFromRootOrCreate(fullyQualifiedName: PackageFullName): PackageSymbol =
    underlying.findPackageFromRootOrCreate(fullyQualifiedName)

  /** Reads a package reference, with a fallback on faked term references.
    *
    * In a full, correct classpath, `createPackageSelection()` will always
    * return a `PackageRef`. However, in an incomplete or incorrect classpath,
    * this method may return a `TermRef` if the target package does not exist.
    *
    * An alternative would be to create missing packages on the fly, but that
    * would not be consistent with `Trees.Select.tpe` and
    * `Trees.TermRefTypeTree.toType`.
    */
  def createPackageSelection(path: List[TermName]): TermReferenceType =
    path.foldLeft[TermReferenceType](RootPackage.packageRef) { (prefix, name) =>
      NamedType.possibleSelFromPackage(prefix, name)
    }
  end createPackageSelection

  def getSourceFile(path: String): SourceFile =
    underlying.getSourceFile(path)

  def hasGenericTuples: Boolean = underlying.hasGenericTuples

  def createObjectMagicMethods(cls: ClassSymbol): Unit =
    underlying.defn.createObjectMagicMethods(cls)

  def createStringMagicMethods(cls: ClassSymbol): Unit =
    underlying.defn.createStringMagicMethods(cls)

  def createEnumMagicMethods(cls: ClassSymbol): Unit =
    underlying.defn.createEnumMagicMethods(cls)

  def createPredefMagicMethods(cls: ClassSymbol): Unit =
    underlying.defn.createPredefMagicMethods(cls)
end ReaderContext

private[reader] object ReaderContext:
  def rctx(using context: ReaderContext): context.type = context
end ReaderContext
