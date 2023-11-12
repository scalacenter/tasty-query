package tastyquery

import scala.annotation.tailrec

import tastyquery.Constants.*
import tastyquery.Contexts.*
import tastyquery.Exceptions.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Trees.*
import tastyquery.Types.*

object Annotations:
  final class Annotation(val tree: TermTree):
    private var mySymbol: ClassSymbol | Null = null
    private var myArguments: List[TermTree] | Null = null

    /** The annotation class symbol. */
    def symbol(using Context): ClassSymbol =
      val local = mySymbol
      if local != null then local
      else
        val computed = computeAnnotSymbol(tree)
        mySymbol = computed
        computed
    end symbol

    /** The symbol of the constructor used in the annotation.
      *
      * This operation is not supported for annotations read from Scala 2.
      * It will throw an `UnsupportedOperationException`.
      */
    def annotConstructor(using Context): TermSymbol =
      computeAnnotConstructor(tree)

    /** All the term arguments to the annotation's constructor.
      *
      * If the constructor has several parameter lists, the arguments are
      * flattened in a single list.
      *
      * `NamedArg`s are not visible with this method. They are replaced by
      * their right-hand-side.
      */
    def arguments: List[TermTree] =
      val local = myArguments
      if local != null then local
      else
        val computed = computeAnnotArguments(tree)
        myArguments = computed
        computed
    end arguments

    def argCount: Int = arguments.size

    def argIfConstant(idx: Int): Option[Constant] =
      arguments(idx) match
        case Literal(constant) => Some(constant)
        case _                 => None

    /** Tests whether this annotation points to `defn.internalRepeatedAnnotClass` without resolving anything.
      *
      * If yes, returns `Some(packageRef)` for the `scala.annotation.internal` package.
      * Otherwise, returns `None`.
      */
    private[tastyquery] def syntacticExtractInternalRepeatedAnnot: Option[PackageRef] =
      val tpt = findNewAnnotTypeTree(tree)
      tpt match
        // It is compiler-synthetic by definition, so it can only be a TypeWrapper
        case TypeWrapper(tpe: TypeRef) =>
          if tpe.name != tpnme.internalRepeatedAnnot then None
          else
            tpe.prefix match
              case pkg: PackageRef =>
                if pkg.fullyQualifiedName == PackageFullName.scalaAnnotationInternalPackage then Some(pkg)
                else None
              case _ =>
                None
        case _ =>
          None
    end syntacticExtractInternalRepeatedAnnot

    override def toString(): String = s"Annotation($tree)"
  end Annotation

  object Annotation:
    /** Constructs an annotation with the given underlying tree. */
    def apply(tree: TermTree): Annotation =
      new Annotation(tree)

    /** Constructs an annotation with the no-arg constructor of the given class.
      *
      * The class must be static.
      */
    def apply(cls: ClassSymbol)(using Context): Annotation =
      val typeRef = cls.staticRef

      val ctor = cls
        .getAllOverloadedDecls(nme.Constructor)
        .find { ctor =>
          ctor.declaredType match
            case mt: MethodType => mt.paramNames.isEmpty && !mt.resultType.isInstanceOf[MethodicType]
            case _              => false
        }
        .getOrElse {
          throw InvalidProgramStructureException(s"Cannot find a no-arg constructor in $cls")
        }
      val ctorName = ctor.signedName.asInstanceOf[SignedName]

      val pos = SourcePosition.NoPosition
      val tree = Apply(Select(New(TypeWrapper(typeRef)(pos))(pos), ctorName)(Some(typeRef))(pos), Nil)(pos)

      new Annotation(tree)
    end apply
  end Annotation

  private def computeAnnotSymbol(tree: TermTree)(using Context): ClassSymbol =
    val tpt = findNewAnnotTypeTree(tree)
    tpt.toType.classSymbol.getOrElse {
      throw InvalidProgramStructureException(s"Illegal annotation class type ${tpt.toType} in $tree")
    }
  end computeAnnotSymbol

  private def findNewAnnotTypeTree(tree: TermTree): TypeTree =
    def invalid(): Nothing =
      throw InvalidProgramStructureException(s"Cannot find annotation class in $tree")

    @tailrec
    def loop(tree: TermTree): TypeTree = tree match
      case Apply(fun, _)     => loop(fun)
      case New(tpt)          => tpt
      case Select(qual, _)   => loop(qual)
      case TypeApply(fun, _) => loop(fun)
      case Block(_, expr)    => loop(expr)
      case _                 => invalid()

    loop(tree)
  end findNewAnnotTypeTree

  private def computeAnnotConstructor(tree: TermTree)(using Context): TermSymbol =
    def invalid(): Nothing =
      throw InvalidProgramStructureException(s"Cannot find annotation constructor in $tree")

    def unsupportedScala2(): Nothing =
      throw UnsupportedOperationException(s"Cannot compute the annotation constructor of a Scala 2 annotation: $tree")

    @tailrec
    def loop(tree: TermTree): TermSymbol = tree match
      case Apply(fun, _)                 => loop(fun)
      case tree @ Select(New(tpt), name) => if name == nme.Constructor then unsupportedScala2() else tree.symbol.asTerm
      case TypeApply(fun, _)             => loop(fun)
      case Block(_, expr)                => loop(expr)
      case _                             => invalid()

    loop(tree)
  end computeAnnotConstructor

  private def computeAnnotArguments(tree: TermTree): List[TermTree] =
    def invalid(): Nothing =
      throw InvalidProgramStructureException(s"Cannot find annotation arguments in $tree")

    @tailrec
    def loop(tree: TermTree, tail: List[TermTree]): List[TermTree] = tree match
      case Apply(fun, args)    => loop(fun, args ::: tail)
      case Select(New(tpt), _) => tail
      case TypeApply(fun, _)   => loop(fun, tail)
      case Block(_, expr)      => loop(expr, tail)
      case New(tpt)            => tail // for some ancient TASTy with raw New's
      case _                   => invalid()

    loop(tree, Nil).map {
      case NamedArg(_, arg) => arg
      case arg              => arg
    }
  end computeAnnotArguments
end Annotations
