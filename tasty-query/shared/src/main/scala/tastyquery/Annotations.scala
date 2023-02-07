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

    /** The symbol of the constructor used in the annotation. */
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
    def arguments(using Context): List[TermTree] =
      val local = myArguments
      if local != null then local
      else
        val computed = computeAnnotArguments(tree)
        myArguments = computed
        computed
    end arguments

    def argCount(using Context): Int = arguments.size

    def argIfConstant(idx: Int)(using Context): Option[Constant] =
      arguments(idx) match
        case Literal(constant) => Some(constant)
        case _                 => None

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

      val ns = Spans.NoSpan
      val tree = Apply(Select(New(TypeWrapper(typeRef)(ns))(ns), ctorName)(Some(typeRef))(ns), Nil)(ns)

      new Annotation(tree)
    end apply
  end Annotation

  private def computeAnnotSymbol(tree: TermTree)(using Context): ClassSymbol =
    def invalid(): Nothing =
      throw InvalidProgramStructureException(s"Cannot find annotation class in $tree")

    @tailrec
    def loop(tree: TermTree): ClassSymbol = tree match
      case Apply(fun, _)     => loop(fun)
      case New(tpt)          => tpt.toType.classSymbol.getOrElse(invalid())
      case Select(qual, _)   => loop(qual)
      case TypeApply(fun, _) => loop(fun)
      case Block(_, expr)    => loop(expr)
      case _                 => invalid()

    loop(tree)
  end computeAnnotSymbol

  private def computeAnnotConstructor(tree: TermTree)(using Context): TermSymbol =
    def invalid(): Nothing =
      throw InvalidProgramStructureException(s"Cannot find annotation constructor in $tree")

    @tailrec
    def loop(tree: TermTree): TermSymbol = tree match
      case Apply(fun, _)              => loop(fun)
      case tree @ Select(New(tpt), _) => tree.tpe.asInstanceOf[TermRef].symbol
      case TypeApply(fun, _)          => loop(fun)
      case Block(_, expr)             => loop(expr)
      case _                          => invalid()

    loop(tree)
  end computeAnnotConstructor

  private def computeAnnotArguments(tree: TermTree)(using Context): List[TermTree] =
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
