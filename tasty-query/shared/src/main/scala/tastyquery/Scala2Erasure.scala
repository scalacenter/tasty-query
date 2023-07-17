package tastyquery

import scala.collection.mutable.ListBuffer

import tastyquery.Contexts.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.Flags.*

/** Erasure logic specific to Scala 2 symbols.
  *
  * This file is basically copy-pasted from the file of the same name in dotc.
  */
private[tastyquery] object Scala2Erasure:
  /** A type that would be represented as a RefinedType in Scala 2.
    *
    * The `RefinedType` of Scala 2 contains both a list of parents
    * and a list of refinements, intersections are represented as a RefinedType
    * with no refinements.
    */
  private type Scala2RefinedType = RefinedType | AndType

  /** A TypeRef that is known to represent a member of a structural type.
    *
    * Its `prefix` is guaranteed to be a `Type`.
    */
  private type StructuralRef = TypeRef

  /** The equivalent of a Scala 2 type symbol.
    *
    * In some situations, nsc will create a symbol for a type where we wouldn't:
    *
    * - `A with B with C { ... }` is represented with a RefinedType whose
    *   symbol is a fresh class symbol whose parents are `A`, `B`, `C`.
    * - Structural members also get their own symbols.
    *
    * To emulate this, we simply use the type itself as a stand-in for its symbol.
    *
    * See also `sameSymbol` which determines if two pseudo-symbols are really the same.
    */
  private type PseudoSymbol = TypeSymbol | StructuralRef | Scala2RefinedType

  /** Is this a supported Scala 2 refinement or parent of such a type?
    *
    * We do not allow types that look like:
    *   ((A with B) @foo) with C
    * or:
    *   (A { type X <: ... })#X with C`
    *
    * as it would make our implementation of Scala 2 intersection erasure
    * significantly more complicated. The problem is that each textual
    * appearance of an intersection or refinement in a parent corresponds to a
    * fresh instance of RefinedType (because Scala 2 does not hash-cons these
    * types) with a fresh synthetic class symbol, thus affecting the result of
    * `isNonBottomSubClass`. To complicate the matter, the Scala 2 UnCurry phase
    * will also recursively dealias parent types, thus creating distinct class
    * symbols even in situations where the same type alias is used to refer to a
    * given refinement. Note that types like `(A with B) with C` do not run into
    * these issues because they get flattened into a single RefinedType with
    * three parents, cf `flattenedParents`.
    *
    * See sbt-test/scala2-compat/erasure/changes/Main.scala for examples.
    *
    * @throws UnsupportedOperationException if this type is unsupported.
    */
  private def checkSupported(tp: Type)(using Context): Unit = tp match
    case tp: AndType =>
      checkSupported(tp.first)
      checkSupported(tp.second)
    case tp: RefinedType =>
      checkSupported(tp.parent)
    case tp: AnnotatedType if tp.typ.dealias.isInstanceOf[Scala2RefinedType] =>
      throw UnsupportedOperationException(
        s"Unsupported Scala 2 type: Component ${tp.typ} of intersection is annotated."
      )
    case tp: TypeRef if tp.optSymbol.isEmpty && prefixDealiasIsScala2RefinedType(tp.prefix) =>
      throw UnsupportedOperationException(
        s"Unsupported Scala 2 type: Prefix ${tp.prefix} of intersection component is an intersection or refinement."
      )
    case _ =>
      () // OK
  end checkSupported

  private def prefixDealiasIsScala2RefinedType(prefix: Prefix)(using Context): Boolean = prefix match
    case prefix: Type => prefix.dealias.isInstanceOf[Scala2RefinedType]
    case _            => false

  /** The pseudo symbol of `tp`, see `PseudoSymbol`.
    *
    * The pseudo-symbol representation of a given type is chosen such that
    * `isNonBottomSubClass` behaves like it would in Scala 2, in particular
    * this lets us strip all aliases.
    */
  private def pseudoSymbol(tp: Type)(using Context): PseudoSymbol = tp.dealias match
    case tpw: Scala2RefinedType =>
      checkSupported(tpw)
      tpw
    case tpw: TypeRef =>
      tpw.optSymbol.getOrElse {
        /* Since we don't have symbols for structural type members, we use the
         * type itself and rely on `sameSymbol` to determine whether two such
         * types would be represented with the same Scala 2 symbol.
         */
        assert(tpw.prefix.isInstanceOf[Type], s"Found a TypeRef without symbol nor Type prefix: $tpw")
        tpw
      }
    case tpw: TypeProxy =>
      pseudoSymbol(tpw.underlying)
    case tpw: TypeLambda =>
      // in dotc, a TypeLambda is a TypeProxy whose underlying is Any, so we mimic this here
      defn.AnyClass
    case tpw: OrType =>
      Erasure.erase(tpw, SourceLanguage.Scala2) match
        case ErasedTypeRef.ClassRef(cls)      => cls
        case ErasedTypeRef.ArrayTypeRef(_, _) => defn.ArrayClass
    case tpw =>
      throw new UnsupportedOperationException(
        s"Internal error: unhandled class ${tpw.getClass} for type $tpw in pseudoSymbol($tp)"
      )
  end pseudoSymbol

  extension (psym: PseudoSymbol)(using Context)
    /** Would these two pseudo-symbols be represented with the same symbol in Scala 2? */
    private def sameSymbol(other: PseudoSymbol): Boolean =
      // Pattern match on (psym1, psym2) desugared by hand to avoid allocating a tuple
      if psym.isInstanceOf[StructuralRef] && other.isInstanceOf[StructuralRef] then
        val tp1 = psym.asInstanceOf[StructuralRef]
        val tp2 = other.asInstanceOf[StructuralRef]
        /* Two structural members will have the same Scala 2 symbol if they
         * point to the same member. We can't just call `=:=` since different
         * prefixes will still have the same symbol.
         */
        (tp1.name eq tp2.name)
        && pseudoSymbol(tp1.prefix.asInstanceOf[Type]).sameSymbol(pseudoSymbol(tp2.prefix.asInstanceOf[Type]))
      else
        /* We intentionally use referential equality here even though we may end
         * up comparing two equivalent intersection types, because Scala 2 will
         * create fresh symbols for each appearance of an intersection type in
         * source code.
         */
        psym eq other
    end sameSymbol

    /** Is this a class symbol?
      *
      * Also returns true for refinements since they get a class symbol in Scala 2.
      */
    private def isClass: Boolean = psym match
      case _: ClassSymbol       => true
      case _: Scala2RefinedType => true
      case _                    => false
    end isClass

    /** Is this a trait symbol? */
    private def isTrait: Boolean = psym match
      case sym: ClassSymbol => sym.isTrait
      case _                => false
    end isTrait

    /** An emulation of `Symbol#isNonBottomSubClass` from Scala 2.
      *
      * The documentation of the original method is:
      *
      * > Is this class symbol a subclass of that symbol,
      * > and is this class symbol also different from Null or Nothing?
      *
      * Which sounds fine, except that it is also used with non-class symbols,
      * so what does it do then? Its implementation delegates to `Type#baseTypeSeq`
      * whose documentation states:
      *
      * > The base type sequence of T is the smallest set of [...] class types Ti, so that [...]
      *
      * But this is also wrong: the sequence returned by `baseTypeSeq` can
      * contain non-class symbols.
      *
      * Given that we cannot rely on the documentation and that the
      * implementation is extremely complex, this reimplementation is mostly
      * based on reverse-engineering rules derived from the observed behavior of
      * the original method.
      */
    private def isNonBottomSubClass(that: PseudoSymbol): Boolean =
      /** Recurse on the upper-bound of `psym`: an abstract type is a sub of a
        * pseudo-symbol, if its upper-bound is a sub of that pseudo-symbol.
        */
      def goUpperBound(psym: TypeSymbol | StructuralRef): Boolean =
        psym match
          case sym: TypeSymbolWithBounds => go(pseudoSymbol(sym.declaredBounds.high))
          case sym: ClassSymbol          => false
          case tp: StructuralRef         => go(pseudoSymbol(tp.bounds.high))
      end goUpperBound

      def go(psym: PseudoSymbol): Boolean =
        psym.sameSymbol(that) || {
          /* As mentioned in the documentation of `Scala2RefinedType`, in Scala 2
           * these types get their own unique synthetic class symbol, therefore they
           * don't have any sub-class Note that we must return false even if the lhs
           * is an abstract type upper-bounded by this refinement, since each
           * textual appearance of a refinement will have its own class symbol.
           */
          !that.isInstanceOf[Scala2RefinedType] &&
          psym.match
            case sym1: TypeSymbol =>
              that match
                case sym2: TypeSymbol =>
                  if sym1.isClass && sym2.isClass then sym1.asClass.isSubClass(sym2.asClass)
                  else if !sym1.isClass then goUpperBound(sym1)
                  else
                    /* sym2 is an abstract type, return false because
                     * `isNonBottomSubClass` in Scala 2 never considers a class C to
                     * be a a sub of an abstract type T, even if it was declared as
                     * `type T >: C`.
                     */
                    false
                case _ =>
                  goUpperBound(sym1)
            case tp1: StructuralRef =>
              goUpperBound(tp1)
            case tp1: RefinedType =>
              go(pseudoSymbol(tp1.parent))
            case tp1: AndType =>
              go(pseudoSymbol(tp1.first)) || go(pseudoSymbol(tp1.second))
        }
      end go

      go(psym)
    end isNonBottomSubClass
  end extension

  /** An emulation of `Erasure#intersectionDominator` from Scala 2.
    *
    * Accurately reproducing the behavior of this method is extremely difficult
    * because it operates on the symbols of the _non-erased_ parent types, an
    * implementation detail of the compiler. Furthermore, these non-class
    * symbols are passed to methods such as `isNonBottomSubClass` whose behavior
    * is only specified for class symbols. Therefore, the accuracy of this
    * method cannot be guaranteed, the best we can do is make sure it works on
    * as many test cases as possible which can be run from sbt using:
    * > sbt-test/scripted scala2-compat/erasure
    *
    * The body of this method is made to look as much as the Scala 2 version as
    * possible to make them easier to compare, cf:
    * https://github.com/scala/scala/blob/v2.13.5/src/reflect/scala/reflect/internal/transform/Erasure.scala#L356-L389
    */
  private def intersectionDominator(parents: List[Type])(using Context): Type =
    val psyms = parents.map(pseudoSymbol)
    if psyms.contains(defn.ArrayClass) then
      defn.ArrayTypeOf(intersectionDominator(parents.collect { case ArrayTypeOfExtractor(arg) => arg.highIfWildcard }))
    else
      def isUnshadowed(psym: PseudoSymbol): Boolean =
        !(psyms.exists(qsym => !psym.sameSymbol(qsym) && qsym.isNonBottomSubClass(psym)))
      val cs = parents.iterator.filter { p =>
        val psym = pseudoSymbol(p)
        psym.isClass && !psym.isTrait && isUnshadowed(psym)
      }
      if cs.hasNext then cs.next()
      else parents.iterator.filter(p => isUnshadowed(pseudoSymbol(p))).next()
  end intersectionDominator

  private object ArrayTypeOfExtractor:
    def unapply(tp: Type)(using Context): Option[TypeOrWildcard] = tp match
      case tp: AppliedType if tp.tycon.classSymbol.contains(defn.ArrayClass) =>
        Some(tp.args.head)
      case _ =>
        None
    end unapply
  end ArrayTypeOfExtractor

  /** A flattened list of parents of this intersection.
    *
    * Mimic what Scala 2 does: intersections like `A with (B with C)` are
    * flattened to three parents.
    */
  private def flattenedParents(tp: AndType)(using Context): List[Type] =
    val parents = ListBuffer[Type]()

    def collect(parent: Type, parents: ListBuffer[Type]): Unit = parent.dealias match
      case dealiasedParent: AndType =>
        collect(dealiasedParent.first, parents)
        collect(dealiasedParent.second, parents)
      case _ =>
        checkSupported(parent)
        parents += parent

    collect(tp, parents)
    parents.toList
  end flattenedParents

  def eraseAndType(tp: AndType)(using Context): Type =
    intersectionDominator(flattenedParents(tp))
end Scala2Erasure
