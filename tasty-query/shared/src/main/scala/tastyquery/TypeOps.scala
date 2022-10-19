package tastyquery

import tastyquery.Contexts.*
import tastyquery.Symbols.*
import tastyquery.Types.*
import tastyquery.TypeMaps.*

private[tastyquery] object TypeOps:
  def asSeenFrom(tp: Type, pre: Type, cls: Symbol)(using Context): Type =
    new AsSeenFromMap(pre, cls).apply(tp)

  /** The TypeMap handling the asSeenFrom */
  class AsSeenFromMap(pre: Type, cls: Symbol)(using Context) extends ApproximatingTypeMap {

    /** Set to true when the result of `apply` was approximated to avoid an unstable prefix. */
    var approximated: Boolean = false

    def apply(tp: Type): Type = {

      /** Map a `C.this` type to the right prefix. If the prefix is unstable, and
        *  the current variance is <= 0, return a range.
        *  @param  pre     The prefix
        *  @param  cls     The class in which the `C.this` type occurs
        *  @param  thiscls The prefix `C` of the `C.this` type.
        */
      def toPrefix(pre: Type, cls: Symbol, thiscls: ClassSymbol): Type =
        if ((pre eq NoType) || (pre eq NoPrefix) || (cls.isPackage))
          tp
        else
          pre match {
            //case pre: SuperType => toPrefix(pre.thistpe, cls, thiscls)
            case _ =>
              cls match
                case cls: ClassSymbol =>
                  if (thiscls.isSubclass(cls) && pre.baseType(thiscls) != NoType)
                    /*if (variance <= 0 && !isLegalPrefix(pre)) // isLegalPrefix always true?
                    if (variance < 0) {
                      approximated = true
                      NothingType
                    }
                    else
                      // Don't set the `approximated` flag yet: if this is a prefix
                      // of a path, we might be able to dealias the path instead
                      // (this is handled in `ApproximatingTypeMap`). If dealiasing
                      // is not possible, then `expandBounds` will end up being
                      // called which we override to set the `approximated` flag.
                      range(NothingType, pre)
                  else*/ pre
                  /*else if (pre.termSymbol.isPackage && !thiscls.isPackage)
                  toPrefix(pre.select(nme.PACKAGE), cls, thiscls)*/
                  else
                    toPrefix(pre.baseType(cls).normalizedPrefix, cls.owner.nn, thiscls)
                case _ =>
                  NoType
          }
      end toPrefix

      tp match {
        case tp: ThisType =>
          toPrefix(pre, cls, tp.cls)
        case _ =>
          mapOver(tp)
      }
    }

    override def reapply(tp: Type): Type =
      // derived infos have already been subjected to asSeenFrom, hence no need to apply the map again.
      tp

    override protected def expandBounds(tp: TypeBounds): Type = {
      approximated = true
      super.expandBounds(tp)
    }
  }
end TypeOps
