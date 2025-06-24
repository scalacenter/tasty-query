package tastyquery.reader.pickles

import scala.collection.mutable

import PickleReader.{PklStream, index, pkl}

import tastyquery.Annotations.Annotation
import tastyquery.Exceptions.*
import tastyquery.Flags.*
import tastyquery.SourceLanguage
import tastyquery.Symbols.TermOrTypeSymbol

import tastyquery.reader.ReaderContext

private[reader] object Unpickler {
  def loadInfo(sigBytes: IArray[Byte])(using ReaderContext): Unit = {

    def run(reader: PickleReader, structure: reader.Structure)(using PklStream): Unit = {
      import structure.given

      // Read the symbol themselves
      index.loopWithIndices { (offset, i) =>
        if (reader.missingSymbolEntry(i)) {
          pkl.unsafeFork(offset) {
            reader.readMaybeExternalSymbolAt(i)
          }
        }
      }

      // Now read the types of symbols
      reader.completeAllSymbolTypes(structure)

      // Read children after reading the symbols themselves, fix for SI-3951
      index.loopWithIndices { (offset, i) =>
        if (reader.missingEntry(i)) {
          if (reader.isChildrenEntry(i)) {
            pkl.unsafeFork(offset) {
              reader.readChildren()
            }
          }
        }
      }

      // Read the annotations to give to the symbols we read
      val annotationMap = mutable.HashMap.empty[TermOrTypeSymbol, List[Annotation]]
      index.loopWithIndices { (offset, i) =>
        if reader.isSymbolAnnotationEntry(i) then
          pkl.unsafeFork(offset) {
            val (sym, annotation) = reader.readSymbolAnnotation()
            annotationMap.updateWith(sym)(prev => Some(annotation :: prev.getOrElse(Nil)))
          }
      }

      // Assign the annotations
      for sym <- structure.allRegisteredSymbols do
        if !(sym.isClass && sym.asClass.isRefinementClass) then
          val optAnnots = annotationMap.remove(sym)
          sym.setAnnotations(optAnnots.fold(Nil)(_.reverse))
      end for

      if annotationMap.nonEmpty then
        throw Scala2PickleFormatException(annotationMap.mkString(s"Found annotations for unknown symbols:\n", "\n", ""))

      // Check that all the Symbols we created have been completed
      for sym <- structure.allRegisteredSymbols do
        sym.checkCompleted()
        assert(sym.sourceLanguage == SourceLanguage.Scala2, s"$sym of ${sym.getClass()}")
      end for
    }

    PklStream.read(sigBytes) {
      val reader = PickleReader()
      run(reader, reader.readStructure())
    }
  }

}
