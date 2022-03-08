package tastyquery.reader.pickles

import PickleReader.{PklStream, index, pkl}

import tastyquery.Contexts.ClassContext

object Unpickler {
  def loadInfo(sigBytes: IArray[Byte])(using ClassContext): Unit = {

    def run(reader: PickleReader, structure: reader.Structure)(using PklStream): Unit = {
      import structure.given
      index.loopWithIndices { (offset, i) =>
        if (reader.missingSymbolEntry(i)) {
          pkl.unsafeFork(offset) {
            val sym = reader.readSymbol()
            // if sym.exists then
            //   entries(i) = sym
            //   sym.infoOrCompleter match {
            //     case info: ClassUnpickler => info.init()
            //     case _                    =>
            //   }
          }
        }
      }
      // read children last, fix for SI-3951
      index.loopWithIndices { (offset, i) =>
        if (reader.missingEntry(i)) {
          // if (isSymbolAnnotationEntry(i)) {
          //   data.unsafeFork(reader.index(i)) {
          //     readSymbolAnnotation()
          //   }
          // } else if (isChildrenEntry(i)) {
          //   data.unsafeFork(index(i)) {
          //     readChildren()
          //   }
          // }
        }
      }
    }

    PklStream.read(sigBytes) {
      val reader = PickleReader()
      run(reader, reader.readStructure())
    }
  }

}
