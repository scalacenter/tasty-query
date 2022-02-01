package tastyquery.api

import tastyquery.Contexts
import tastyquery.Contexts.{BaseContext, baseCtx}
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}

class ProjectReader {

  def read(classes: String*)(using BaseContext): TastyQuery = {
    val trees = classes.flatMap { className =>
      baseCtx.classloader.lookupTasty(className) match
        case Some(tasty) =>
          getTreeUnpickler(tasty.bytes).unpickle(using baseCtx.withFile(tasty.debugPath))
        case _ =>
          println(s"[warning] No tasty file found for class $className")
          Nil
    }
    new TastyQuery(baseCtx, TastyTrees(trees.toList))
  }

  private def getTreeUnpickler(bytes: IArray[Byte]): TreeUnpickler = {
    val unpickler = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get
  }
}
