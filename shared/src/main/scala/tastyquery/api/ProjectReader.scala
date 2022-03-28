package tastyquery.api

import tastyquery.Contexts
import tastyquery.Contexts.{BaseContext, baseCtx}
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}

class ProjectReader {

  def read(classes: String*)(using BaseContext): TastyQuery = {
    val trees = classes.flatMap { className =>
      val trees =
        for
          cls <- baseCtx.getClassIfDefined(className).toOption
          if baseCtx.classloader.scanClass(cls)
          tasty <- baseCtx.classloader.topLevelTasty(cls)
        yield tasty

      trees.getOrElse {
        println(s"[warning] No tasty file found for class $className")
        Nil
      }
    }
    new TastyQuery(baseCtx, TastyTrees(trees.toList))
  }

}
