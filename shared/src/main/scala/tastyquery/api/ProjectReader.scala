package tastyquery.api

import tastyquery.Contexts
import tastyquery.Contexts.{Context, ctx}
import tastyquery.reader.{TastyUnpickler, TreeUnpickler}

class ProjectReader {

  def read(classes: String*)(using Context): TastyQuery = {
    val trees = classes.flatMap { className =>
      val trees =
        for
          cls <- ctx.getClassIfDefined(className).toOption
          if ctx.classloader.scanClass(cls)
          tasty <- ctx.classloader.topLevelTasty(cls)
        yield tasty

      trees.getOrElse {
        println(s"[warning] No tasty file found for class $className")
        Nil
      }
    }
    new TastyQuery(ctx, TastyTrees(trees.toList))
  }

}
