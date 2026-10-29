package tastyquery

import scala.concurrent.Await
import scala.concurrent.duration.Duration

import tastyquery.Contexts.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.testutil.TestPlatform

object ManualDocStringCheck:
  def main(args: Array[String]): Unit =
    val classpath = Await.result(TestPlatform.loadClasspath(), Duration.Inf)
    given ctx: Context = Context.initialize(classpath)

    val DocStrings = ctx.findTopLevelClass("simple_trees.DocStrings")

    println("class              : " + DocStrings.docString)
    println("type member        : " + DocStrings.findDecl(typeName("DocumentedType")).docString)
    println("value              : " + DocStrings.findDecl(termName("documentedValue")).docString)
    println("overloaded methods : " + DocStrings.findAllOverloadedDecls(termName("documentedMethod")).map(_.docString))
    println("non-ASCII          : " + DocStrings.findNonOverloadedDecl(termName("documentedWithNonAscii")).docString)
    println("object class       : " + DocStrings.findDecl(moduleClassName("DocumentedObject")).asClass.docString)
    println("object value       : " + DocStrings.findDecl(moduleClassName("DocumentedObject")).asClass.moduleValue.get.docString)
    println("inherited          : " + DocStrings.findMember(termName("inheritedDocumentedMethod")).docString)
    println("undocumented method: " + DocStrings.findNonOverloadedDecl(termName("undocumentedMethod")).docString)
    println("undocumented value : " + DocStrings.findDecl(termName("undocumentedValue")).docString)
    println(
      "java toString      : " + ctx.findStaticClass("java.lang.Object").findNonOverloadedDecl(termName("toString")).docString
    )
  end main
end ManualDocStringCheck