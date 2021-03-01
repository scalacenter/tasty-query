import tastyquery.ast.Names.{EmptyTermName, QualifiedName, SimpleName, TypeName}
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{TermRef, TypeRef}
import tastyquery.reader.TastyUnpickler

import java.nio.file.{Files, Paths}

class ReadTreeSuite extends munit.FunSuite {
  val ResourceProperty = "test-resources"

  def unpickle(filename: String): Tree = {
    val resourcePath = getResourcePath(filename)
    val bytes        = Files.readAllBytes(Paths.get(resourcePath))
    val unpickler    = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle.head
  }

  def getResourcePath(name: String): String =
    s"${System.getProperty(ResourceProperty)}/$name.tasty"

  def containsSubtree(p: PartialFunction[Tree, Unit])(t: Tree): Boolean = {
    def rec(t: Tree): Boolean = containsSubtree(p)(t)
    p.isDefinedAt(t) || (t match {
      case PackageDef(_, stats) => stats.exists(rec)
      case TypeDef(_, rhs)      => rec(rhs)
      case Template(constr, parents, self, body) =>
        rec(constr) || rec(self) || parents.exists(rec) || body.exists(rec)
      case ValDef(_, tpt, rhs) => rec(tpt) || rec(rhs)
      case DefDef(_, tparams, vparamss, tpt, rhs) =>
        tparams.exists(rec) || vparamss.flatten.exists(rec) || rec(tpt) || rec(rhs)
      case Select(qualifier, _) => rec(qualifier)
      case Apply(fun, args)     => rec(fun) || args.exists(rec)
      case New(tpt)             => rec(tpt)

      // Nowhere to walk
      case ImportSelector(_, _, _) | Import(_, _) | Ident(_) | TypeTree(_) | EmptyTree => false
    })
  }

  val isJavaLangObject: PartialFunction[Tree, Unit] = {
    case Apply(
          Select(
            New(
              TypeTree(
                TypeRef(
                  TermRef(_, QualifiedName(_, SimpleName("java"), SimpleName("lang"))),
                  TypeName(SimpleName("Object"))
                )
              )
            ),
            _
          ),
          List()
        ) =>
  }

  test("empty-class") {
    assert({
      {
        case PackageDef(
              _,
              List(
                TypeDef(
                  TypeName(SimpleName("EmptyClass")),
                  Template(
                    // default constructor: no type params, no arguments, empty body
                    DefDef(SimpleName("<init>"), List(), List(), TypeTree(_), EmptyTree),
                    // a single parent -- java.lang.Object
                    List(parent),
                    // self not specified => EmptyValDef
                    EmptyValDef,
                    // empty body
                    List()
                  )
                )
              )
            ) if isJavaLangObject.isDefinedAt(parent) =>
      }: PartialFunction[Tree, Unit]
    }.isDefinedAt(clue(unpickle("empty_class/EmptyClass"))))
  }

  test("basic-import") {
    val importMatch: PartialFunction[Tree, Unit] = {
      case Import(_, List(ImportSelector(Ident(SimpleName("A")), EmptyTree, EmptyTree))) =>
    }
    assert(containsSubtree(clue(importMatch))(clue(unpickle("imports/Import"))))
  }

  test("multiple-imports") {
    val importMatch: PartialFunction[Tree, Unit] = {
      case Import(
            _,
            List(
              ImportSelector(Ident(SimpleName("A")), EmptyTree, EmptyTree),
              ImportSelector(Ident(SimpleName("B")), EmptyTree, EmptyTree)
            )
          ) =>
    }
    assert(containsSubtree(importMatch)(clue(unpickle("imports/MultipleImports"))))
  }
  
  test("renamed-import") {
    val importMatch: PartialFunction[Tree, Unit] = {
      case Import(_, List(ImportSelector(Ident(SimpleName("A")), Ident(SimpleName("ClassA")), EmptyTree))) =>
    }
    assert(containsSubtree(importMatch)(clue(unpickle("imports/RenamedImport"))))
  }

  test("given-import") {
    val importMatch: PartialFunction[Tree, Unit] = {
      case Import(_, List(ImportSelector(Ident(EmptyTermName), EmptyTree, EmptyTree))) =>
    }
    assert(containsSubtree(importMatch)(clue(unpickle("imports/ImportGiven"))))
  }
}
