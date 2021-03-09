import tastyquery.ast.Constants.Constant
import tastyquery.ast.Names._
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
      case Select(qualifier, _)          => rec(qualifier)
      case Apply(fun, args)              => rec(fun) || args.exists(rec)
      case New(tpt)                      => rec(tpt)
      case Block(stats, expr)            => stats.exists(rec) || rec(expr)
      case If(cond, thenPart, elsePart)  => rec(cond) || rec(thenPart) || rec(elsePart)
      case Match(selector, cases)        => rec(selector) || cases.exists(rec)
      case Alternative(trees)            => trees.exists(rec)
      case CaseDef(pattern, guard, body) => rec(pattern) || rec(guard) || rec(body)
      case While(cond, body)             => rec(cond) || rec(body)

      // Nowhere to walk
      case ImportSelector(_, _, _) | Import(_, _) | Ident(_) | TypeTree(_) | Literal(_) | EmptyTree => false
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

  test("identity-method") {
    val identityMatch: PartialFunction[Tree, Unit] = {
      case DefDef(
            SimpleName("id"),
            // no type params
            List(),
            // one param -- x: Int
            List(List(ValDef(SimpleName("x"), Ident(TypeName(SimpleName("Int"))), EmptyTree))),
            Ident(TypeName(SimpleName("Int"))),
            // TODO: when the symbols are correctly created, this should be x
            Ident(_)
          ) =>
    }
    assert(containsSubtree(identityMatch)(clue(unpickle("simple_trees/IdentityMethod"))))
  }

  test("constants") {
    val tree = unpickle("simple_trees/Constants")
    val unitConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("unitVal"), _, Literal(Constant(()))) =>
    }
    assert(containsSubtree(unitConstMatch)(clue(tree)))

    val falseConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("falseVal"), _, Literal(Constant(false))) =>
    }
    assert(containsSubtree(falseConstMatch)(clue(tree)))

    val trueConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("trueVal"), _, Literal(Constant(true))) =>
    }
    assert(containsSubtree(trueConstMatch)(clue(tree)))

    val byteConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("byteVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(byteConstMatch)(clue(tree)))

    val shortConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("shortVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(shortConstMatch)(clue(tree)))

    val charConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("charVal"), _, Literal(Constant('a'))) =>
    }
    assert(containsSubtree(charConstMatch)(clue(tree)))

    val intConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("intVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(intConstMatch)(clue(tree)))

    val longConstMatch: PartialFunction[Tree, Unit] = { case ValDef(SimpleName("longVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(longConstMatch)(clue(tree)))

    val floatConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("floatVal"), _, Literal(Constant(1.1f))) =>
    }
    assert(containsSubtree(floatConstMatch)(clue(tree)))

    val doubleConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("doubleVal"), _, Literal(Constant(1.1d))) =>
    }
    assert(containsSubtree(doubleConstMatch)(clue(tree)))

    val stringConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("stringVal"), _, Literal(Constant("string"))) =>
    }
    assert(containsSubtree(stringConstMatch)(clue(tree)))

    val nullConstMatch: PartialFunction[Tree, Unit] = {
      case ValDef(SimpleName("nullVal"), _, Literal(Constant(null))) =>
    }
    assert(containsSubtree(nullConstMatch)(clue(tree)))
  }

  test("if") {
    val ifMatch: PartialFunction[Tree, Unit] = {
      case If(
            // TODO: when the symbols are correctly created, all Ident(_) should be Ident(x)
            Apply(Select(Ident(_), SignedName(SimpleName("<"), _)), List(Literal(Constant(0)))),
            Select(Ident(_), SimpleName("unary_-")),
            Ident(_)
          ) =>
    }
    val tree = unpickle("simple_trees/If")
    assert(containsSubtree(ifMatch)(clue(tree)))
  }

  test("block") {
    val blockMatch: PartialFunction[Tree, Unit] = {
      case Block(
            List(ValDef(SimpleName("a"), _, Literal(Constant(1))), ValDef(SimpleName("b"), _, Literal(Constant(2)))),
            Literal(Constant(()))
          ) =>
    }
    val tree = unpickle("simple_trees/Block")
    assert(containsSubtree(blockMatch)(clue(tree)))
  }

  test("empty-infinite-while") {
    val whileMatch: PartialFunction[Tree, Unit] = {
      case While(Literal(Constant(true)), Block(Nil, Literal(Constant(())))) =>
    }
    val tree = unpickle("simple_trees/While")
    assert(containsSubtree(whileMatch)(clue(tree)))
  }

  test("match") {
    val tree = unpickle("simple_trees/Match")

    val matchStructure: PartialFunction[Tree, Unit] = {
      case Match(Ident(_), cases) if cases.length == 6 =>
    }
    assert(containsSubtree(matchStructure)(clue(tree)))

    val simpleGuard: PartialFunction[Tree, Unit] = { case CaseDef(Literal(Constant(0)), EmptyTree, body: Block) =>
    }
    assert(containsSubtree(simpleGuard)(clue(tree)))

    val guardWithAlternatives: PartialFunction[Tree, Unit] = {
      case CaseDef(
            Alternative(List(Literal(Constant(1)), Literal(Constant(-1)), Literal(Constant(2)))),
            EmptyTree,
            body: Block
          ) =>
    }
    assert(containsSubtree(guardWithAlternatives)(clue(tree)))

    val guardAndCondition: PartialFunction[Tree, Unit] = {
      case CaseDef(
            Literal(Constant(7)),
            Apply(Select(_, SignedName(SimpleName("=="), _)), Literal(Constant(7)) :: Nil),
            body: Block
          ) =>
    }
    assert(containsSubtree(guardAndCondition)(clue(tree)))

    val alternativesAndCondition: PartialFunction[Tree, Unit] = {
      case CaseDef(
            Alternative(List(Literal(Constant(3)), Literal(Constant(4)), Literal(Constant(5)))),
            Apply(Select(_, SignedName(SimpleName("<"), _)), Literal(Constant(5)) :: Nil),
            body: Block
          ) =>
    }
    assert(containsSubtree(alternativesAndCondition)(clue(tree)))

    val defaultWithCondition: PartialFunction[Tree, Unit] = {
      case CaseDef(
            Ident(Wildcard),
            Apply(
              Select(
                Apply(Select(_, SignedName(SimpleName("%"), _)), Literal(Constant(2)) :: Nil),
                SignedName(SimpleName("=="), _)
              ),
              Literal(Constant(0)) :: Nil
            ),
            body: Block
          ) =>
    }
    assert(containsSubtree(defaultWithCondition)(clue(tree)))

    val default: PartialFunction[Tree, Unit] = { case CaseDef(Ident(Wildcard), EmptyTree, body: Block) =>
    }
    assert(containsSubtree(default)(clue(tree)))
  }
}
