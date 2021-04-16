import tastyquery.Contexts
import tastyquery.ast.Constants.{ClazzTag, Constant, IntTag, NullTag}
import tastyquery.ast.Names._
import tastyquery.ast.Symbols.Symbol
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{AppliedType, TermRef, TypeRef}
import tastyquery.reader.TastyUnpickler

import java.nio.file.{Files, Paths}

class ReadTreeSuite extends munit.FunSuite {
  type StructureCheck = PartialFunction[Tree, Unit]
  val ResourceProperty = "test-resources"

  def unpickle(filename: String): Tree = {
    val resourcePath = getResourcePath(filename)
    val bytes        = Files.readAllBytes(Paths.get(resourcePath))
    val unpickler    = new TastyUnpickler(bytes)
    unpickler.unpickle(new TastyUnpickler.TreeSectionUnpickler()).get.unpickle (using Contexts.empty).head
  }

  def getResourcePath(name: String): String =
    s"${System.getProperty(ResourceProperty)}/$name.tasty"

  def containsSubtree(p: StructureCheck)(t: Tree): Boolean = {
    def rec(t: Tree): Boolean = containsSubtree(p)(t)
    p.isDefinedAt(t) || (t match {
      case PackageDef(_, stats) => stats.exists(rec)
      case TypeDef(_, rhs)      => rec(rhs)
      case Template(constr, parents, self, body) =>
        rec(constr) || rec(self) || parents.exists(rec) || body.exists(rec)
      case ValDef(_, tpt, rhs) => rec(tpt) || rec(rhs)
      case DefDef(_, tparams, vparamss, tpt, rhs) =>
        tparams.exists(rec) || vparamss.flatten.exists(rec) || rec(tpt) || rec(rhs)
      case Select(qualifier, _)         => rec(qualifier)
      case Apply(fun, args)             => rec(fun) || args.exists(rec)
      case Block(stats, expr)           => stats.exists(rec) || rec(expr)
      case If(cond, thenPart, elsePart) => rec(cond) || rec(thenPart) || rec(elsePart)
      case Match(selector, cases)       => rec(selector) || cases.exists(rec)

      // Trees, inside which the existing tests do not descend
      case _: New | _: Alternative | _: CaseDef | _: SingletonTypeTree | _: While | _: Assign | _: Throw | _: Typed |
          _: SeqLiteral | _: AppliedTypeTree =>
        false

      // Nowhere to walk
      case _: ImportSelector | _: Import | Ident(_) | TypeTree(_) | Literal(_) | EmptyTree => false
    })
  }

  val isJavaLangObject: StructureCheck = {
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
                    DefDef(SimpleName("<init>"), Nil, List(Nil), TypeTree(_), EmptyTree),
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
      }: StructureCheck
    }.isDefinedAt(clue(unpickle("empty_class/EmptyClass"))))
  }

  test("basic-import") {
    val importMatch: StructureCheck = {
      case Import(_, List(ImportSelector(Ident(SimpleName("A")), EmptyTree, EmptyTree))) =>
    }
    assert(containsSubtree(clue(importMatch))(clue(unpickle("imports/Import"))))
  }

  test("multiple-imports") {
    val importMatch: StructureCheck = {
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
    val importMatch: StructureCheck = {
      case Import(_, List(ImportSelector(Ident(SimpleName("A")), Ident(SimpleName("ClassA")), EmptyTree))) =>
    }
    assert(containsSubtree(importMatch)(clue(unpickle("imports/RenamedImport"))))
  }

  test("given-import") {
    val importMatch: StructureCheck = {
      case Import(_, List(ImportSelector(Ident(EmptyTermName), EmptyTree, EmptyTree))) =>
    }
    assert(containsSubtree(importMatch)(clue(unpickle("imports/ImportGiven"))))
  }

  test("identity-method") {
    val identityMatch: StructureCheck = {
      case DefDef(
            SimpleName("id"),
            // no type params
            List(),
            // one param -- x: Int
            List(List(ValDef(SimpleName("x"), Ident(TypeName(SimpleName("Int"))), EmptyTree))),
            Ident(TypeName(SimpleName("Int"))),
            Ident(SimpleName("x"))
          ) =>
    }
    assert(containsSubtree(identityMatch)(clue(unpickle("simple_trees/IdentityMethod"))))
  }

  test("constants") {
    val tree = unpickle("simple_trees/Constants")
    val unitConstMatch: StructureCheck = { case ValDef(SimpleName("unitVal"), _, Literal(Constant(()))) =>
    }
    assert(containsSubtree(unitConstMatch)(clue(tree)))

    val falseConstMatch: StructureCheck = { case ValDef(SimpleName("falseVal"), _, Literal(Constant(false))) =>
    }
    assert(containsSubtree(falseConstMatch)(clue(tree)))

    val trueConstMatch: StructureCheck = { case ValDef(SimpleName("trueVal"), _, Literal(Constant(true))) =>
    }
    assert(containsSubtree(trueConstMatch)(clue(tree)))

    val byteConstMatch: StructureCheck = { case ValDef(SimpleName("byteVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(byteConstMatch)(clue(tree)))

    val shortConstMatch: StructureCheck = { case ValDef(SimpleName("shortVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(shortConstMatch)(clue(tree)))

    val charConstMatch: StructureCheck = { case ValDef(SimpleName("charVal"), _, Literal(Constant('a'))) =>
    }
    assert(containsSubtree(charConstMatch)(clue(tree)))

    val intConstMatch: StructureCheck = { case ValDef(SimpleName("intVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(intConstMatch)(clue(tree)))

    val longConstMatch: StructureCheck = { case ValDef(SimpleName("longVal"), _, Literal(Constant(1))) =>
    }
    assert(containsSubtree(longConstMatch)(clue(tree)))

    val floatConstMatch: StructureCheck = { case ValDef(SimpleName("floatVal"), _, Literal(Constant(1.1f))) =>
    }
    assert(containsSubtree(floatConstMatch)(clue(tree)))

    val doubleConstMatch: StructureCheck = { case ValDef(SimpleName("doubleVal"), _, Literal(Constant(1.1d))) =>
    }
    assert(containsSubtree(doubleConstMatch)(clue(tree)))

    val stringConstMatch: StructureCheck = { case ValDef(SimpleName("stringVal"), _, Literal(Constant("string"))) =>
    }
    assert(containsSubtree(stringConstMatch)(clue(tree)))

    val nullConstMatch: StructureCheck = { case ValDef(SimpleName("nullVal"), _, Literal(Constant(null))) =>
    }
    assert(containsSubtree(nullConstMatch)(clue(tree)))
  }

  test("if") {
    val ifMatch: StructureCheck = {
      case If(
            Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("<"), _)), List(Literal(Constant(0)))),
            Select(Ident(SimpleName("x")), SimpleName("unary_-")),
            Ident(SimpleName("x"))
          ) =>
    }
    val tree = unpickle("simple_trees/If")
    assert(containsSubtree(ifMatch)(clue(tree)))
  }

  test("block") {
    val blockMatch: StructureCheck = {
      case Block(
            List(ValDef(SimpleName("a"), _, Literal(Constant(1))), ValDef(SimpleName("b"), _, Literal(Constant(2)))),
            Literal(Constant(()))
          ) =>
    }
    val tree = unpickle("simple_trees/Block")
    assert(containsSubtree(blockMatch)(clue(tree)))
  }

  test("empty-infinite-while") {
    val whileMatch: StructureCheck = { case While(Literal(Constant(true)), Block(Nil, Literal(Constant(())))) =>
    }
    val tree = unpickle("simple_trees/While")
    assert(containsSubtree(whileMatch)(clue(tree)))
  }

  test("match") {
    val tree = unpickle("simple_trees/Match")

    val matchStructure: StructureCheck = {
      case Match(Ident(_), cases) if cases.length == 6 =>
    }
    assert(containsSubtree(matchStructure)(clue(tree)))

    val simpleGuard: StructureCheck = { case CaseDef(Literal(Constant(0)), EmptyTree, body: Block) =>
    }
    assert(containsSubtree(simpleGuard)(clue(tree)))

    val guardWithAlternatives: StructureCheck = {
      case CaseDef(
            Alternative(List(Literal(Constant(1)), Literal(Constant(-1)), Literal(Constant(2)))),
            EmptyTree,
            body: Block
          ) =>
    }
    assert(containsSubtree(guardWithAlternatives)(clue(tree)))

    val guardAndCondition: StructureCheck = {
      case CaseDef(
            Literal(Constant(7)),
            Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("=="), _)), Literal(Constant(7)) :: Nil),
            body: Block
          ) =>
    }
    assert(containsSubtree(guardAndCondition)(clue(tree)))

    val alternativesAndCondition: StructureCheck = {
      case CaseDef(
            Alternative(List(Literal(Constant(3)), Literal(Constant(4)), Literal(Constant(5)))),
            Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("<"), _)), Literal(Constant(5)) :: Nil),
            body: Block
          ) =>
    }
    assert(containsSubtree(alternativesAndCondition)(clue(tree)))

    val defaultWithCondition: StructureCheck = {
      case CaseDef(
            Ident(Wildcard),
            Apply(
              Select(
                Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("%"), _)), Literal(Constant(2)) :: Nil),
                SignedName(SimpleName("=="), _)
              ),
              Literal(Constant(0)) :: Nil
            ),
            body: Block
          ) =>
    }
    assert(containsSubtree(defaultWithCondition)(clue(tree)))

    val default: StructureCheck = { case CaseDef(Ident(Wildcard), EmptyTree, body: Block) =>
    }
    assert(containsSubtree(default)(clue(tree)))
  }

  test("assign") {
    val tree = unpickle("simple_trees/Assign")
    val assignBlockMatch: StructureCheck = {
      case Block(
            List(
              ValDef(SimpleName("y"), tpt, Literal(Constant(0))),
              Assign(Ident(SimpleName("y")), Ident(SimpleName("x")))
            ),
            Ident(SimpleName("x"))
          ) =>
    }
    assert(containsSubtree(assignBlockMatch)(clue(tree)))
  }

  test("throw") {
    val tree = unpickle("simple_trees/ThrowException")
    val throwMatch: StructureCheck = {
      case Throw(
            Apply(
              Select(New(Ident(TypeName(SimpleName("NullPointerException")))), SignedName(SimpleName("<init>"), _)),
              Nil
            )
          ) =>
    }
    assert(containsSubtree(throwMatch)(clue(tree)))
  }

  test("singletonType") {
    val tree = unpickle("simple_trees/SingletonType")
    val defDefWithSingleton: StructureCheck = {
      case DefDef(
            SimpleName("singletonReturnType"),
            Nil,
            List(List(_)),
            SingletonTypeTree(Ident(SimpleName("x"))),
            Ident(SimpleName("x"))
          ) =>
    }
    assert(containsSubtree(defDefWithSingleton)(clue(tree)))
  }

  test("defaultSelfType") {
    val tree = unpickle("simple_trees/ClassWithSelf")
    val selfDefMatch: StructureCheck = {
      case ValDef(SimpleName("self"), TypeTree(TypeRef(_, Symbol(TypeName(SimpleName("ClassWithSelf"))))), EmptyTree) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))
  }

  test("selfType") {
    val tree = unpickle("simple_trees/TraitWithSelf")
    val selfDefMatch: StructureCheck = {
      case ValDef(SimpleName("self"), Ident(TypeName(SimpleName("ClassWithSelf"))), EmptyTree) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))
  }

  test("fields") {
    val tree = unpickle("simple_trees/Field")

    val classFieldMatch: StructureCheck = {
      case ValDef(SimpleName("x"), Ident(TypeName(SimpleName("Field"))), Literal(c)) if c.tag == NullTag =>
    }
    assert(containsSubtree(classFieldMatch)(clue(tree)))

    val intFieldMatch: StructureCheck = {
      case ValDef(SimpleName("y"), Ident(TypeName(SimpleName("Int"))), Literal(c)) if c.value == 0 && c.tag == IntTag =>
    }
    assert(containsSubtree(intFieldMatch)(clue(tree)))
  }

  test("object") {
    val tree = unpickle("simple_trees/ScalaObject")

    val selfDefMatch: StructureCheck = {
      case ValDef(Wildcard, SingletonTypeTree(Ident(SimpleName("ScalaObject"))), EmptyTree) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))

    // check that the class constant from writeReplace is unpickled
    val classConstMatch: StructureCheck = {
      case Literal(c) if c.tag == ClazzTag =>
    }
    assert(containsSubtree(classConstMatch)(clue(tree)))
  }

  test("typed") {
    val tree = unpickle("simple_trees/Typed")

    val typedMatch: StructureCheck = {
      case Typed(Literal(c), Ident(TypeName(SimpleName("Int")))) if c.tag == IntTag && c.value == 1 =>
    }
    assert(containsSubtree(typedMatch)(clue(tree)))
  }

  test("repeated") {
    val tree = unpickle("simple_trees/Repeated")

    val typedRepeated: StructureCheck = {
      case Typed(
            SeqLiteral(
              Literal(c1) :: Literal(c2) :: Literal(c3) :: Nil,
              TypeTree(TypeRef(_, TypeName(SimpleName("Int"))))
            ),
            TypeTree(
              AppliedType(
                TypeRef(_, TypeName(SimpleName("<repeated>"))),
                TypeRef(_, TypeName(SimpleName("Int"))) :: Nil
              )
            )
          ) =>
    }
    assert(containsSubtree(typedRepeated)(clue(tree)))
  }

  test("applied-type-annot") {
    val tree = unpickle("simple_trees/AppliedTypeAnnotation")

    val valDefMatch: StructureCheck = {
      case ValDef(
            SimpleName("x"),
            AppliedTypeTree(Ident(TypeName(SimpleName("Option"))), Ident(TypeName(SimpleName("Int"))) :: Nil),
            Ident(SimpleName("None"))
          ) =>
    }
    assert(containsSubtree(valDefMatch)(clue(tree)))
  }
}
