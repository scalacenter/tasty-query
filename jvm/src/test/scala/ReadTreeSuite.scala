import tastyquery.Contexts
import tastyquery.ast.Constants.{ClazzTag, Constant, IntTag, NullTag}
import tastyquery.ast.Names._
import tastyquery.ast.Symbols.Symbol
import tastyquery.ast.Trees._
import tastyquery.ast.Types.{AppliedType, ConstantType, TermRef, ThisType, TypeRef}
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
          _: SeqLiteral | _: AppliedTypeTree | _: TypeApply | _: This | _: Lambda | _: NamedArg | _: Super =>
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

  test("multiple-parameter-lists") {
    val tree = unpickle("simple_trees/MultipleParameterLists")
    val methodMatch: StructureCheck = {
      case DefDef(
            SimpleName("threeParameterLists"),
            Nil,
            List(
              ValDef(SimpleName("x"), _, _) :: Nil,
              ValDef(SimpleName("y"), _, _) :: ValDef(SimpleName("z"), _, _) :: Nil,
              ValDef(SimpleName("last"), _, _) :: Nil
            ),
            _,
            _
          ) =>
    }
    assert(containsSubtree(methodMatch)(clue(tree)))
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

  test("match-case-class") {
    val tree = unpickle("simple_trees/PatternMatchingOnCaseClass")

    val guardWithAlternatives: StructureCheck = {
      case CaseDef(
            Typed(
              Unapply(
                Select(Ident(SimpleName("FirstCase")), SignedName(SimpleName("unapply"), _)),
                Nil,
                List(Bind(SimpleName("x"), Ident(Wildcard)))
              ),
              _
            ),
            EmptyTree,
            body: Block
          ) =>
    }
    assert(containsSubtree(guardWithAlternatives)(clue(tree)))
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

  test("try-catch") {
    val tree = unpickle("simple_trees/TryCatch")
    val tryMatch: StructureCheck = {
      case Try(
            _,
            CaseDef(Ident(Wildcard), EmptyTree, Block(Nil, Literal(Constant(0)))) :: Nil,
            Block(Nil, Literal(Constant(())))
          ) =>
    }
    assert(containsSubtree(tryMatch)(clue(tree)))
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

  test("construct-inner-class") {
    val tree = unpickle("simple_trees/InnerClass")

    val innerInstanceMatch: StructureCheck = {
      case ValDef(
            SimpleName("innerInstance"),
            // "Inner" inside THIS
            TypeTree(TypeRef(ThisType(_), Symbol(TypeName(SimpleName("Inner"))))),
            Apply(Select(New(Ident(TypeName(SimpleName("Inner")))), _), Nil)
          ) =>
    }
    assert(containsSubtree(innerInstanceMatch)(clue(tree)))
  }

  test("type-application") {
    val tree = unpickle("simple_trees/TypeApply")

    val applyMatch: StructureCheck = {
      case Apply(
            // apply[Int]
            TypeApply(
              Select(Ident(SimpleName("Seq")), SignedName(SimpleName("apply"), _)),
              TypeTree(TypeRef(_, TypeName(SimpleName("Int")))) :: Nil
            ),
            Typed(SeqLiteral(Literal(Constant(1)) :: Nil, _), _) :: Nil
          ) =>
    }
    assert(containsSubtree(applyMatch)(clue(tree)))
  }

  test("final") {
    val tree = unpickle("simple_trees/Final")

    val constTypeMatch: StructureCheck = {
      case ValDef(SimpleName("Const"), TypeTree(ConstantType(Constant(1))), Literal(Constant(1))) =>
    }
    assert(containsSubtree(constTypeMatch)(clue(tree)))
  }

  test("var") {
    val tree = unpickle("simple_trees/Var")

    // var = val with a setter
    val valDefMatch: StructureCheck = {
      case ValDef(SimpleName("x"), TypeTree(TypeRef(_, TypeName(SimpleName("Int")))), Literal(Constant(1))) =>
    }
    val setterMatch: StructureCheck = {
      case DefDef(
            SimpleName("x_="),
            Nil,
            List(ValDef(SimpleName("x$1"), _, _) :: Nil),
            TypeTree(TypeRef(_, TypeName(SimpleName("Unit")))),
            Literal(Constant(()))
          ) =>
    }
    assert(containsSubtree(valDefMatch)(clue(tree)))
    assert(containsSubtree(setterMatch)(clue(tree)))

    // x = 2
    val assignmentMatch: StructureCheck = {
      case Assign(Select(This(Some(Ident(TypeName(SimpleName("Var"))))), SimpleName("x")), Literal(Constant(2))) =>
    }
    assert(containsSubtree(assignmentMatch)(clue(tree)))
  }

  test("constructor-with-parameters") {
    val tree = unpickle("simple_trees/ConstructorWithParameters")
    val classWithParams: StructureCheck = {
      case Template(
            DefDef(
              SimpleName("<init>"),
              Nil,
              List(
                ValDef(SimpleName("local"), _, _),
                ValDef(SimpleName("theVal"), _, _),
                ValDef(SimpleName("theVar"), _, _),
                ValDef(SimpleName("privateVal"), _, _)
              ) :: Nil,
              _,
              _
            ),
            _,
            _,
            // TODO: check the modifiers (private, local etc) once they are read
            // constructor parameters are members
            List(
              ValDef(SimpleName("local"), _, _),
              ValDef(SimpleName("theVal"), _, _),
              ValDef(SimpleName("theVar"), _, _),
              ValDef(SimpleName("privateVal"), _, _),
              // setter for theVar
              DefDef(SimpleName("theVar_="), Nil, _ :: Nil, _, _)
            )
          ) =>
    }
    assert(containsSubtree(classWithParams)(clue(tree)))
  }

  test("use-given") {
    val tree = unpickle("simple_trees/UsingGiven")

    // given Int
    val givenDefinition: StructureCheck = {
      case ValDef(SimpleName("given_Int"), Ident(TypeName(SimpleName("Int"))), _) =>
    }
    assert(containsSubtree(givenDefinition)(clue(tree)))

    // def useGiven(using Int)
    // useGiven
    val withGiven: StructureCheck = {
      case Apply(
            Select(_, SignedName(SimpleName("useGiven"), _)),
            Select(This(Some(Ident(TypeName(SimpleName("UsingGiven"))))), SimpleName("given_Int")) :: Nil
          ) =>
    }
    assert(containsSubtree(withGiven)(clue(tree)))

    // useGiven(using 0)
    val explicitUsing: StructureCheck = {
      case Apply(Select(_, SignedName(SimpleName("useGiven"), _)), Literal(Constant(0)) :: Nil) =>
    }
    assert(containsSubtree(explicitUsing)(clue(tree)))
  }

  test("trait-with-parameter") {
    val tree = unpickle("simple_trees/TraitWithParameter")

    val traitMatch: StructureCheck = {
      case Template(
            DefDef(SimpleName("<init>"), Nil, List(ValDef(SimpleName("param"), _, _) :: Nil), _, EmptyTree),
            TypeTree(TypeRef(_, TypeName(SimpleName("Object")))) :: Nil,
            _,
            ValDef(SimpleName("param"), _, _) :: Nil
          ) =>
    }

  }

  test("extend-trait") {
    val tree = unpickle("simple_trees/ExtendsTrait")

    val classMatch: StructureCheck = {
      case Template(
            _,
            jlObject :: Ident(TypeName(SimpleName("AbstractTrait"))) :: Nil,
            _,
            // TODO: check the OVERRIDE modifer once modifiers are read
            DefDef(SimpleName("abstractMethod"), _, _, _, _) :: Nil
          ) if isJavaLangObject.isDefinedAt(jlObject) =>
    }
    assert(containsSubtree(classMatch)(clue(tree)))
  }

  test("lambda") {
    val tree = unpickle("simple_trees/Function")

    val functionLambdaMatch: StructureCheck = {
      case ValDef(
            SimpleName("functionLambda"),
            _,
            Block(
              List(DefDef(SimpleName("$anonfun"), Nil, List(ValDef(SimpleName("x"), _, _)) :: Nil, _, _)),
              // a lambda is simply a wrapper around a DefDef, defined in the same block. Its type is a function type,
              // therefore not specified (left as EmptyTree)
              Lambda(Ident(SimpleName("$anonfun")), EmptyTree)
            )
          ) =>
    }
    assert(containsSubtree(functionLambdaMatch)(clue(tree)))

    val SAMLambdaMatch: StructureCheck = {
      case ValDef(
            SimpleName("samLambda"),
            _,
            Block(
              List(DefDef(SimpleName("$anonfun"), Nil, List(Nil), _, _)),
              // the lambda's type is not just a function type, therefore specified
              Lambda(Ident(SimpleName("$anonfun")), TypeTree(TypeRef(_, TypeName(SimpleName("Runnable")))))
            )
          ) =>
    }
    assert(containsSubtree(SAMLambdaMatch)(clue(tree)))
  }

  test("eta-expansion") {
    val tree = unpickle("simple_trees/EtaExpansion")

    /*
    takesFunction(intMethod)
    the compiler generates a function which simply calls intMethod;
    this function is passed as the argument to takesFunction
     */
    val applicationMatch: StructureCheck = {
      case Apply(
            Select(This(Some(Ident(TypeName(SimpleName("EtaExpansion"))))), SignedName(SimpleName("takesFunction"), _)),
            Block(
              List(
                DefDef(
                  SimpleName("$anonfun"),
                  Nil,
                  List(ValDef(SimpleName("x"), _, _)) :: Nil,
                  _,
                  Apply(
                    Select(
                      This(Some(Ident(TypeName(SimpleName("EtaExpansion"))))),
                      SignedName(SimpleName("intMethod"), _)
                    ),
                    List(Ident(SimpleName("x")))
                  )
                )
              ),
              Lambda(Ident(SimpleName("$anonfun")), EmptyTree)
            ) :: Nil
          ) =>
    }
    assert(containsSubtree(applicationMatch)(clue(tree)))
  }

  test("partial-application") {
    val tree = unpickle("simple_trees/PartialApplication")

    // Partial application under the hood is defining a function which takes the remaining parameters
    // and calls the original function with fixed + remaining parameters
    val applicationMatch: StructureCheck = {
      case DefDef(
            SimpleName("partiallyApplied"),
            Nil,
            Nil,
            _,
            Block(
              List(
                DefDef(
                  SimpleName("$anonfun"),
                  Nil,
                  List(ValDef(SimpleName("second"), _, _)) :: Nil,
                  _,
                  Apply(
                    Apply(
                      Select(
                        This(Some(Ident(TypeName(SimpleName("PartialApplication"))))),
                        SignedName(SimpleName("withManyParams"), _)
                      ),
                      Literal(Constant(0)) :: Nil
                    ),
                    Ident(SimpleName("second")) :: Nil
                  )
                )
              ),
              Lambda(Ident(SimpleName("$anonfun")), EmptyTree)
            )
          ) =>
    }
    assert(containsSubtree(applicationMatch)(clue(tree)))
  }

  test("named-argument") {
    val tree = unpickle("simple_trees/NamedArgument")

    val withNamedArgumentApplication: StructureCheck = {
      case Apply(
            Select(This(Some(Ident(TypeName(SimpleName("NamedArgument"))))), SignedName(SimpleName("withNamed"), _)),
            List(Literal(Constant(0)), NamedArg(SimpleName("second"), Literal(Constant(1))))
          ) =>
    }
    assert(containsSubtree(withNamedArgumentApplication)(clue(tree)))
  }

  test("return") {
    val tree = unpickle("simple_trees/Return")

    val returnMatch: StructureCheck = { case Return(Literal(Constant(1)), Ident(SimpleName("withReturn"))) =>
    }
    assert(containsSubtree(returnMatch)(clue(tree)))
  }

  test("super") {
    val tree = unpickle("simple_trees/Super")

    val superMatch: StructureCheck = { case Super(This(None), None) =>
    }
    assert(containsSubtree(superMatch)(clue(tree)))

    val mixinSuper: StructureCheck = { case Super(This(None), Some(Ident(TypeName(SimpleName("Base"))))) =>
    }
    assert(containsSubtree(mixinSuper)(clue(tree)))
  }

  test("type-member") {
    val tree = unpickle("simple_trees/TypeMember")

    val typeMember: StructureCheck = {
      case TypeDef(TypeName(SimpleName("TypeMember")), Ident(TypeName(SimpleName("Int")))) =>
    }
    assert(containsSubtree(typeMember)(clue(tree)))
  }
}
