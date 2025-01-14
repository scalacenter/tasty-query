package tastyquery

import scala.concurrent.ExecutionContext.Implicits.global

import munit.{Location, TestOptions}

import tastyquery.Annotations.*
import tastyquery.Contexts.*
import tastyquery.Constants.{ClazzTag, Constant, IntTag, NullTag}
import tastyquery.Modifiers.*
import tastyquery.Names.*
import tastyquery.Symbols.*
import tastyquery.Traversers.*
import tastyquery.Trees.*
import tastyquery.Types.*

import TestUtils.*

class ReadTreeSuite extends RestrictedUnpicklingSuite {
  type StructureCheck = PartialFunction[Tree, Unit]
  type TypeStructureCheck = PartialFunction[Type, Unit]

  def containsSubtree(p: StructureCheck)(t: Tree): Boolean =
    object finder extends TreeTraverser:
      var found = false

      override def traverse(tree: Tree): Unit =
        if !found then
          if p.isDefinedAt(tree) then found = true
          else super.traverse(tree)
      end traverse
    end finder

    finder.traverse(t)
    finder.found
  end containsSubtree

  private object SimpleIdent:
    def unapply(ident: Ident): Option[String] = ident match
      case Ident(SimpleName(nameStr)) => Some(nameStr)
      case _                          => None
  end SimpleIdent

  private object SimpleTypeIdent:
    def unapply(ident: TypeIdent): Option[String] = ident match
      case TypeIdent(SimpleTypeName(nameStr)) => Some(nameStr)
      case _                                  => None
  end SimpleTypeIdent

  private object SymbolWithName:
    def unapply(sym: Symbol): Some[sym.name.type] = Some(sym.name)

  private object PackageWithFullName:
    def unapplySeq(sym: PackageSymbol): Option[List[Name]] = Some(sym.fullName.path)

  private object ScalaPackageRef:
    def unapply(tree: PackageRef): Boolean = tree.fullyQualifiedName.path == List(termName("scala"))

  private object PredefRef:
    def unapply(tree: TermRef): Boolean = tree match
      case TermRefInternal(ScalaPackageRef(), SimpleName("Predef")) => true
      case _                                                        => false

  private object ScalaCollImmutablePackageRef:
    def unapply(tree: PackageRef): Boolean =
      tree.fullyQualifiedName.path == List(termName("scala"), termName("collection"), termName("immutable"))

  private object SimpleTreesPackageRef:
    def unapply(tree: PackageRef): Boolean = tree.fullyQualifiedName.path == List(termName("simple_trees"))

  private type AnyDesignator = Symbol | Name | LookupIn | LookupTypeIn | Scala2ExternalSymRef

  private object TypeRefInternal:
    def unapply(tpe: TypeRef): Some[(Prefix, AnyDesignator)] = Some((tpe.prefix, tpe.designatorInternal))

  private object TermRefInternal:
    def unapply(tpe: TermRef): Some[(Prefix, AnyDesignator)] = Some((tpe.prefix, tpe.designatorInternal))

  private object NothingAnyTypeBoundsTree:
    def unapply(tree: ExplicitTypeBoundsTree): Boolean = tree match
      case ExplicitTypeBoundsTree(
            TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Nothing"))),
            TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Any")))
          ) =>
        true
      case _ =>
        false
  end NothingAnyTypeBoundsTree

  private object NothingAnyTypeBounds:
    def unapply(bounds: AbstractTypeBounds): Boolean = bounds match
      case AbstractTypeBounds(
            TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Nothing")),
            TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Any"))
          ) =>
        true
      case _ =>
        false
  end NothingAnyTypeBounds

  /** Extractors for `Type`s.
    *
    * "`ty`" stands for "type", but we make it very short not to clutter the
    * actual tests below.
    */
  private object ty:
    object PackageRef:
      def unapply(tpe: Types.PackageRef): Some[PackageFullName] = Some(tpe.fullyQualifiedName)

    object AppliedType:
      def unapply(tpe: Types.AppliedType): (Type, List[TypeOrWildcard]) = (tpe.tycon, tpe.args)

    object ThisType:
      def unapply(tpe: Types.ThisType): Some[TypeRef] = Some(tpe.tref)

    object SuperType:
      def unapply(tpe: Types.SuperType): (Type, Option[Type]) = (tpe.thistpe, tpe.explicitSupertpe)

    object ConstantType:
      def unapply(tpe: Types.ConstantType): Some[Constant] = Some(tpe.value)

    object AnnotatedType:
      def unapply(tpe: Types.AnnotatedType): (Type, Annotation) = (tpe.typ, tpe.annotation)

    object Annotation:
      def unapply(annot: Annotations.Annotation): Some[Tree] = Some(annot.tree)

    object ByNameType:
      def unapply(tpe: Types.ByNameType): Some[Type] = Some(tpe.resultType)

    object RepeatedType:
      def unapply(tpe: Types.RepeatedType): Some[Type] = Some(tpe.elemType)

    object OrType:
      def unapply(tpe: Types.OrType): (Type, Type) = (tpe.first, tpe.second)

    object AndType:
      def unapply(tpe: Types.AndType): (Type, Type) = (tpe.first, tpe.second)

    object TypeRefinement:
      def unapply(tpe: Types.TypeRefinement): (Type, Name, TypeBounds) =
        (tpe.parent, tpe.refinedName, tpe.refinedBounds)

    object TermRefinement:
      def unapply(tpe: Types.TermRefinement): (Type, Name, TypeOrMethodic) =
        (tpe.parent, tpe.refinedName, tpe.refinedType)

    object WildcardTypeArg:
      def unapply(tpe: Types.WildcardTypeArg): Some[TypeBounds] = Some(tpe.bounds)

    object MatchType:
      def unapply(tpe: Types.MatchType): (Type, Type, List[MatchTypeCase]) = (tpe.bound, tpe.scrutinee, tpe.cases)

    object MatchTypeCase:
      def unapply(tpe: Types.MatchTypeCase): (List[Type], Type, Type) = (tpe.paramRefs, tpe.pattern, tpe.result)

    object PolyType:
      def unapply(tpe: Types.PolyType): (List[(TypeName, TypeBounds)], TypeOrMethodic) =
        (tpe.paramNames.zip(tpe.paramTypeBounds), tpe.resultType)

    object MethodType:
      def unapply(tpe: Types.MethodType): (List[(TermName, Type)], TypeOrMethodic) =
        (tpe.paramNames.zip(tpe.paramTypes), tpe.resultType)

    object TypeLambda:
      def unapply(tpe: Types.TypeLambda): (List[Type], Type) = (tpe.paramRefs, tpe.resultType)
  end ty

  val isJavaLangObject: StructureCheck = {
    case Apply(
          Select(
            New(
              TypeWrapper(
                TypeRefInternal(
                  ty.PackageRef(PackageFullName(List(SimpleName("java"), SimpleName("lang")))),
                  SimpleTypeName("Object")
                )
              )
            ),
            SignedName(SimpleName("<init>"), _, _)
          ),
          List()
        ) =>
  }

  def testUnpickleTopLevel(name: String, rootSymbolPath: String)(using Location)(
    body: Contexts.Context ?=> Tree => Unit
  ): Unit =
    testUnpickleTopLevel(new TestOptions(name), rootSymbolPath)(body)
  end testUnpickleTopLevel

  def testUnpickleTopLevel(testOptions: TestOptions, rootSymbolPath: String)(
    using Location
  )(body: Contexts.Context ?=> Tree => Unit): Unit =
    test(testOptions) {
      for (base, tree) <- findTopLevelTasty(rootSymbolPath)() yield body(using base)(tree)
    }
  end testUnpickleTopLevel

  def testUnpickle(name: String, rootSymbolPath: String)(using Location)(
    body: Contexts.Context ?=> ClassDef => Unit
  ): Unit =
    testUnpickle(new TestOptions(name), rootSymbolPath)(body)
  end testUnpickle

  def testUnpickle(testOptions: TestOptions, rootSymbolPath: String)(
    using Location
  )(body: Contexts.Context ?=> ClassDef => Unit): Unit =
    test(testOptions) {
      for ctx <- getUnpicklingContext(rootSymbolPath) yield
        given Context = ctx
        val cls = findTopLevelClassOrModuleClass(rootSymbolPath)
        val tree = cls.tree.getOrElse {
          fail(s"Missing tasty for $rootSymbolPath, $cls")
        }
        body(tree)
    }
  end testUnpickle

  testUnpickleTopLevel("empty-class", "empty_class.EmptyClass") { tree =>
    assert({
      {
        case PackageDef(
              s @ SymbolWithName(SimpleName("empty_class")),
              List(
                ClassDef(
                  SimpleTypeName("EmptyClass"),
                  Template(
                    // default constructor: no type params, no arguments, empty body
                    DefDef(
                      SimpleName("<init>"),
                      Left(Nil) :: Nil,
                      TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Unit"))),
                      None,
                      _
                    ),
                    // a single parent -- java.lang.Object
                    List(parent: Apply),
                    // self not specified
                    None,
                    // empty body
                    List()
                  ),
                  _
                )
              )
              // tree of package symbols is never set, because one package symbol corresponds to multiple trees
              // (defined in different files)
            ) if isJavaLangObject.isDefinedAt(parent) && s.tree.isEmpty =>
      }: StructureCheck
    }.isDefinedAt(clue(tree)))
  }

  testUnpickleTopLevel("nested-packages", "simple_trees.nested.InNestedPackage") { tree =>
    val nestedPackages: StructureCheck = {
      case PackageDef(
            SymbolWithName(SimpleName("simple_trees")),
            List(PackageDef(PackageWithFullName(SimpleName("simple_trees"), SimpleName("nested")), _))
          ) =>
    }

    assert(containsSubtree(nestedPackages)(clue(tree)))
  }

  testUnpickleTopLevel("qualified-nested-package", "simple_trees.nested.InQualifiedNestedPackage") { tree =>
    val packageCheck: StructureCheck = {
      case PackageDef(PackageWithFullName(SimpleName("simple_trees"), SimpleName("nested")), _) =>
    }

    assert(containsSubtree(packageCheck)(clue(tree)))
  }

  testUnpickleTopLevel("basic-import", "imports.Import") { tree =>
    val importMatch: StructureCheck = {
      case Import(_, List(ImportSelector(ImportIdent(SimpleName("A")), None, None))) =>
    }
    assert(containsSubtree(clue(importMatch))(clue(tree)))
  }

  testUnpickleTopLevel("multiple-imports", "imports.MultipleImports") { tree =>
    val importMatch: StructureCheck = {
      case Import(
            Ident(SimpleName("imported_files")),
            List(
              ImportSelector(ImportIdent(SimpleName("A")), None, None),
              ImportSelector(ImportIdent(SimpleName("B")), None, None)
            )
          ) =>
    }
    assert(containsSubtree(importMatch)(clue(tree)))
  }

  testUnpickleTopLevel("renamed-import", "imports.RenamedImport") { tree =>
    val importMatch: StructureCheck = {
      case Import(
            Ident(SimpleName("imported_files")),
            List(ImportSelector(ImportIdent(SimpleName("A")), Some(ImportIdent(SimpleName("ClassA"))), None))
          ) =>
    }
    assert(containsSubtree(importMatch)(clue(tree)))

    val qualThisPackageImportMatch: StructureCheck = {
      case Import(
            This(TypeIdent(SimpleTypeName("imports"))),
            List(
              ImportSelector(
                ImportIdent(SimpleName("ClassInSameFile")),
                Some(ImportIdent(SimpleName("RenamedClassInSameFile"))),
                None
              )
            )
          ) =>
    }
    assert(containsSubtree(qualThisPackageImportMatch)(clue(tree)))
  }

  testUnpickleTopLevel("given-import", "imports.ImportGiven") { tree =>
    val importMatch: StructureCheck = {
      // A given import selector has an empty name
      case Import(
            // TODO: SELECTtpt?
            Select(Ident(SimpleName("imported_files")), SimpleName("Givens")),
            List(ImportSelector(ImportIdent(nme.EmptyTermName), None, None))
          ) =>
    }
    assert(containsSubtree(importMatch)(clue(tree)))
  }

  testUnpickleTopLevel("given-bounded-import", "imports.ImportGivenWithBound") { tree =>
    val importMatch: StructureCheck = {
      // A given import selector has an empty name
      case Import(
            // TODO: SELECTtpt?
            Select(Ident(SimpleName("imported_files")), SimpleName("Givens")),
            ImportSelector(ImportIdent(nme.EmptyTermName), None, Some(TypeIdent(SimpleTypeName("A")))) :: Nil
          ) =>
    }
    assert(containsSubtree(importMatch)(clue(tree)))
  }

  testUnpickle("export", "simple_trees.Export") { tree =>
    val simpleExport: StructureCheck = {
      case Export(
            Select(This(TypeIdent(SimpleTypeName("Export"))), SimpleName("first")),
            ImportSelector(ImportIdent(SimpleName("status")), None, None) :: Nil
          ) =>
    }
    assert(containsSubtree(simpleExport)(clue(tree)))

    val omittedAndWildcardExport: StructureCheck = {
      case Export(
            Select(This(TypeIdent(SimpleTypeName("Export"))), SimpleName("second")),
            // An omitting selector is simply a rename to _
            ImportSelector(ImportIdent(SimpleName("status")), Some(ImportIdent(nme.Wildcard)), None) ::
            ImportSelector(ImportIdent(nme.Wildcard), None, None) :: Nil
          ) =>
    }
    assert(containsSubtree(omittedAndWildcardExport)(clue(tree)))

    val givenExport: StructureCheck = {
      case Export(
            Select(This(TypeIdent(SimpleTypeName("Export"))), SimpleName("givens")),
            // A given selector has an empty name
            ImportSelector(ImportIdent(nme.EmptyTermName), None, Some(TypeIdent(SimpleTypeName("AnyRef")))) :: Nil
          ) =>
    }
    assert(containsSubtree(givenExport)(clue(tree)))
  }

  testUnpickle("identity-method", "simple_trees.IdentityMethod") { tree =>
    val identityMatch: StructureCheck = {
      case DefDef(
            SimpleName("id"),
            // no type params, one param -- x: Int
            List(Left(List(defTree @ ValDef(SimpleName("x"), TypeIdent(SimpleTypeName("Int")), None, valSymbol)))),
            TypeIdent(SimpleTypeName("Int")),
            Some(Ident(SimpleName("x"))),
            defSymbol
          ) if valSymbol.tree.contains(defTree) =>
    }
    assert(containsSubtree(identityMatch)(clue(tree)))
  }

  testUnpickle("multiple-parameter-lists", "simple_trees.MultipleParameterLists") { tree =>
    val methodMatch: StructureCheck = {
      case DefDef(
            SimpleName("threeParameterLists"),
            List(
              Left(List(ValDef(SimpleName("x"), _, _, _))),
              Left(List(ValDef(SimpleName("y"), _, _, _), ValDef(SimpleName("z"), _, _, _))),
              Left(List(ValDef(SimpleName("last"), _, _, _)))
            ),
            _,
            _,
            _
          ) =>
    }
    assert(containsSubtree(methodMatch)(clue(tree)))
  }

  testUnpickle("constants", "simple_trees.Constants") { tree =>
    val unitConstMatch: StructureCheck = { case ValDef(SimpleName("unitVal"), _, Some(Literal(Constant(()))), _) =>
    }
    assert(containsSubtree(unitConstMatch)(clue(tree)))

    val falseConstMatch: StructureCheck = { case ValDef(SimpleName("falseVal"), _, Some(Literal(Constant(false))), _) =>
    }
    assert(containsSubtree(falseConstMatch)(clue(tree)))

    val trueConstMatch: StructureCheck = { case ValDef(SimpleName("trueVal"), _, Some(Literal(Constant(true))), _) =>
    }
    assert(containsSubtree(trueConstMatch)(clue(tree)))

    val byteConstMatch: StructureCheck = { case ValDef(SimpleName("byteVal"), _, Some(Literal(Constant(1))), _) =>
    }
    assert(containsSubtree(byteConstMatch)(clue(tree)))

    val shortConstMatch: StructureCheck = { case ValDef(SimpleName("shortVal"), _, Some(Literal(Constant(1))), _) =>
    }
    assert(containsSubtree(shortConstMatch)(clue(tree)))

    val charConstMatch: StructureCheck = { case ValDef(SimpleName("charVal"), _, Some(Literal(Constant('a'))), _) =>
    }
    assert(containsSubtree(charConstMatch)(clue(tree)))

    val intConstMatch: StructureCheck = { case ValDef(SimpleName("intVal"), _, Some(Literal(Constant(1))), _) =>
    }
    assert(containsSubtree(intConstMatch)(clue(tree)))

    val longConstMatch: StructureCheck = { case ValDef(SimpleName("longVal"), _, Some(Literal(Constant(1))), _) =>
    }
    assert(containsSubtree(longConstMatch)(clue(tree)))

    val floatConstMatch: StructureCheck = { case ValDef(SimpleName("floatVal"), _, Some(Literal(Constant(1.5f))), _) =>
    }
    assert(containsSubtree(floatConstMatch)(clue(tree)))

    val doubleConstMatch: StructureCheck = {
      case ValDef(SimpleName("doubleVal"), _, Some(Literal(Constant(1.1d))), _) =>
    }
    assert(containsSubtree(doubleConstMatch)(clue(tree)))

    val stringConstMatch: StructureCheck = {
      case ValDef(SimpleName("stringVal"), _, Some(Literal(Constant("string"))), _) =>
    }
    assert(containsSubtree(stringConstMatch)(clue(tree)))

    val nullConstMatch: StructureCheck = { case ValDef(SimpleName("nullVal"), _, Some(Literal(Constant(null))), _) =>
    }
    assert(containsSubtree(nullConstMatch)(clue(tree)))
  }

  testUnpickle("if", "simple_trees.If") { tree =>
    val ifMatch: StructureCheck = {
      case If(
            Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("<"), _, _)), List(Literal(Constant(0)))),
            Select(Ident(SimpleName("x")), SimpleName("unary_-")),
            Ident(SimpleName("x"))
          ) =>
    }
    assert(containsSubtree(ifMatch)(clue(tree)))
  }

  testUnpickle("block", "simple_trees.Block") { tree =>
    val blockMatch: StructureCheck = {
      case Block(
            List(
              ValDef(SimpleName("a"), _, Some(Literal(Constant(1))), _),
              ValDef(SimpleName("b"), _, Some(Literal(Constant(2))), _)
            ),
            Literal(Constant(()))
          ) =>
    }
    assert(containsSubtree(blockMatch)(clue(tree)))
  }

  testUnpickle("empty-infinite-while", "simple_trees.While") { tree =>
    val whileMatch: StructureCheck = { case While(Literal(Constant(true)), Block(Nil, Literal(Constant(())))) =>
    }
    assert(containsSubtree(whileMatch)(clue(tree)))
  }

  testUnpickle("match", "simple_trees.Match") { tree =>
    val fTree = findTree(tree) { case fTree @ DefDef(SimpleName("f"), _, _, _, _) =>
      fTree
    }

    val matchStructure: StructureCheck = {
      case Match(Ident(_), cases) if cases.length == 6 =>
    }
    assert(containsSubtree(matchStructure)(clue(fTree)))

    val simpleGuard: StructureCheck = { case CaseDef(ExprPattern(Literal(Constant(0))), None, body: Block) =>
    }
    assert(containsSubtree(simpleGuard)(clue(fTree)))

    val guardWithAlternatives: StructureCheck = {
      case CaseDef(
            Alternative(
              List(
                ExprPattern(Literal(Constant(1))),
                ExprPattern(Literal(Constant(-1))),
                ExprPattern(Literal(Constant(2)))
              )
            ),
            None,
            body: Block
          ) =>
    }
    assert(containsSubtree(guardWithAlternatives)(clue(fTree)))

    val guardAndCondition: StructureCheck = {
      case CaseDef(
            ExprPattern(Literal(Constant(7))),
            Some(
              Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("=="), _, _)), Literal(Constant(7)) :: Nil)
            ),
            body: Block
          ) =>
    }
    assert(containsSubtree(guardAndCondition)(clue(fTree)))

    val alternativesAndCondition: StructureCheck = {
      case CaseDef(
            Alternative(
              List(
                ExprPattern(Literal(Constant(3))),
                ExprPattern(Literal(Constant(4))),
                ExprPattern(Literal(Constant(5)))
              )
            ),
            Some(Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("<"), _, _)), Literal(Constant(5)) :: Nil)),
            body: Block
          ) =>
    }
    assert(containsSubtree(alternativesAndCondition)(clue(fTree)))

    val defaultWithCondition: StructureCheck = {
      case CaseDef(
            WildcardPattern(_),
            Some(
              Apply(
                Select(
                  Apply(Select(Ident(SimpleName("x")), SignedName(SimpleName("%"), _, _)), Literal(Constant(2)) :: Nil),
                  SignedName(SimpleName("=="), _, _)
                ),
                Literal(Constant(0)) :: Nil
              )
            ),
            body: Block
          ) =>
    }
    assert(containsSubtree(defaultWithCondition)(clue(fTree)))

    val default: StructureCheck = { case CaseDef(WildcardPattern(_), None, body: Block) =>
    }
    assert(containsSubtree(default)(clue(fTree)))

    val gTree = findTree(tree) { case gTree @ DefDef(SimpleName("g"), _, _, _, _) =>
      gTree
    }

    val wildcardSequenceStructure: StructureCheck = {
      case Bind(
            SimpleName("elems"),
            TypeTest(
              WildcardPattern(
                ty.AppliedType(
                  TypeRefInternal(_, SimpleTypeName("Seq")),
                  List(TypeRefInternal(_, SimpleTypeName("Any")))
                )
              ),
              TypeWrapper(ty.RepeatedType(TypeRefInternal(_, SimpleTypeName("Any"))))
            ),
            _
          ) =>
    }
    assert(containsSubtree(wildcardSequenceStructure)(clue(gTree)))
  }

  testUnpickle("match-case-class", "simple_trees.PatternMatchingOnCaseClass") { tree =>
    val guardWithAlternatives: StructureCheck = {
      case CaseDef(
            TypeTest(
              Unapply(
                Select(Ident(SimpleName("FirstCase")), SignedName(SimpleName("unapply"), _, _)),
                Nil,
                List(bindTree @ Bind(SimpleName("x"), WildcardPattern(_), bindSymbol))
              ),
              _
            ),
            None,
            body: Block
          ) if bindSymbol.tree.contains(bindTree) =>
    }
    assert(containsSubtree(guardWithAlternatives)(clue(tree)))
  }

  testUnpickle("assign", "simple_trees.Assign") { tree =>
    val assignBlockMatch: StructureCheck = {
      case Block(
            List(
              ValDef(SimpleName("y"), tpt, Some(Literal(Constant(0))), _),
              Assign(Ident(SimpleName("y")), Ident(SimpleName("x")))
            ),
            Ident(SimpleName("x"))
          ) =>
    }
    assert(containsSubtree(assignBlockMatch)(clue(tree)))
  }

  testUnpickle("throw", "simple_trees.ThrowException") { tree =>
    val throwMatch: StructureCheck = {
      case Throw(
            Apply(
              Select(New(TypeIdent(SimpleTypeName("NullPointerException"))), SignedName(SimpleName("<init>"), _, _)),
              Nil
            )
          ) =>
    }
    assert(containsSubtree(throwMatch)(clue(tree)))
  }

  testUnpickle("try-catch", "simple_trees.TryCatch") { tree =>
    val tryMatch: StructureCheck = {
      case Try(
            _,
            CaseDef(WildcardPattern(_), None, Block(Nil, Literal(Constant(0)))) :: Nil,
            Some(Block(Nil, Literal(Constant(()))))
          ) =>
    }
    assert(containsSubtree(tryMatch)(clue(tree)))
  }

  testUnpickle("for-expressions", "simple_trees.ForExpressions") { tree =>
    val test1Def = findTree(tree) { case test1Def @ DefDef(SimpleName("test1"), _, _, _, _) =>
      test1Def
    }
    val matchTree = findTree(test1Def) { case mt: Match =>
      mt
    }

    val forExpressionMatch1: StructureCheck = {
      case CaseDef(
            Unapply(
              TypeApply(Select(Ident(SimpleName("Tuple2")), SignedName(SimpleName("unapply"), _, _)), _),
              Nil,
              List(
                Bind(SimpleName("i"), WildcardPattern(TypeRefInternal(_, SimpleTypeName("Int"))), _),
                WildcardPattern(TypeRefInternal(_, SimpleTypeName("String")))
              )
            ),
            None,
            _
          ) =>
    }
    assert(containsSubtree(forExpressionMatch1)(clue(matchTree)))
  }

  testUnpickle("singletonType", "simple_trees.SingletonType") { tree =>
    val defDefWithSingleton: StructureCheck = {
      case DefDef(
            SimpleName("singletonReturnType"),
            List(Left(List(_))),
            SingletonTypeTree(Ident(SimpleName("x"))),
            Some(Ident(SimpleName("x"))),
            _
          ) =>
    }
    assert(containsSubtree(defDefWithSingleton)(clue(tree)))
  }

  testUnpickle("defaultSelfType", "simple_trees.ClassWithSelf") { tree =>
    val selfDefMatch: StructureCheck = {
      case SelfDef(
            SimpleName("self"),
            TypeWrapper(TypeRefInternal(SimpleTreesPackageRef(), SymbolWithName(SimpleTypeName("ClassWithSelf"))))
          ) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))
  }

  testUnpickle("selfType", "simple_trees.TraitWithSelf") { tree =>
    val selfDefMatch: StructureCheck = { case SelfDef(SimpleName("self"), TypeIdent(SimpleTypeName("ClassWithSelf"))) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))
  }

  testUnpickle("fields", "simple_trees.Field") { tree =>
    val classFieldMatch: StructureCheck = {
      case ValDef(SimpleName("x"), TypeIdent(SimpleTypeName("Field")), Some(Literal(c)), _) if c.tag == NullTag =>
    }
    assert(containsSubtree(classFieldMatch)(clue(tree)))

    val intFieldMatch: StructureCheck = {
      case ValDef(SimpleName("y"), TypeIdent(SimpleTypeName("Int")), Some(Literal(c)), _)
          if c.value == 0 && c.tag == IntTag =>
    }
    assert(containsSubtree(intFieldMatch)(clue(tree)))
  }

  testUnpickle("object", "simple_trees.ScalaObject$") { tree =>
    val selfDefMatch: StructureCheck = {
      case SelfDef(nme.Wildcard, SingletonTypeTree(Ident(SimpleName("ScalaObject")))) =>
    }
    assert(containsSubtree(selfDefMatch)(clue(tree)))

    // check that the class constant from writeReplace is unpickled
    val classConstMatch: StructureCheck = {
      case Literal(c) if c.tag == ClazzTag =>
    }
    assert(containsSubtree(classConstMatch)(clue(tree)))

    val classDefMatch: StructureCheck = {
      case ClassDef(ObjectClassTypeName(SimpleTypeName("ScalaObject")), _, symbol) if symbol.isModuleClass =>
    }
    assert(containsSubtree(classDefMatch)(clue(tree)))
  }

  testUnpickle("typed", "simple_trees.Typed") { tree =>
    val typedMatch: StructureCheck = {
      case Typed(Literal(c), TypeIdent(SimpleTypeName("Int"))) if c.tag == IntTag && c.value == 1 =>
    }
    assert(containsSubtree(typedMatch)(clue(tree)))
  }

  testUnpickle("repeated", "simple_trees.Repeated") { tree =>
    val typedRepeated: StructureCheck = {
      case Typed(
            SeqLiteral(
              Literal(c1) :: Literal(c2) :: Literal(c3) :: Nil,
              TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int")))
            ),
            TypeWrapper(ty.RepeatedType(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int"))))
          ) =>
    }
    assert(containsSubtree(typedRepeated)(clue(tree)))
  }

  testUnpickle("applied-type-annot", "simple_trees.AppliedTypeAnnotation") { tree =>
    val valDefMatch: StructureCheck = {
      case ValDef(
            SimpleName("x"),
            AppliedTypeTree(TypeIdent(SimpleTypeName("Option")), TypeIdent(SimpleTypeName("Int")) :: Nil),
            Some(Ident(SimpleName("None"))),
            _
          ) =>
    }
    assert(containsSubtree(valDefMatch)(clue(tree)))
  }

  testUnpickle("construct-inner-class", "simple_trees.InnerClass") { tree =>
    val innerInstanceMatch: StructureCheck = {
      case ValDef(
            SimpleName("innerInstance"),
            // "Inner" inside THIS
            TypeWrapper(
              TypeRefInternal(
                ty.ThisType(TypeRefInternal(SimpleTreesPackageRef(), SymbolWithName(SimpleTypeName("InnerClass")))),
                SymbolWithName(SimpleTypeName("Inner"))
              )
            ),
            Some(Apply(Select(New(TypeIdent(SimpleTypeName("Inner"))), _), Nil)),
            _
          ) =>
    }
    assert(containsSubtree(innerInstanceMatch)(clue(tree)))
  }

  testUnpickle("type-application", "simple_trees.TypeApply") { tree =>
    val applyMatch: StructureCheck = {
      case Apply(
            // apply[Int]
            TypeApply(
              Select(Ident(SimpleName("Seq")), SignedName(SimpleName("apply"), _, _)),
              TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int"))) :: Nil
            ),
            Typed(SeqLiteral(Literal(Constant(1)) :: Nil, _), _) :: Nil
          ) =>
    }
    assert(containsSubtree(applyMatch)(clue(tree)))
  }

  testUnpickle("final", "simple_trees.Final") { tree =>
    val constTypeMatch: StructureCheck = {
      case ValDef(SimpleName("Const"), TypeWrapper(ty.ConstantType(Constant(1))), Some(Literal(Constant(1))), _) =>
    }
    assert(containsSubtree(constTypeMatch)(clue(tree)))
  }

  testUnpickle("var", "simple_trees.Var") { tree =>
    // var = val with a setter
    val valDefMatch: StructureCheck = {
      case defTree @ ValDef(
            SimpleName("x"),
            TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int"))),
            Some(Literal(Constant(1))),
            symbol
          ) if symbol.tree.contains(defTree) && symbol.kind == TermSymbolKind.Var && !symbol.isSetter =>
    }
    val setterMatch: StructureCheck = {
      case DefDef(
            SimpleName("x_="),
            Left(ValDef(SimpleName("x$1"), _, _, _) :: Nil) :: Nil,
            TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Unit"))),
            Some(Literal(Constant(()))),
            symbol
          ) if symbol.kind == TermSymbolKind.Def && symbol.isSetter =>
    }
    assert(containsSubtree(valDefMatch)(clue(tree)))
    assert(containsSubtree(setterMatch)(clue(tree)))

    // x = 2
    val assignmentMatch: StructureCheck = {
      case Assign(Select(This(TypeIdent(SimpleTypeName("Var"))), SimpleName("x")), Literal(Constant(2))) =>
    }
    assert(containsSubtree(assignmentMatch)(clue(tree)))
  }

  testUnpickle("constructor-with-parameters", "simple_trees.ConstructorWithParameters") { tree =>
    val classWithParams: StructureCheck = {
      case Template(
            DefDef(
              SimpleName("<init>"),
              List(
                Left(
                  List(
                    ValDef(SimpleName("local"), _, _, _),
                    ValDef(SimpleName("theVal"), _, _, _),
                    ValDef(SimpleName("theVar"), _, _, _),
                    ValDef(SimpleName("privateVal"), _, _, _)
                  )
                )
              ),
              _,
              _,
              _
            ),
            jlObject :: Nil,
            _,
            // TODO: check the modifiers (private, local etc) once they are read
            // constructor parameters are members
            List(
              ValDef(SimpleName("local"), _, _, _),
              ValDef(SimpleName("theVal"), _, _, _),
              ValDef(SimpleName("theVar"), _, _, _),
              ValDef(SimpleName("privateVal"), _, _, _),
              // setter for theVar
              DefDef(SimpleName("theVar_="), List(Left(List(_))), _, _, _)
            )
          ) =>
    }
    assert(containsSubtree(classWithParams)(clue(tree)))
  }

  testUnpickle("call-parent-ctor-with-defaults", "simple_trees.ChildCallsParentWithDefaultParameter") { tree =>
    val blockParent: StructureCheck = {
      case defTree @ ClassDef(
            SimpleTypeName("ChildCallsParentWithDefaultParameter"),
            Template(_, List(Block(_, _)), _, _),
            symbol
          ) if symbol.tree.contains(defTree) =>
    }
    assert(containsSubtree(blockParent)(clue(tree)))
  }

  testUnpickle("use-given", "simple_trees.UsingGiven") { tree =>
    // given Int
    val givenDefinition: StructureCheck = {
      case ValDef(SimpleName("given_Int"), TypeIdent(SimpleTypeName("Int")), _, _) =>
    }
    assert(containsSubtree(givenDefinition)(clue(tree)))

    // def useGiven(using Int)
    // useGiven
    val withGiven: StructureCheck = {
      case Apply(
            Select(This(TypeIdent(SimpleTypeName("UsingGiven"))), SignedName(SimpleName("useGiven"), _, _)),
            Select(This(TypeIdent(SimpleTypeName("UsingGiven"))), SimpleName("given_Int")) :: Nil
          ) =>
    }
    assert(containsSubtree(withGiven)(clue(tree)))

    // useGiven(using 0)
    val explicitUsing: StructureCheck = {
      case Apply(
            Select(This(TypeIdent(SimpleTypeName("UsingGiven"))), SignedName(SimpleName("useGiven"), _, _)),
            Literal(Constant(0)) :: Nil
          ) =>
    }
    assert(containsSubtree(explicitUsing)(clue(tree)))
  }

  testUnpickle("trait-with-parameter", "simple_trees.TraitWithParameter") { tree =>
    val traitMatch: StructureCheck = {
      case Template(
            DefDef(SimpleName("<init>"), List(Left(ValDef(SimpleName("param"), _, _, _) :: Nil)), _, None, _),
            TypeWrapper(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Object"))) :: Nil,
            _,
            ValDef(SimpleName("param"), _, _, _) :: Nil
          ) =>
    }

  }

  testUnpickle("extend-trait", "simple_trees.ExtendsTrait") { tree =>
    val classMatch: StructureCheck = {
      case Template(
            _,
            List(jlObject: Apply, TypeIdent(SimpleTypeName("AbstractTrait"))),
            _,
            // TODO: check the OVERRIDE modifer once modifiers are read
            DefDef(SimpleName("abstractMethod"), _, _, _, _) :: Nil
          ) if isJavaLangObject.isDefinedAt(jlObject) =>
    }
    assert(containsSubtree(classMatch)(clue(tree)))
  }

  testUnpickle("lambda", "simple_trees.Function") { tree =>
    val functionLambdaMatch: StructureCheck = {
      case ValDef(
            SimpleName("functionLambda"),
            _,
            Some(
              Block(
                List(DefDef(SimpleName("$anonfun"), List(Left(List(ValDef(SimpleName("x"), _, _, _)))), _, _, _)),
                // A lambda is simply a wrapper around a DefDef, defined in the same block.
                // Its type is a function type, therefore not specified.
                Lambda(Ident(SimpleName("$anonfun")), None)
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(functionLambdaMatch)(clue(tree)))

    val SAMLambdaMatch: StructureCheck = {
      case ValDef(
            SimpleName("samLambda"),
            _,
            Some(
              Block(
                List(DefDef(SimpleName("$anonfun"), List(Left(Nil)), _, _, _)),
                // the lambda's type is not just a function type, therefore specified
                Lambda(
                  Ident(SimpleName("$anonfun")),
                  Some(
                    TypeWrapper(
                      TypeRefInternal(
                        ty.PackageRef(PackageFullName(List(SimpleName("java"), SimpleName("lang")))),
                        SimpleTypeName("Runnable")
                      )
                    )
                  )
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(SAMLambdaMatch)(clue(tree)))

    val polyIDMatch: StructureCheck = {
      case ValDef(
            SimpleName("polyID"),
            _,
            Some(
              Block(
                List(
                  DefDef(
                    SimpleName("$anonfun"),
                    List(
                      Right(List(TypeParam(SimpleTypeName("T"), _, _))),
                      Left(List(ValDef(SimpleName("x"), _, _, _)))
                    ),
                    _,
                    _,
                    defSym
                  )
                ),
                Lambda(defRef @ Ident(SimpleName("$anonfun")), None)
              )
            ),
            _
          ) if defRef.symbol == defSym =>
    }
    val polyIDVal = findValDefTree(tree, termName("polyID"))
    assert(containsSubtree(polyIDMatch)(clue(polyIDVal)))

    val dependentIDMatch: StructureCheck = {
      case ValDef(
            SimpleName("dependentID"),
            _,
            Some(
              Block(
                List(
                  DefDef(
                    _,
                    List(Left(List(ValDef(SimpleName("x"), TypeWrapper(_), None, xSym)))),
                    TypeWrapper(TermRefInternal(NoPrefix, xRef)),
                    Some(Ident(SimpleName("x"))),
                    _
                  )
                ),
                Lambda(Ident(_), None)
              )
            ),
            _
          ) if xRef == xSym =>
    }
    assert(containsSubtree(dependentIDMatch)(clue(tree)))
  }

  testUnpickle("eta-expansion", "simple_trees.EtaExpansion") { tree =>
    /*
    takesFunction(intMethod)
    the compiler generates a function which simply calls intMethod;
    this function is passed as the argument to takesFunction
     */
    val applicationMatch: StructureCheck = {
      case Apply(
            Select(This(TypeIdent(SimpleTypeName("EtaExpansion"))), SignedName(SimpleName("takesFunction"), _, _)),
            Block(
              List(
                DefDef(
                  SimpleName("$anonfun"),
                  Left(List(ValDef(SimpleName("x"), _, _, _))) :: Nil,
                  _,
                  Some(
                    Apply(
                      Select(
                        This(TypeIdent(SimpleTypeName("EtaExpansion"))),
                        SignedName(SimpleName("intMethod"), _, _)
                      ),
                      List(Ident(SimpleName("x")))
                    )
                  ),
                  _
                )
              ),
              Lambda(Ident(SimpleName("$anonfun")), None)
            ) :: Nil
          ) =>
    }
    assert(containsSubtree(applicationMatch)(clue(tree)))
  }

  testUnpickle("partial-application", "simple_trees.PartialApplication") { tree =>
    // Partial application under the hood is defining a function which takes the remaining parameters
    // and calls the original function with fixed + remaining parameters
    val applicationMatch: StructureCheck = {
      case DefDef(
            SimpleName("partiallyApplied"),
            Nil,
            _,
            Some(
              Block(
                List(
                  DefDef(
                    SimpleName("$anonfun"),
                    Left(ValDef(SimpleName("second"), _, _, _) :: Nil) :: Nil,
                    _,
                    Some(
                      Apply(
                        Apply(
                          Select(
                            This(TypeIdent(SimpleTypeName("PartialApplication"))),
                            SignedName(SimpleName("withManyParams"), _, _)
                          ),
                          Literal(Constant(0)) :: Nil
                        ),
                        Ident(SimpleName("second")) :: Nil
                      )
                    ),
                    _
                  )
                ),
                Lambda(Ident(SimpleName("$anonfun")), None)
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(applicationMatch)(clue(tree)))
  }

  testUnpickle("partial-function", "simple_trees.WithPartialFunction") { tree =>
    val partialFunction: StructureCheck = {
      case DefDef(
            SimpleName("$anonfun"),
            Left(List(ValDef(SimpleName("x$1"), _, None, _))) :: Nil,
            _,
            // match x$1 with type x$1
            Some(
              Match(
                Ident(SimpleName("x$1")),
                List(CaseDef(ExprPattern(Literal(Constant(0))), None, Block(Nil, Literal(Constant(1)))))
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(partialFunction)(clue(tree)))
  }

  testUnpickle("named-argument", "simple_trees.NamedArgument") { tree =>
    val withNamedArgumentApplication: StructureCheck = {
      case Apply(
            Select(This(TypeIdent(SimpleTypeName("NamedArgument"))), SignedName(SimpleName("withNamed"), _, _)),
            List(Literal(Constant(0)), NamedArg(SimpleName("second"), Literal(Constant(1))))
          ) =>
    }
    assert(containsSubtree(withNamedArgumentApplication)(clue(tree)))
  }

  testUnpickle("return", "simple_trees.Return") { tree =>
    val returnMatch: StructureCheck = {
      case Return(Some(Literal(Constant(1))), from) if from.name == SimpleName("withReturn") =>
    }
    assert(containsSubtree(returnMatch)(clue(tree)))
  }

  testUnpickle("super", "simple_trees.Super") { tree =>
    val superMatch: StructureCheck = { case Super(This(TypeIdent(SimpleTypeName("Super"))), None) =>
    }
    assert(containsSubtree(superMatch)(clue(tree)))

    val mixinSuper: StructureCheck = {
      case Super(This(TypeIdent(SimpleTypeName("Super"))), Some(TypeIdent(SimpleTypeName("Base")))) =>
    }
    assert(containsSubtree(mixinSuper)(clue(tree)))
  }

  testUnpickle("parents", "simple_trees.Super") { tree =>
    val classWithParams: StructureCheck = {
      case Template(
            _,
            List(
              Apply(Select(New(TypeIdent(Base @ _)), SignedName(nme.Constructor, _, _)), List()),
              TypeIdent(SimpleTypeName("BaseTrait"))
            ),
            _,
            _
          ) =>
    }
    assert(containsSubtree(classWithParams)(clue(tree)))
  }

  testUnpickle("super-types", "simple_trees.SuperTypes$") { tree =>
    val treeBar = findTree(tree) { case cd @ ClassDef(SimpleTypeName("Bar"), _, _) =>
      cd
    }

    val barMethodCheck: StructureCheck = {
      case DefDef(
            SimpleName("bar"),
            Nil,
            SingletonTypeTree(Select(Super(This(TypeIdent(SimpleTypeName("Bar"))), None), SimpleName("foo"))),
            Some(
              Match(
                _,
                List(
                  CaseDef(
                    Unapply(
                      _,
                      Nil,
                      List(
                        Bind(
                          SimpleName("x"),
                          WildcardPattern(
                            TermRefInternal(
                              ty.SuperType(
                                ty.ThisType(TypeRefInternal(_, symBar: TypeSymbol)),
                                Some(TypeRefInternal(_, symFoo: TypeSymbol))
                              ),
                              symFooField: TermSymbol
                            )
                          ),
                          _
                        )
                      )
                    ),
                    None,
                    _
                  )
                )
              )
            ),
            _
          )
          if symBar.name == typeName("Bar") && symFoo.name == typeName("Foo") && symFooField.name == termName("foo") =>
    }
    assert(containsSubtree(barMethodCheck)(clue(treeBar)))
  }

  testUnpickle("type-member", "simple_trees.TypeMember") { tree =>
    // simple type member
    val typeMember: StructureCheck = {
      case defTree @ TypeMember(
            SimpleTypeName("TypeMember"),
            TypeAliasDefinitionTree(TypeIdent(SimpleTypeName("Int"))),
            symbol
          ) if symbol.tree.contains(defTree) =>
    }
    assert(containsSubtree(typeMember)(clue(tree)))

    // abstract without user-specified bounds, therefore default bounds are generated
    val abstractTypeMember: StructureCheck = {
      case TypeMember(SimpleTypeName("AbstractType"), NothingAnyTypeBoundsTree(), _) =>
    }
    assert(containsSubtree(abstractTypeMember)(clue(tree)))

    // abstract with explicit bounds
    val abstractWithBounds: StructureCheck = {
      case TypeMember(
            SimpleTypeName("AbstractWithBounds"),
            ExplicitTypeBoundsTree(TypeIdent(SimpleTypeName("Null")), TypeIdent(SimpleTypeName("Product"))),
            _
          ) =>
    }
    assert(containsSubtree(abstractWithBounds)(clue(tree)))

    // opaque
    val opaqueTypeMember: StructureCheck = {
      case TypeMember(
            SimpleTypeName("Opaque"),
            OpaqueTypeAliasDefinitionTree(
              InferredTypeBoundsTree(defn.NothingAnyBounds),
              TypeIdent(SimpleTypeName("Int"))
            ),
            _
          ) =>
    }
    assert(containsSubtree(opaqueTypeMember)(clue(tree)))

    // bounded opaque
    val opaqueWithBounds: StructureCheck = {
      case TypeMember(
            SimpleTypeName("OpaqueWithBounds"),
            OpaqueTypeAliasDefinitionTree(
              ExplicitTypeBoundsTree(TypeIdent(SimpleTypeName("Null")), TypeIdent(SimpleTypeName("Product"))),
              TypeIdent(SimpleTypeName("Null"))
            ),
            _
          ) =>
    }
    assert(containsSubtree(opaqueWithBounds)(clue(tree)))
  }

  testUnpickle("generic-class", "simple_trees.GenericClass") { tree =>
    /*
    The class and its constructor have the same type bounds for the type parameter,
    but the constructor's are attached to the type parameter declaration in the code,
    and the class's are just typebounds (no associated code location), hence the difference in structures
     */
    val genericClass: StructureCheck = {
      case defTree @ ClassDef(
            SimpleTypeName("GenericClass"),
            Template(
              DefDef(
                SimpleName("<init>"),
                List(
                  Right(
                    List(
                      firstTypeParamTree @ TypeParam(
                        SimpleTypeName("T"),
                        NothingAnyTypeBoundsTree(),
                        firstTypeParamSymbol
                      )
                    )
                  ),
                  Left(List(ValDef(SimpleName("value"), TypeIdent(SimpleTypeName("T")), None, valueParamSymbol)))
                ),
                _,
                _,
                _
              ),
              _,
              _,
              (secondTypeParamTree @ TypeParam(
                SimpleTypeName("T"),
                InferredTypeBoundsTree(NothingAnyTypeBounds()),
                secondTypeParamSymbol
              )) :: _
            ),
            classSymbol
          )
          if classSymbol.tree.contains(defTree)
            && firstTypeParamSymbol.isInstanceOf[LocalTypeParamSymbol]
            && secondTypeParamSymbol.isInstanceOf[ClassTypeParamSymbol]
            && firstTypeParamSymbol.tree.contains(firstTypeParamTree)
            && secondTypeParamSymbol.tree.contains(secondTypeParamTree) =>
    }
    assert(containsSubtree(genericClass)(clue(tree)))
  }

  testUnpickle("generic-method", "simple_trees.GenericMethod") { tree =>
    val genericMethod: StructureCheck = {
      case DefDef(
            SimpleName("usesTypeParam"),
            List(Right(List(TypeParam(SimpleTypeName("T"), NothingAnyTypeBoundsTree(), _))), Left(Nil)),
            AppliedTypeTree(TypeIdent(SimpleTypeName("Option")), TypeIdent(SimpleTypeName("T")) :: Nil),
            _,
            _
          ) =>
    }
    assert(containsSubtree(genericMethod)(clue(tree)))
  }

  testUnpickle("generic-extension", "simple_trees.GenericExtension$package$") { tree =>
    val extensionCheck: StructureCheck = {
      case DefDef(
            SimpleName("genericExtension"),
            List(
              Left(List(ValDef(SimpleName("i"), TypeIdent(SimpleTypeName("Int")), None, _))),
              Right(List(TypeParam(SimpleTypeName("T"), NothingAnyTypeBoundsTree(), _))),
              Left(List(ValDef(SimpleName("genericArg"), TypeIdent(SimpleTypeName("T")), None, _)))
            ),
            _,
            _,
            _
          ) =>
    }
    assert(containsSubtree(extensionCheck)(clue(tree)))
  }

  testUnpickle("class-type-bounds", "simple_trees.TypeBoundsOnClass") { tree =>
    val genericClass: StructureCheck = {
      case defTree @ ClassDef(
            SimpleTypeName("TypeBoundsOnClass"),
            Template(
              DefDef(
                SimpleName("<init>"),
                List(
                  Right(
                    List(
                      TypeParam(
                        SimpleTypeName("T"),
                        ExplicitTypeBoundsTree(TypeIdent(SimpleTypeName("Null")), TypeIdent(SimpleTypeName("AnyRef"))),
                        _
                      )
                    )
                  ),
                  Left(Nil)
                ),
                _,
                _,
                _
              ),
              _,
              _,
              TypeParam(
                SimpleTypeName("T"),
                InferredTypeBoundsTree(
                  AbstractTypeBounds(
                    TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Null")),
                    TypeRefInternal(ScalaPackageRef(), SimpleTypeName("AnyRef"))
                  )
                ),
                _
              ) :: _
            ),
            symbol
          ) if symbol.tree.contains(defTree) =>
    }
    assert(containsSubtree(genericClass)(clue(tree)))
  }

  testUnpickle("shared-type-bounds", "simple_trees.GenericClassWithNestedGeneric") { tree =>
    // The type bounds of the class and its inner class are shared in the TASTy serializations.
    // This test checks that such shared type bounds are read correctly.
    val genericClass: StructureCheck = {
      case outerDefTree @ ClassDef(
            SimpleTypeName("GenericClassWithNestedGeneric"),
            Template(
              DefDef(
                SimpleName("<init>"),
                List(Right(List(TypeParam(SimpleTypeName("T"), NothingAnyTypeBoundsTree(), _))), Left(Nil)),
                _,
                _,
                _
              ),
              _,
              _,
              TypeParam(
                SimpleTypeName("T"),
                InferredTypeBoundsTree(NothingAnyTypeBounds()),
                _
              ) :: (innerDefTree @ ClassDef(SimpleTypeName("NestedGeneric"), _, innerSymbol)) :: _
            ),
            outerSymbol
          ) if outerSymbol.tree.contains(outerDefTree) && innerSymbol.tree.contains(innerDefTree) =>
    }
    assert(containsSubtree(genericClass)(clue(tree)))

    val nestedClass: StructureCheck = {
      case defTree @ ClassDef(
            SimpleTypeName("NestedGeneric"),
            Template(
              DefDef(
                SimpleName("<init>"),
                List(Right(List(TypeParam(SimpleTypeName("U"), NothingAnyTypeBoundsTree(), _))), Left(Nil)),
                _,
                _,
                _
              ),
              _,
              _,
              TypeParam(SimpleTypeName("U"), InferredTypeBoundsTree(NothingAnyTypeBounds()), _) :: _
            ),
            symbol
          ) if symbol.tree.contains(defTree) =>
    }
    assert(containsSubtree(nestedClass)(clue(tree)))
  }

  testUnpickle("inline-method", "simple_trees.InlinedCall") { tree =>
    val inlined: StructureCheck = {
      case Inlined(
            // 0 + HasInlinedMethod_this.externalVal
            Apply(
              Select(Inlined(Literal(Constant(0)), None, Nil), SignedName(SimpleName("+"), _, _)),
              Select(Inlined(Ident(SimpleName("HasInlinedMethod_this")), None, Nil), SimpleName("externalVal")) :: Nil
            ),
            // the _toplevel_ class, method inside which is inlined
            Some(TypeIdent(SimpleTypeName("HasInlinedMethod"))),
            ValDef(
              SimpleName("HasInlinedMethod_this"),
              _,
              Some(Select(This(TypeIdent(SimpleTypeName("InlinedCall"))), SimpleName("withInlineMethod"))),
              _
            ) :: Nil
          ) =>
    }
    assert(containsSubtree(inlined)(clue(tree)))
  }

  testUnpickle("inlined-path", "simple_trees.InlinedPath") { tree =>
    val inlinedPath: StructureCheck = {
      case SelectTypeTree(
            InlinedTypeTree(
              Some(TypeIdent(ObjectClassTypeName(SimpleTypeName("InlinedPath")))),
              InlinedTypeTree(None, TypeWrapper(TermRefInternal(NoPrefix, xSym: Symbol)))
            ),
            SimpleTypeName("Inner")
          ) if xSym.name == termName("x") =>
    }
    val testDef = findTree(tree) { case testDef @ DefDef(SimpleName("test"), _, _, _, _) =>
      testDef
    }
    assert(containsSubtree(inlinedPath)(clue(testDef)))
  }

  testUnpickle("select-tpt", "simple_trees.SelectType") { tree =>
    val selectTpt: StructureCheck = {
      case ValDef(
            SimpleName("random"),
            TypeWrapper(
              TypeRefInternal(
                /* This should be a PackageRef for scala.util, but since it is not
                 * available on the restricted classpath, it becomes a TermRef instead.
                 */
                TermRefInternal(ty.PackageRef(PackageFullName.scalaPackageName), SimpleName("util")),
                SimpleTypeName("Random")
              )
            ),
            Some(
              Apply(
                // select scala.util.Random
                Select(
                  New(
                    SelectTypeTree(
                      // Same as above
                      TypeWrapper(TermRefInternal(ty.PackageRef(PackageFullName.scalaPackageName), SimpleName("util"))),
                      SimpleTypeName("Random")
                    )
                  ),
                  SignedName(SimpleName("<init>"), _, _)
                ),
                Nil
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(selectTpt)(clue(tree)))
  }

  testUnpickle("by-name-parameter", "simple_trees.ByNameParameter") { tree =>
    val byName: StructureCheck = {
      case DefDef(
            SimpleName("withByName"),
            List(Left(List(ValDef(SimpleName("x"), ByNameTypeTree(TypeIdent(SimpleTypeName("Int"))), None, _)))),
            _,
            _,
            _
          ) =>
    }
    assert(containsSubtree(byName)(clue(tree)))
  }

  testUnpickle("by-name-type", "simple_trees.ClassWithByNameParameter") { tree =>
    val byName: StructureCheck = {
      case ValDef(
            SimpleName("byNameParam"),
            TypeWrapper(ty.ByNameType(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int")))),
            None,
            _
          ) =>
    }
    assert(containsSubtree(byName)(clue(tree)))
  }

  testUnpickle("union-type", "simple_trees.UnionType") { tree =>
    val unionTypeMethod: StructureCheck = {
      case DefDef(
            SimpleName("argWithOrType"),
            // Int | String = | [Int, String]
            List(
              Left(
                List(
                  ValDef(
                    SimpleName("x"),
                    AppliedTypeTree(
                      TypeIdent(SimpleTypeName("|")),
                      List(TypeIdent(SimpleTypeName("Int")), TypeIdent(SimpleTypeName("String")))
                    ),
                    None,
                    _
                  )
                )
              )
            ),
            TypeWrapper(
              ty.OrType(
                TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int")),
                TypeRefInternal(PredefRef(), SimpleTypeName("String"))
              )
            ),
            _,
            _
          ) =>
    }
    assert(containsSubtree(unionTypeMethod)(clue(tree)))
  }

  testUnpickle("intersection-type", "simple_trees.IntersectionType") { tree =>
    val intersectionTypeMethod: StructureCheck = {
      case DefDef(
            SimpleName("argWithAndType"),
            List(
              Left(
                List(
                  ValDef(
                    SimpleName("x"),
                    // IntersectionType & UnionType = & [IntersectionType, UnionType]
                    AppliedTypeTree(
                      TypeIdent(SimpleTypeName("&")),
                      List(TypeIdent(SimpleTypeName("IntersectionType")), TypeIdent(SimpleTypeName("UnionType")))
                    ),
                    None,
                    _
                  )
                )
              )
            ),
            TypeWrapper(
              ty.AndType(
                TypeRefInternal(SimpleTreesPackageRef(), SymbolWithName(SimpleTypeName("IntersectionType"))),
                TypeRefInternal(SimpleTreesPackageRef(), SimpleTypeName("UnionType"))
              )
            ),
            _,
            _
          ) =>
    }
    assert(containsSubtree(intersectionTypeMethod)(clue(tree)))
  }

  testUnpickle("type-lambda", "simple_trees.TypeLambda") { tree =>
    val lambdaTpt: StructureCheck = {
      // TL: [X] =>> List[X]
      case TypeMember(
            SimpleTypeName("TL"),
            PolyTypeDefinitionTree(
              // [X]
              TypeParam(SimpleTypeName("X"), NothingAnyTypeBoundsTree(), _) :: Nil,
              // List[X]
              TypeAliasDefinitionTree(
                AppliedTypeTree(TypeIdent(SimpleTypeName("List")), TypeIdent(SimpleTypeName("X")) :: Nil)
              )
            ),
            _
          ) =>
    }

    assert(containsSubtree(lambdaTpt)(clue(tree)))
  }

  testUnpickle("type-lambda-type", "simple_trees.HigherKinded") { tree =>
    val typeLambdaResultIsAny: TypeStructureCheck = { case TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Any")) =>
    }

    // A[_], i.e. A >: Nothing <: [X] =>> Any
    val typeLambda: StructureCheck = {
      case TypeParam(SimpleTypeName("A"), InferredTypeBoundsTree(AbstractTypeBounds(nothing, tl: TypeLambda)), _)
          if tl.paramNames == List(UniqueTypeName(tpnme.EmptyTypeName, "_$", 1))
            && typeLambdaResultIsAny.isDefinedAt(tl.resultType) =>
    }
    assert(containsSubtree(typeLambda)(clue(tree)))

    val fDef = findTree(tree) { case fDef @ DefDef(SimpleName("f"), _, _, _, _) =>
      fDef
    }
    val fDefExpected: StructureCheck = {
      case DefDef(
            SimpleName("f"),
            List(
              Right(
                List(
                  TypeParam(
                    SimpleTypeName("B"),
                    PolyTypeDefinitionTree(
                      List(TypeParam(_, NothingAnyTypeBoundsTree(), _)),
                      NothingAnyTypeBoundsTree()
                    ),
                    _
                  ),
                  TypeParam(SimpleTypeName("T"), NothingAnyTypeBoundsTree(), _)
                )
              ),
              Left(
                List(
                  ValDef(
                    SimpleName("x"),
                    AppliedTypeTree(TypeIdent(SimpleTypeName("B")), List(TypeIdent(SimpleTypeName("T")))),
                    None,
                    _
                  )
                )
              )
            ),
            AppliedTypeTree(TypeIdent(SimpleTypeName("B")), List(TypeIdent(SimpleTypeName("T")))),
            None,
            _
          ) =>
    }
    assert(containsSubtree(fDefExpected)(clue(fDef)))
  }

  object TyParamRef:
    def unapply(t: TypeParamRef): Some[Name] = Some(t.paramName)

  testUnpickle("type-lambda-type-result-depends-on-param", "simple_trees.HigherKindedWithParam") { tree =>
    // Type lambda result is List[X]
    val typeLambdaResultIsListOf: TypeStructureCheck = {
      case ty.AppliedType(
            TypeRefInternal(_: PackageRef, SimpleTypeName("List")),
            TyParamRef(SimpleTypeName("X")) :: Nil
          ) =>
    }

    // A[X] <: List[X], i.e. A >: Nothing <: [X] =>> List[X]
    val typeLambda: StructureCheck = {
      case TypeParam(SimpleTypeName("A"), InferredTypeBoundsTree(AbstractTypeBounds(nothing, tl: TypeLambda)), _)
          if tl.paramNames == List(typeName("X")) && typeLambdaResultIsListOf.isDefinedAt(tl.resultType) =>
    }
    assert(containsSubtree(typeLambda)(clue(tree)))
  }

  testUnpickle("varags-annotated-type", "simple_trees.VarargFunction") { tree =>
    def findDefDef(name: String): DefDef =
      findTree(tree) { case dd @ DefDef(SimpleName(`name`), _, _, _, _) =>
        dd
      }

    object RepeatedAnnot:
      def unapply(tree: Apply): Boolean = tree match
        case Apply(
              Select(
                New(TypeWrapper(TypeRefInternal(_: PackageRef, SimpleTypeName("Repeated")))),
                SignedName(SimpleName("<init>"), _, _)
              ),
              Nil
            ) =>
          true
        case _ =>
          false
    end RepeatedAnnot

    val takesVarargs: StructureCheck = {
      case DefDef(
            SimpleName("takesVarargs"),
            List(
              Left(
                List(
                  ValDef(
                    SimpleName("xs"),
                    AnnotatedTypeTree(
                      // Int* ==> Seq[Int]
                      AppliedTypeTree(
                        TypeWrapper(TypeRefInternal(_: PackageRef, SimpleTypeName("Seq"))),
                        SimpleTypeIdent("Int") :: Nil
                      ),
                      RepeatedAnnot()
                    ),
                    None,
                    _
                  )
                )
              )
            ),
            AppliedTypeTree(SimpleTypeIdent("Seq"), List(SimpleTypeIdent("Int"))),
            Some(SimpleIdent("xs")),
            _
          ) =>
    }
    assert(containsSubtree(takesVarargs)(clue(findDefDef("takesVarargs"))))

    val givesVarargs: StructureCheck = {
      case DefDef(
            SimpleName("givesVarargs"),
            List(
              Left(
                List(
                  ValDef(
                    SimpleName("xs"),
                    AppliedTypeTree(SimpleTypeIdent("Seq"), List(SimpleTypeIdent("Int"))),
                    None,
                    _
                  )
                )
              )
            ),
            AppliedTypeTree(SimpleTypeIdent("Seq"), List(SimpleTypeIdent("Int"))),
            Some(
              Apply(
                Select(_, SignedName(SimpleName("takesVarargs"), _, _)),
                List(Typed(SimpleIdent("xs"), TypeWrapper(ty.RepeatedType(_))))
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(givesVarargs)(clue(findDefDef("givesVarargs"))))

    val givesSeqLiteral: StructureCheck = {
      case DefDef(
            SimpleName("givesSeqLiteral"),
            List(Left(List(ValDef(SimpleName("x"), SimpleTypeIdent("Int"), None, _)))),
            AppliedTypeTree(SimpleTypeIdent("Seq"), List(SimpleTypeIdent("Int"))),
            Some(
              Apply(
                Select(_, SignedName(SimpleName("takesVarargs"), _, _)),
                List(
                  Typed(
                    SeqLiteral(
                      List(SimpleIdent("x"), Literal(Constant(1))),
                      TypeWrapper(TypeRefInternal(_, SimpleTypeName("Int")))
                    ),
                    TypeWrapper(ty.RepeatedType(_))
                  )
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(givesSeqLiteral)(clue(findDefDef("givesSeqLiteral"))))

    val givesSeqToJava: StructureCheck = {
      case DefDef(
            SimpleName("givesSeqToJava"),
            List(
              Left(
                List(
                  ValDef(
                    SimpleName("xs"),
                    AppliedTypeTree(SimpleTypeIdent("Seq"), List(SimpleTypeIdent("Int"))),
                    None,
                    _
                  )
                )
              )
            ),
            AppliedTypeTree(SelectTypeTree(_, SimpleTypeName("List")), List(SimpleTypeIdent("Int"))),
            Some(
              Apply(
                TypeApply(Select(_, SignedName(SimpleName("asList"), _, _)), _),
                List(Typed(SimpleIdent("xs"), TypeWrapper(ty.RepeatedType(_))))
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(givesSeqToJava)(clue(findDefDef("givesSeqToJava"))))

    val givesSeqLiteralToJava: StructureCheck = {
      case DefDef(
            SimpleName("givesSeqLiteralToJava"),
            List(Left(List(ValDef(SimpleName("x"), SimpleTypeIdent("Int"), None, _)))),
            AppliedTypeTree(SelectTypeTree(_, SimpleTypeName("List")), List(SimpleTypeIdent("Int"))),
            Some(
              Apply(
                TypeApply(Select(_, SignedName(SimpleName("asList"), _, _)), _),
                List(
                  Typed(
                    SeqLiteral(
                      List(SimpleIdent("x"), Literal(Constant(1))),
                      TypeWrapper(TypeRefInternal(_, SimpleTypeName("Int")))
                    ),
                    TypeWrapper(ty.RepeatedType(_))
                  )
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(givesSeqLiteralToJava)(clue(findDefDef("givesSeqLiteralToJava"))))
  }

  testUnpickle("refined-type-tree", "simple_trees.RefinedTypeTree") { tree =>
    val refinedTpt: StructureCheck = {
      case TypeMember(
            SimpleTypeName("Refined"),
            // TypeMember { type AbstractType = Int }
            TypeAliasDefinitionTree(
              RefinedTypeTree(
                TypeIdent(SimpleTypeName("TypeMember")),
                TypeMember(
                  SimpleTypeName("AbstractType"),
                  TypeAliasDefinitionTree(TypeIdent(SimpleTypeName("Int"))),
                  _
                ) :: Nil,
                _
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(refinedTpt)(clue(tree)))

    val recTpt: StructureCheck = {
      case ValDef(
            SimpleName("innerRefVal"),
            RefinedTypeTree(
              TypeIdent(SimpleTypeName("C")),
              DefDef(SimpleName("c1"), Nil, TypeIdent(SimpleTypeName("C1")), None, _) :: Nil,
              _
            ),
            Some(
              Block(
                ClassDef(anonType1, _, _) :: Nil,
                Typed(Apply(Select(New(TypeIdent(anonType2)), _), Nil), TypeWrapper(rt: RecType))
              )
            ),
            _
          ) if anonType1 == anonType2 =>
    }
    assert(containsSubtree(recTpt)(clue(tree)))
  }

  testUnpickle("refined-type", "simple_trees.RefinedType") { tree =>
    val refinedType: StructureCheck = {
      case Typed(
            expr,
            TypeWrapper(
              ty.TypeRefinement(
                ty.TypeRefinement(
                  TypeRefInternal(SimpleTreesPackageRef(), SimpleTypeName("TypeMember")),
                  SimpleTypeName("AbstractType"),
                  TypeAlias(alias)
                ),
                SimpleTypeName("AbstractWithBounds"),
                TypeAlias(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Null")))
              )
            )
          ) =>
    }
    assert(containsSubtree(refinedType)(clue(tree)))

    val givenRefinementCheck: StructureCheck = {
      case DefDef(
            SimpleName("givenRefinement"),
            Nil,
            TypeWrapper(
              ty.TermRefinement(
                _,
                SimpleName("foo"),
                ty.MethodType(
                  List(_ -> TypeRefInternal(_, SimpleTypeName("Int"))),
                  TypeRefInternal(_, SimpleTypeName("Int"))
                )
              )
            ),
            Some(_),
            _
          ) =>
    }
    assert(containsSubtree(givenRefinementCheck)(clue(tree)))
  }

  testUnpickle("match-type", "simple_trees.MatchType") { tree =>
    val matchTpt: StructureCheck = {
      case TypeMember(
            SimpleTypeName("MT"),
            PolyTypeDefinitionTree(
              List(TypeParam(SimpleTypeName("X"), NothingAnyTypeBoundsTree(), _)),
              TypeAliasDefinitionTree(
                MatchTypeTree(
                  // No bound on the match result -- inferred to be String
                  TypeWrapper(TypeRefInternal(PredefRef(), tpnme.String)),
                  TypeIdent(SimpleTypeName("X")),
                  List(TypeCaseDef(TypeIdent(SimpleTypeName("Int")), TypeIdent(SimpleTypeName("String"))))
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(matchTpt)(clue(tree)))

    val matchWithBound: StructureCheck = {
      case TypeMember(
            SimpleTypeName("MTWithBound"),
            PolyTypeDefinitionTree(
              List(TypeParam(SimpleTypeName("X"), NothingAnyTypeBoundsTree(), _)),
              TypeAliasDefinitionTree(
                MatchTypeTree(
                  TypeIdent(SimpleTypeName("Product")),
                  TypeIdent(SimpleTypeName("X")),
                  List(
                    TypeCaseDef(
                      TypeIdent(SimpleTypeName("Int")),
                      AppliedTypeTree(TypeIdent(SimpleTypeName("Some")), List(TypeIdent(SimpleTypeName("Int"))))
                    )
                  )
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(matchWithBound)(clue(tree)))

    val matchWithWildcard: StructureCheck = {
      case TypeMember(
            SimpleTypeName("MTWithWildcard"),
            PolyTypeDefinitionTree(
              List(TypeParam(SimpleTypeName("X"), NothingAnyTypeBoundsTree(), _)),
              TypeAliasDefinitionTree(
                MatchTypeTree(
                  // No bound on the match result -- inferred to be Int
                  TypeWrapper(TypeRefInternal(ScalaPackageRef(), tpnme.Int)),
                  TypeIdent(SimpleTypeName("X")),
                  List(TypeCaseDef(TypeIdent(tpnme.Wildcard), TypeIdent(SimpleTypeName("Int"))))
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(matchWithWildcard)(clue(tree)))

    val matchWithBind: StructureCheck = {
      case TypeMember(
            SimpleTypeName("MTWithBind"),
            PolyTypeDefinitionTree(
              List(TypeParam(SimpleTypeName("X"), NothingAnyTypeBoundsTree(), _)),
              TypeAliasDefinitionTree(
                MatchTypeTree(
                  // No bound on the match result -> (erroneously) inferred to `t`
                  TypeWrapper(_),
                  TypeIdent(SimpleTypeName("X")),
                  List(
                    TypeCaseDef(
                      AppliedTypeTree(
                        TypeIdent(SimpleTypeName("List")),
                        TypeTreeBind(SimpleTypeName("t"), NamedTypeBoundsTree(tpnme.Wildcard, _), _) :: Nil
                      ),
                      TypeIdent(SimpleTypeName("t"))
                    )
                  )
                )
              )
            ),
            _
          ) =>
    }
    assert(containsSubtree(matchWithBind)(clue(tree)))

    val castMatchResult: StructureCheck = {
      case DefDef(
            SimpleName("castMatchResult"),
            List(Right(List(X @ _)), _),
            _,
            Some(
              TypeApply(
                Select(rhs, SignedName(SimpleName("$asInstanceOf$"), _, _)),
                TypeWrapper(
                  ty.MatchType(
                    TypeRefInternal(PredefRef(), SimpleTypeName("String")),
                    TypeRefInternal(_, xRef),
                    List(
                      ty.MatchTypeCase(
                        Nil,
                        TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int")),
                        TypeRefInternal(PredefRef(), SimpleTypeName("String"))
                      )
                    )
                  )
                ) :: Nil
              )
            ),
            _
          ) if xRef == X.symbol =>
    }
    assert(containsSubtree(castMatchResult)(clue(tree)))

    val castMatchResultWithBind: StructureCheck = {
      case DefDef(
            SimpleName("castMatchResultWithBind"),
            List(Right(List(X @ _)), _),
            _,
            Some(
              TypeApply(
                Select(rhs, SignedName(SimpleName("$asInstanceOf$"), _, _)),
                TypeWrapper(
                  ty.MatchType(
                    _, // erroneously inferred to `t`
                    TypeRefInternal(_, xRef),
                    List(
                      ty.MatchTypeCase(
                        List(tRef),
                        ty.AppliedType(
                          TypeRefInternal(ScalaCollImmutablePackageRef(), SimpleTypeName("List")),
                          tRef2 :: Nil
                        ),
                        tRef3
                      )
                    )
                  )
                ) :: Nil
              )
            ),
            _
          ) if xRef == X.symbol && tRef == tRef2 && tRef == tRef3 =>
    }
    assert(containsSubtree(castMatchResultWithBind)(clue(tree)))
  }

  testUnpickle("package-type-ref", "toplevelEmptyPackage$package$") { tree =>
    // Empty package (the path to the toplevel$package[ModuleClass]) is a THIS of a TYPEREFpkg as opposed to
    // non-empty package, which is simply TERMREFpkg. Therefore, reading the type of the package object reads TYPEREFpkg.
    val packageVal: StructureCheck = {
      case ValDef(
            SimpleName("toplevelEmptyPackage$package"),
            TypeIdent(ObjectClassTypeName(SimpleTypeName("toplevelEmptyPackage$package"))),
            _,
            _
          ) =>
    }
    val valTree = tree.symbol.moduleValue.get.tree.get
    assert(containsSubtree(packageVal)(clue(valTree)))
  }

  testUnpickle("wildcard-type-application", "simple_trees.WildcardTypeApplication") { tree =>
    // class parameter as a val
    val appliedTypeToTypeBounds: StructureCheck = {
      case ValDef(
            SimpleName("anyList"),
            TypeWrapper(
              ty.AppliedType(
                TypeRefInternal(_: PackageRef, SimpleTypeName("List")),
                ty.WildcardTypeArg(NothingAnyTypeBounds()) :: Nil
              )
            ),
            None,
            _
          ) =>
    }
    assert(containsSubtree(appliedTypeToTypeBounds)(clue(tree)))

    // class parameter as a constructor parameter
    val appliedTypeToTypeBoundsTpt: StructureCheck = {
      case ValDef(
            SimpleName("anyList"),
            AppliedTypeTree(TypeIdent(SimpleTypeName("List")), WildcardTypeArgTree(NothingAnyTypeBoundsTree()) :: Nil),
            None,
            _
          ) =>
    }
    assert(containsSubtree(appliedTypeToTypeBoundsTpt)(clue(tree)))

    // extends GenericWithTypeBound[_]
    val wildcardParent: StructureCheck = {
      case New(
            AppliedTypeTree(
              TypeIdent(SimpleTypeName("GenericWithTypeBound")),
              WildcardTypeArgTree(
                InferredTypeBoundsTree(
                  AbstractTypeBounds(
                    TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Nothing")),
                    TypeRefInternal(ScalaPackageRef(), SimpleTypeName("AnyKind"))
                  )
                )
              ) :: Nil
            )
          ) =>
    }
    assert(containsSubtree(wildcardParent)(clue(tree)))
  }

  testUnpickle("qual-this-type", "simple_trees.QualThisType") { tree =>
    val newInner: StructureCheck = {
      case New(
            SelectTypeTree(
              TypeWrapper(
                ty.ThisType(TypeRefInternal(SimpleTreesPackageRef(), SymbolWithName(SimpleTypeName("QualThisType"))))
              ),
              SimpleTypeName("Inner")
            )
          ) =>
    }
    assert(containsSubtree(newInner)(clue(tree)))
  }

  testUnpickle("shared-package-reference", "simple_trees.SharedPackageReference$package$") { tree =>
    // TODO: once references are created, check correctness
  }

  testUnpickle("typerefin", "simple_trees.TypeRefIn") { tree =>
    val typerefCheck: StructureCheck = {
      case TypeApply(
            Select(qualifier, SignedName(SimpleName("withArray"), _, _)),
            TypeWrapper(
              TypeRefInternal(
                TermRefInternal(NoPrefix, SymbolWithName(SimpleName("arr"))),
                LookupTypeIn(TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Array")), SimpleTypeName("T"))
              )
            ) :: Nil
          ) =>
    }
    assert(containsSubtree(typerefCheck)(clue(tree)))
  }

  testUnpickle("termrefin", "simple_trees.EmbeddedConfig") { tree =>
    val termRefInCheck: StructureCheck = {
      case TypeWrapper(
            TermRefInternal(
              ty.ThisType(TypeRefInternal(_, SimpleTypeName("DefaultConfigs"))),
              LookupIn(TypeRefInternal(_, SimpleTypeName("DefaultConfigs")), SimpleName("PrivateConfig"))
            )
          ) =>
    }
    assert(containsSubtree(termRefInCheck)(clue(tree.symbol.annotations.head.tree)))
  }

  testUnpickle("thistype", "simple_trees.ThisType") { tree =>
    val thisTypeCheck: StructureCheck = {
      case DefDef(
            SimpleName("m"),
            _ :: Nil,
            SingletonTypeTree(This(TypeIdent(SimpleTypeName("ThisType")))),
            Some(This(TypeIdent(SimpleTypeName("ThisType")))),
            _
          ) =>
    }
    assert(containsSubtree(thisTypeCheck)(clue(tree)))
  }

  testUnpickle("annotations", "simple_trees.Annotations") { tree =>
    object SimpleAnnotCtorNamed:
      def unapply(t: Select): Option[String] = t match
        case Select(New(TypeIdent(SimpleTypeName(name))), _) => Some(name)
        case _                                               => None
    end SimpleAnnotCtorNamed

    val inlineAnnotCheck: StructureCheck = { case Apply(SimpleAnnotCtorNamed("inline"), Nil) =>
    }

    def deprecatedAnnotCheck(msg: String, since: String): StructureCheck = {
      case Apply(SimpleAnnotCtorNamed("deprecated"), List(Literal(Constant(`msg`)), Literal(Constant(`since`)))) =>
    }

    def deprecatedAnnotNamedCheck(msg: String, since: String): StructureCheck = {
      case Apply(
            SimpleAnnotCtorNamed("deprecated"),
            List(Literal(Constant(`msg`)), NamedArg(SimpleName("since"), Literal(Constant(`since`))))
          ) =>
    }

    def deprecatedAnnotBothNamedCheck(msg: String, since: String): StructureCheck = {
      case Apply(
            SimpleAnnotCtorNamed("deprecated"),
            List(
              NamedArg(SimpleName("message"), Literal(Constant(`msg`))),
              NamedArg(SimpleName("since"), Literal(Constant(`since`)))
            )
          ) =>
    }

    def implicitNotFoundAnnotCheck(msg: String): StructureCheck = {
      case Apply(SimpleAnnotCtorNamed("implicitNotFound"), List(Literal(Constant(`msg`)))) =>
    }

    val constructorOnlyAnnotCheck: StructureCheck = { case Apply(SimpleAnnotCtorNamed("constructorOnly"), Nil) =>
    }

    val inlineMethodSym = findTree(tree) { case DefDef(SimpleName("inlineMethod"), _, _, _, sym) =>
      sym
    }
    assert(clue(inlineMethodSym.annotations).sizeIs == 1)
    assert(containsSubtree(inlineAnnotCheck)(clue(inlineMethodSym.annotations(0).tree)))

    val inlineDeprecatedMethodSym = findTree(tree) { case DefDef(SimpleName("inlineDeprecatedMethod"), _, _, _, sym) =>
      sym
    }
    assert(clue(inlineDeprecatedMethodSym.annotations).sizeIs == 2)
    assert(containsSubtree(inlineAnnotCheck)(clue(inlineDeprecatedMethodSym.annotations(0).tree)))
    assert(
      containsSubtree(deprecatedAnnotNamedCheck("some reason", "1.0"))(
        clue(inlineDeprecatedMethodSym.annotations(1).tree)
      )
    )

    val deprecatedValSym = findTree(tree) { case ValDef(SimpleName("deprecatedVal"), _, _, sym) =>
      sym
    }
    assert(clue(deprecatedValSym.annotations).sizeIs == 1)
    assert(
      containsSubtree(deprecatedAnnotBothNamedCheck("reason", "forever"))(clue(deprecatedValSym.annotations(0).tree))
    )

    val myTypeClassSym = findTree(tree) { case ClassDef(SimpleTypeName("MyTypeClass"), _, sym) =>
      sym
    }
    assert(clue(myTypeClassSym.annotations).sizeIs == 1)
    assert(
      containsSubtree(implicitNotFoundAnnotCheck("Cannot find implicit for MyTypeClass[${T}]"))(
        clue(myTypeClassSym.annotations(0).tree)
      )
    )

    val intAliasSym = findTree(tree) { case TypeMember(SimpleTypeName("IntAlias"), _, sym) =>
      sym
    }
    assert(clue(intAliasSym.annotations).sizeIs == 1)
    assert(containsSubtree(deprecatedAnnotCheck("other reason", "forever"))(clue(intAliasSym.annotations(0).tree)))

    val javaAnnotWithDefaultImplicitSym = findTree(tree) {
      case DefDef(SimpleName("javaAnnotWithDefaultImplicit"), _, _, _, sym) =>
        sym
    }
    assert(clue(javaAnnotWithDefaultImplicitSym.annotations).sizeIs == 1)
    val javaAnnotWithDefaultImplicitAnnotCheck: StructureCheck = { case Apply(Select(New(_), _), Nil) =>
    }
    assert(
      containsSubtree(javaAnnotWithDefaultImplicitAnnotCheck)(clue(javaAnnotWithDefaultImplicitSym.annotations(0).tree))
    )

    val javaAnnotWithDefaultExplicitSym = findTree(tree) {
      case DefDef(SimpleName("javaAnnotWithDefaultExplicit"), _, _, _, sym) =>
        sym
    }
    assert(clue(javaAnnotWithDefaultExplicitSym.annotations).sizeIs == 1)
    val javaAnnotWithDefaultExplicitAnnotCheck: StructureCheck = {
      case Apply(Select(New(_), _), List(NamedArg(SimpleName("value"), Literal(Constant(false))))) =>
    }
    assert(
      containsSubtree(javaAnnotWithDefaultExplicitAnnotCheck)(clue(javaAnnotWithDefaultExplicitSym.annotations(0).tree))
    )
  }

  testUnpickle("uninitialized-var", "simple_trees.Uninitialized") { tree =>
    val wildcardRHSCheck: StructureCheck = {
      case ValDef(SimpleName("wildcardRHS"), TypeIdent(SimpleTypeName("Int")), Some(Ident(nme.Wildcard)), sym)
          if !sym.isAbstractMember =>
    }
    assert(containsSubtree(wildcardRHSCheck)(clue(tree)))

    val uninitializedRHSCheck: StructureCheck = {
      case ValDef(
            SimpleName("uninitializedRHS"),
            TypeIdent(SimpleTypeName("Product")),
            Some(Select(_, SimpleName("uninitialized"))),
            sym
          ) if !sym.isAbstractMember =>
    }
    assert(containsSubtree(uninitializedRHSCheck)(clue(tree)))

    val renamedUninitializedRHSCheck: StructureCheck = {
      case ValDef(
            SimpleName("renamedUninitializedRHS"),
            TypeIdent(SimpleTypeName("String")),
            Some(Ident(SimpleName("uninitialized"))),
            sym
          ) if !sym.isAbstractMember =>
    }
    assert(containsSubtree(renamedUninitializedRHSCheck)(clue(tree)))

    // Confidence check
    val abstractVarCheck: StructureCheck = {
      case ValDef(SimpleName("abstractVar"), TypeIdent(SimpleTypeName("Int")), None, sym) if sym.isAbstractMember =>
    }
    assert(containsSubtree(abstractVarCheck)(clue(tree)))
  }

  testUnpickle("quotes-and-splices", "simple_trees.QuotesAndSplices$") { tree =>
    val termQuoteBody = findTree(tree) { case dd @ DefDef(SimpleName("termQuote"), _, _, Some(rhs), _) =>
      rhs
    }
    val termQuoteCheck: StructureCheck = {
      case Quote(Literal(Constant("hello")), TypeRefInternal(_, SimpleTypeName("String"))) =>
    }
    assert(containsSubtree(termQuoteCheck)(clue(termQuoteBody)))

    val termSpliceBody = findTree(tree) { case dd @ DefDef(SimpleName("termSplice"), _, _, Some(rhs), _) =>
      rhs
    }
    val termSpliceCheck: StructureCheck = {
      case Splice(Block(List(_: DefDef), _: Lambda), TypeRefInternal(_, SimpleTypeName("String"))) =>
    }
    assert(containsSubtree(termSpliceCheck)(clue(termSpliceBody)))

    val termQuotePatternDef = findTree(tree) { case dd @ DefDef(SimpleName("termQuotePattern"), _, _, _, _) =>
      dd
    }
    val termQuotePatternCaseDef = findTree(termQuotePatternDef) { case cd: CaseDef =>
      cd
    }
    val termQuotePatternCheck: StructureCheck = {
      case QuotePattern(
            Nil,
            Left(
              Apply(
                Select(
                  Typed(
                    SplicePattern(
                      Bind(SimpleName("a"), WildcardPattern(_), aSym),
                      Nil,
                      Nil,
                      TypeRefInternal(ScalaPackageRef(), SimpleTypeName("Int"))
                    ),
                    _
                  ),
                  _
                ),
                _
              )
            ),
            Ident(SimpleName("quotes")),
            _
          ) =>
    }
    assert(containsSubtree(termQuotePatternCheck)(clue(termQuotePatternCaseDef)))

    val typeQuotePatternDef = findTree(tree) { case dd @ DefDef(SimpleName("typeQuotePattern"), _, _, _, _) =>
      dd
    }
    val typeQuotePatternCaseDef = findTree(typeQuotePatternDef) { case cd: CaseDef =>
      cd
    }
    val typeQuotePatternCheck: StructureCheck = {
      case QuotePattern(
            List(TypeTreeBind(SimpleTypeName("t"), _, tSym), TypeTreeBind(SimpleTypeName("u"), _, uSym)),
            Right(
              AppliedTypeTree(
                TypeIdent(SimpleTypeName("Map")),
                List(TypeWrapper(TypeRefInternal(NoPrefix, tSymRef)), TypeWrapper(TypeRefInternal(NoPrefix, uSymRef)))
              )
            ),
            Ident(SimpleName("quotes")),
            _
          ) if tSymRef == tSym && uSymRef == uSym && tSym != uSym =>
    }
    assert(containsSubtree(typeQuotePatternCheck)(clue(typeQuotePatternCaseDef)))
  }

  testUnpickle("anon-classes-in-constructor", "simple_trees.AnonClassesInCtor") { tree =>
    val ctorDef = findTree(tree) {
      case ctorDef @ DefDef(nme.Constructor, _, _, _, ctorSym) if ctorSym.owner.name == typeName("AnonClassesInCtor") =>
        ctorDef
    }
    val ctorSym = ctorDef.symbol

    val anonClassStructure: StructureCheck = {
      case ClassDef(SimpleTypeName("$anon"), _, sym) if sym.owner == ctorSym =>
    }
    assert(containsSubtree(anonClassStructure)(clue(tree)))
  }

  testUnpickle("double-poly-extensions", "simple_trees.DoublePolyExtensions") { tree =>
    val myMapDef = findTree(tree) { case myMapDef @ DefDef(SimpleName("+++:"), _, _, _, _) =>
      myMapDef
    }
    val myMapStructure: StructureCheck = {
      case DefDef(
            SimpleName("+++:"),
            List(
              Right(List(TypeParam(SimpleTypeName("A"), _, _))),
              Right(List(TypeParam(SimpleTypeName("B"), _, _))),
              Left(List(ValDef(SimpleName("x"), _, _, _))),
              Left(List(ValDef(SimpleName("list"), _, _, _)))
            ),
            _,
            _,
            _
          ) =>
    }
    assert(containsSubtree(myMapStructure)(clue(myMapDef)))
  }
}
