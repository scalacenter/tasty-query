package inheritance

object CtorParamsNormalization:
  private given TheInt: Int = 5

  class SuperClassNoNorm()(using x: Int)

  trait SuperTraitNoNorm()(using x: Int)

  class SuperClassWithNorm(using x: Int)

  trait SuperTraitWithNorm(using x: Int)

  class Sub1 extends SuperClassNoNorm with SuperTraitNoNorm
  class Sub2 extends SuperClassWithNorm with SuperTraitNoNorm
  class Sub3 extends SuperClassNoNorm with SuperTraitWithNorm
  class Sub4 extends SuperClassWithNorm with SuperTraitWithNorm

  class PolySuperClassNoNorm[T]()(using x: T)

  trait PolySuperTraitNoNorm[T]()(using x: T)

  class PolySuperClassWithNorm[T](using x: T)

  trait PolySuperTraitWithNorm[T](using x: T)

  class PolySub1 extends PolySuperClassNoNorm[Int] with PolySuperTraitNoNorm[Int]
  class PolySub2 extends PolySuperClassWithNorm[Int] with PolySuperTraitNoNorm[Int]
  class PolySub3 extends PolySuperClassNoNorm[Int] with PolySuperTraitWithNorm[Int]
  class PolySub4 extends PolySuperClassWithNorm[Int] with PolySuperTraitWithNorm[Int]
end CtorParamsNormalization
