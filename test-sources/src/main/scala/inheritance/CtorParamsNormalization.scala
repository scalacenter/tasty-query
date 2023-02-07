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
end CtorParamsNormalization
