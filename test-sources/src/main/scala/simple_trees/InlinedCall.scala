package simple_trees

class HasInlinedMethod {
  val externalVal = 1

  class Inner {
    transparent inline def inlined(arg: Int) = arg + externalVal
  }
}

class InlinedCall {
  val withInlineMethod = HasInlinedMethod()

  new withInlineMethod.Inner().inlined(0)
}
