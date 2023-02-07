package crosspackagetasty

opaque type TopLevelOpaqueTypeAlias <: AnyVal = Int

object TopLevelOpaqueTypeAlias:
  def apply(x: Int): TopLevelOpaqueTypeAlias = x
end TopLevelOpaqueTypeAlias
