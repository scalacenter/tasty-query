package simple_trees

class ClassWithSelf extends TraitWithSelf {
  self =>
}

trait TraitWithSelf {
  self: ClassWithSelf =>
}
