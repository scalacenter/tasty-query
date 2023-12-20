package simple_trees

class ValueClassNonVal(self: String) extends AnyVal:
  def get: String = self

  def getThroughThis: String = this.self
end ValueClassNonVal
