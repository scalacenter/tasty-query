package simple_trees

class QualThisType {
  class Inner {
    def withOp(op: Inner => Unit): Unit = op(Inner())
  }
}
