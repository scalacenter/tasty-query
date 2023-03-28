val toplevel = 123

class ClassInEmptyPackage {
  def meth(c: ClassInEmptyPackage): Int = toplevel
}
