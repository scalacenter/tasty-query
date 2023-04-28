package simple_trees

class AnonClassesInCtor:
  def f(runnable: Runnable): Unit = runnable.run()

  // Two anonymous classes in the constructor
  f(new Runnable {
    def run(): Unit = println(1)
  })
  f(new Runnable {
    def run(): Unit = println(2)
  })
end AnonClassesInCtor
