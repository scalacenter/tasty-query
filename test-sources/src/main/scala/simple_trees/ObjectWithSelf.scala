package simple_trees

object ObjectWithSelf:
  object StaticObjectNoSelf:
    def foo: Any = this
    def bar: Any = this.foo
  end StaticObjectNoSelf

  object StaticObjectWithSelf:
    self =>

    def foo: Any = self
    def bar: Any = self.foo
  end StaticObjectWithSelf

  class Container:
    object NonStaticObjectNoSelf:
      def foo: Any = this
      def bar: Any = this.foo
    end NonStaticObjectNoSelf

    object NonStaticObjectWithSelf:
      self =>

      def foo: Any = self
      def bar: Any = self.foo // used to cause StackOverflow while resolving this in WholeClasspathSuite tests
    end NonStaticObjectWithSelf
  end Container

  def methodOwner(): Unit =
    object LocalObjectNoSelf:
      def foo: Any = this
      def bar: Any = this.foo
    end LocalObjectNoSelf

    object LocalObjectWithSelf:
      self =>

      def foo: Any = self
      def bar: Any = self.foo
    end LocalObjectWithSelf
  end methodOwner
end ObjectWithSelf
