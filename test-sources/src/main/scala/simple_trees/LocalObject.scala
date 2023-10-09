package simple_trees

class LocalObject:
  def method(): Unit =
    object MyLocalObject

    class Inner:
      def foo(obj: MyLocalObject.type): MyLocalObject.type = obj

      foo(MyLocalObject)
  end method
end LocalObject
