package javacompat

class InferredFromJavaObject:
  // inferred as FromJavaObject
  def atTopLevel = java.lang.reflect.Array.get(Array[String]("foo"), 0)

  // inferred as Array[FromJavaObject]
  def inArray = new java.util.LinkedList[String]().toArray()
end InferredFromJavaObject
