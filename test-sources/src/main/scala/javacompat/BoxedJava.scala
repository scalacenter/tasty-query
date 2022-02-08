package javacompat

class BoxedJava(val boxed: javadefined.JavaDefined) {
  def xMethod = boxed.getX()
  def xField = boxed.x
}
