package javadefined;

import mixjavascala.ScalaStaticOuter;
import mixjavascala.ScalaOuter;

public class BagOfJavaDefinitions {
  public int x;

  protected int protectedY;
  private int privateZ;

  public static int STATIC_INT = 1;

  public static int defaultInt() {
    return 1;
  }

  static int packagePrivateIntField = 1;
  static int packagePrivateIntMethod() {
    return 1;
  }

  public BagOfJavaDefinitions recField;

  public JavaDefined.MyInner innerClassField;
  public JavaDefined.MyStaticInner staticInnerClassField;

  public MyOwnInner outerRefToInner;
  public MyOwnStaticInner outerRefToStaticInner;

  ScalaStaticOuter.StaticInnerClass scalaStaticInnerRefFromJava;
  ScalaOuter.InnerClass scalaInnerRefFromJava;

  public BagOfJavaDefinitions(int x) {
    this.x = x;
  }

  public void printX() {
    System.out.println(x);
  }

  public int[] wrapXArray() {
    return new int[] { x };
  }

  public javadefined.JavaDefined[] arrIdentity(javadefined.JavaDefined[] arr) {
    return arr;
  }

  public java.lang.ProcessBuilder processBuilder() {
    return new ProcessBuilder("echo");
  }

  public class MyOwnInner {

    public int getX() {
      return x;
    }
  }

  public static class MyOwnStaticInner {

    public int getX() {
      return 0;
    }
  }
}
