package javadefined;

public class JavaShadowingClassParent {
  public class InnerClass {
    public int foo() {
      return 1;
    }
  }

  public InnerClass makeParentInnerClass() {
    return new InnerClass();
  }
}
