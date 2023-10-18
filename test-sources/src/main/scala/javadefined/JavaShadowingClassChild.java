package javadefined;

public class JavaShadowingClassChild extends JavaShadowingClassParent {
  public class InnerClass {
    public int bar() {
      return 2;
    }
  }

  public InnerClass makeChildInnerClass() {
    return new InnerClass();
  }

  public JavaShadowingClassParent.InnerClass makeOtherParentInnerClass() {
    return new JavaShadowingClassParent.InnerClass();
  }
}
