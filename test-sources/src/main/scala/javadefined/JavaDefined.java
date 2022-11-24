package javadefined;

public class JavaDefined {
  public int x;

  public JavaDefined(int x) {
    this.x = x;
  }

  public int getX() {
    return x;
  }

  public class MyInner {
    public class MyInnerInner {
      public class MyInnerInnerGenInner<U> {}
    }
  }

  public static class MyStaticInner {

    public int getX() {
      return 0;
    }
  }

  public class MyGenInner<T> {
    public class MyInnerInner {
      public class MyInnerInnerInner {}
    }
  }
  public static class MyStaticGenInner<T> {
    public static class MyStaticGenInnerInner<U> {
      public static class MyStaticGenInnerInnerInner<V> {}
    }
  }

}
