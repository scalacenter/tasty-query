package javadefined;

public class GenericJavaClass<T> {
  public T x; // ()TT; // Aka can refer to type parameter of the outer class

  public GenericJavaClass(T x) {
    this.x = x;
  }

  public T getX() {
    return x;
  }

  public class MyInner<U> {
    T getX() {
      return x; // this will throw ClassCastException when called on the result of shadowedParam if !(T =:= U)
    }
  }

  public static class MyStaticInner<U> {}

  // public <V> MyInner<V> getInner() {
  //   return new MyInner(); // <V:Ljava/lang/Object;>()Ljavadefined/GenericJavaClass<TT;>.MyInner<TV;>;
  // }

  // public <T> MyInner<T> shadowedParam() {
  //   // yes `T` is shadowing `T` in the outer class, this is dangerous!
  //   return new MyInner(); // <T:Ljava/lang/Object;>()Ljavadefined/GenericJavaClass<TT;>.MyInner<TT;>;
  // }

  // public void nested() {
  //   class MyLocal {
  //     T x; // ()TT; // Aka can refer to type parameter of the outer class

  //     MyLocal(T x) {
  //       this.x = x;
  //     }

  //     T getX() {
  //       return x;
  //     }
  //   }
  // }
}
