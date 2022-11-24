package javadefined;

import javadefined.GenericJavaClass;
import javadefined.JavaDefined;
import mixjavascala.ScalaGenOuter;
import mixjavascala.ScalaStaticOuter;

public class BagOfGenJavaDefinitions {

  public GenericJavaClass<JavaDefined> x; // Ljavadefined/GenericJavaClass<Ljavadefined/JavaDefined;>;

  public BagOfGenJavaDefinitions(GenericJavaClass<JavaDefined> x) {
    this.x = x;
  }

  public GenericJavaClass<JavaDefined> getX() {
    // ()Ljavadefined/GenericJavaClass<Ljavadefined/JavaDefined;>;
    return x;
  }

  public GenericJavaClass<JavaDefined>[] getXArray() {
    // ()[Ljavadefined/GenericJavaClass<Ljavadefined/JavaDefined;>;
    return new GenericJavaClass[] { x };
  }

  public <X extends Exception, Y extends Exception> void printX(X x) throws X, Y {
    // <X:Ljava/lang/Exception;Y:Ljava/lang/Exception;>(TX;)V^TX;^TY;
    throw x;
  }

  public <A extends GenericJavaClass<Y>, Y> void recTypeParams() {
    // <A:Ljavadefined/GenericJavaClass<TY;>;Y:Ljava/lang/Object;>()V
  }

  public <A extends JavaInterface1 & JavaInterface2> void refInterface() {
    // <A::Ljavadefined/JavaInterface1;:Ljavadefined/JavaInterface2;>()V
  }

  public GenericJavaClass<JavaDefined>.MyInner<JavaDefined> getInner() {
    // ()Ljavadefined/GenericJavaClass<Ljavadefined/JavaDefined;>.MyInner<Ljavadefined/JavaDefined;>;
    return null;
  }

  public ScalaGenOuter<JavaDefined>.InnerGenClass<JavaDefined> getScalaInner() {
    // ()Lmixjavascala.ScalaGenOuter<Ljavadefined/JavaDefined;>.InnerGenClass<Ljavadefined/JavaDefined;>;
    return null;
  }

  public ScalaStaticOuter.StaticInnerGenClass<JavaDefined> getScalaStaticInner() {
    // ()Lmixjavascala.ScalaStaticOuter$StaticInnerGenClass<Ljavadefined/JavaDefined;>;
    return null;
  }

  public GenericJavaClass.MyStaticInner<JavaDefined> getStaticInner() {
    // ()Ljavadefined/GenericJavaClass$MyStaticInner<Ljavadefined/JavaDefined;>;
    //                                ^ note the $ in the name, aka inner class name is mangled.
    return null;
  }

  public JavaDefined.MyInner.MyInnerInner.MyInnerInnerGenInner<JavaDefined> getAbsurdInner() {
    // ()Ljavadefined.JavaDefined$MyInner$MyInnerInner$MyInnerInnerGenInner<Ljavadefined/JavaDefined;>;
    //                           ^       ^            ^
    //                           note the $ in the name, aka inner class names are mangled.
    return null;
  }

  public JavaDefined.MyGenInner<JavaDefined>.MyInnerInner.MyInnerInnerInner getAbsurdInner2() {
    // ()Ljavadefined.JavaDefined$MyGenInner<Ljavadefined/JavaDefined;>.MyInnerInner.MyInnerInnerInner;
    //                                                                 ^            ^
    //                                       note that after the first type args, switch to `.` instead of `$`.
    return null;
  }

  public JavaDefined.MyStaticGenInner.MyStaticGenInnerInner.MyStaticGenInnerInnerInner<JavaDefined> getAbsurdInner3() {
    // ()Ljavadefined.JavaDefined$MyStaticGenInner$MyStaticGenInnerInner$MyStaticGenInnerInnerInner<javadefined.JavaDefined>;
    return null;
  }

  // public GenericJavaClass<JavaDefined>.MyInner<JavaDefined> getInner() {
  // 	// ()Ljavadefined/GenericJavaClass<Ljavadefined/JavaDefined;>.MyInner<Ljavadefined/JavaDefined;>;
  // 	return null;
  // }

  public GenericJavaClass genraw; // no signature attribute
  public GenericJavaClass<GenericJavaClass> mixgenraw; // Ljavadefined/GenericJavaClass<Ljavadefined/GenericJavaClass;>;
  public GenericJavaClass<?> genwild; // Ljavadefined/GenericJavaClass<*>;
  public GenericJavaClass<? extends JavaDefined> gencovarient; // Ljavadefined/GenericJavaClass<+Ljavadefined/JavaDefined;>;
  public GenericJavaClass<? super JavaDefined> gencontravarient; // Ljavadefined/GenericJavaClass<-Ljavadefined/JavaDefined;>;
}
