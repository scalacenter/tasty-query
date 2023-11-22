package javadefined;

import java.util.concurrent.TimeUnit;

@JavaAnnotWithDefault
@JavaAnnotSingleValue(5)
@JavaAnnotMultiValues(foo = 5, bar = true)
@JavaAnnotArrayValue({ 2, 3, 5, 7 })
@JavaAnnotEnumValue(TimeUnit.MINUTES)
@JavaAnnotClassValue(short.class)
@JavaAnnotAnnotValue(@JavaAnnotSingleValue(42))
@JavaAnnotClassRetention
public class JavaAnnotations {
  @JavaAnnotWithDefault(false)
  @JavaAnnotSingleValue(10)
  @JavaAnnotMultiValues(bar = true, foo = 5)
  @JavaAnnotClassValue(CharSequence.class)
  @JavaAnnotClassRetention
  public int annotatedField;

  @JavaAnnotClassValue(void.class)
  @JavaAnnotClassRetention
  public int annotatedMethod() {
    return 1;
  }

  @JavaAnnotClassValue(java.util.List.class)
  public int otherAnnotatedMethod() {
    return 1;
  }

  public <T> int annotatedParams(
    int noAnnot,
    @JavaAnnotSingleValue(123)
    T oneAnnot,
    @JavaAnnotClassValue(String[].class)
    @JavaAnnotClassRetention
    String severalAnnots,
    @JavaAnnotWithDefault
    int oneMoreParam
  ) {
    return noAnnot;
  }
}
