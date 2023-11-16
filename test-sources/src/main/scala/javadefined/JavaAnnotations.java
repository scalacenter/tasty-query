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
}
