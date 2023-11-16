package javadefined;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
public @interface JavaAnnotMultiValues {
  int foo() default 1;
  boolean bar();
}
