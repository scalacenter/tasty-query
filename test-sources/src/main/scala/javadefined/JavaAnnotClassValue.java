package javadefined;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

@Retention(RetentionPolicy.RUNTIME)
public @interface JavaAnnotClassValue {
  Class<?> value();
}
