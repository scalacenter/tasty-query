package javadefined;

import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;

import java.util.concurrent.TimeUnit;

@Retention(RetentionPolicy.RUNTIME)
public @interface JavaAnnotEnumValue {
  TimeUnit value();
}
