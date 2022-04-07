package javadefined;

public interface JavaInterface1 {
  int X = 23;

  default int getX() {
    return X;
  }
}
