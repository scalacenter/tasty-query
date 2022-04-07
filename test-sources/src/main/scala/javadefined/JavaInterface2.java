package javadefined;

public interface JavaInterface2 {
  int Y = 23;

  default int getY() {
    return Y;
  }
}
