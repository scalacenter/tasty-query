package inheritance

object PrivateOverrides:
  class Parent(val x: Int):
    val w = 1
    val y = 2

  class Child(x: Int, y: Int, val z: Int) extends Parent(20):
    def readIdentW: Int = w // Parent.w
    def readIdentX: Int = x // Child.x
    def readIdentY: Int = y // Child.y
    def readIdentZ: Int = z // Child.z

    def readThisW: Int = this.w // Parent.w
    def readThisX: Int = this.x // Child.x
    def readThisY: Int = this.y // Child.y
    def readThisZ: Int = this.z // Child.z

    def readSelfW: Int =
      val self: this.type = this
      self.w // Parent.w

    def readSelfX: Int =
      val self: this.type = this
      self.x // Parent.x

    def readSelfY: Int =
      val self: this.type = this
      self.y // Parent.y

    def readSelfZ: Int =
      val self: this.type = this
      self.z // Child.z

    class Inner(y: Int, z: Int):
      def readIdentW: Int = w // Parent.w
      def readIdentX: Int = x // Child.x
      def readIdentY: Int = y // Inner.y
      def readIdentZ: Int = z // Inner.z

      def readChildThisW: Int = Child.this.w // Parent.w
      def readChildThisX: Int = Child.this.x // Child.x
      def readChildThisY: Int = Child.this.y // Child.y
      def readChildThisZ: Int = Child.this.z // Child.z

      // this.w does not compile
      // this.x does not compile
      def readThisY: Int = this.y // Inner.y
      def readThisZ: Int = this.z // Inner.z
    end Inner
  end Child

  def testSetup(): Int =
    val child = new Child(1, 11, 111)
    val w = child.w // Parent.w
    val x = child.x // Parent.x
    val y = child.y // Parent.y
    val z = child.z // Child.z
    w + x + y + z
end PrivateOverrides
