package simple_trees

/** Documentation of the class DocStrings. */
class DocStrings extends DocumentedDependency:
  /** Documentation of the type member DocumentedType. */
  type DocumentedType = Int

  /** Documentation of the value documentedValue. */
  val documentedValue: Int = 1

  /** Documentation of the method documentedMethod. */
  def documentedMethod(x: Int): Int = x + 1

  /** Documentation of the method documentedMethod.
    * Overloaded methods have separate docstrings.
    */
  def documentedMethod(x: Int, y: Int): Int = x + y

  /** Documentation with non-ASCII characters: àéîõü, 日本語, Ελληνικά. */
  def documentedWithNonAscii: Int = 4

  /** Documentation of the object DocumentedObject. */
  object DocumentedObject:
    /** Documentation of the value documentedObjectValue. */
    val documentedObjectValue: Int = 2

  def undocumentedMethod: Int = 0

  val undocumentedValue: String = "no documentation"
end DocStrings
