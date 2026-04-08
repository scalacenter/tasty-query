package simple_trees

case class Wrapper(value: Option[String])

class NamedExtractorPattern {
  def extract(items: List[Wrapper]): List[String] =
    items.collect { case Wrapper(value = Some(v)) => v }
}
