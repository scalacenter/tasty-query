package subtyping

class TypesFromTASTy:
  val listDefaultImport: List[Int] = Nil
  val listFullyQualified: scala.collection.immutable.List[Int] = Nil
  val listPackageAlias: scala.List[Int] = Nil

  val orType: Int | String = 1
  val andType: Product & Serializable = Nil

  type TToTType[T] = T => T
end TypesFromTASTy
