package simple_trees

object PredefMethods:
  def test(): Unit =
    val x = valueOf[5]
    assert(x == 5)

    val obj: List[Int] | Null = List(1, 2)
    assert(obj.nn.size == 2, "with message")
    assert(Predef.eq(obj)(obj))
    assert(Predef.ne(obj)(List(1, 2)))

    println(summon[DummyImplicit])
  end test
end PredefMethods
