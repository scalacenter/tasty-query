package tastyquery.util

object syntax {

  object chaining {
    given Chaining: AnyRef with {
      extension [T](inline t: T)

        inline def andThen(inline after: Unit): T = useWith(_ => after)

        inline def useWith(inline tap: T => Unit): T =
          val res = t
          tap(res)
          res

    }
  }

}
