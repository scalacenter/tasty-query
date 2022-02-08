package tastyquery.util

object syntax {

  object chaining {
    given Chaining: AnyRef with {
      extension [T](t: T) inline def andThen(inline tap: => Unit): T = { tap; t }
    }
  }

}
