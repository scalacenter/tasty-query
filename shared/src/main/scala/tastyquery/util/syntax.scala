package tastyquery.util

object syntax {

  object chaining {
    given Chaining: AnyRef with {
      extension [T](t: T) inline def andThen(inline after: => Unit): T = { after; t }
      extension [T](t: T) inline def useWith(inline tap: T => Unit): T = { tap(t); t }
    }
  }

}
