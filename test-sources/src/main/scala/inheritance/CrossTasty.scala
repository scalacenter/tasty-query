package inheritance

abstract class CrossTasty:
  def foo: Int = 23

/** Defined in a separate tasty file to CrossTasty */
class SubCrossTasty extends CrossTasty
