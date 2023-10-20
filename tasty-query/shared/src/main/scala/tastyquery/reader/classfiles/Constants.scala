package tastyquery.reader.classfiles

import tastyquery.Names.*

private[classfiles] object Constants:
  object attr:
    val TASTY = termName("TASTY")
    val Scala = termName("Scala")
    val ScalaSig = termName("ScalaSig")
    val InnerClasses = termName("InnerClasses")
    val RuntimeVisibleAnnotations = termName("RuntimeVisibleAnnotations") // RetentionPolicy.RUNTIME
    val Signature = termName("Signature")
  end attr

  object annot:
    val ScalaSignature = termName("Lscala/reflect/ScalaSignature;")
    val ScalaLongSignature = termName("Lscala/reflect/ScalaLongSignature;")
  end annot
end Constants
