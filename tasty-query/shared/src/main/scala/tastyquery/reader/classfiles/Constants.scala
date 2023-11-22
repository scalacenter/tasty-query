package tastyquery.reader.classfiles

import tastyquery.Names.*

private[classfiles] object Constants:
  object attr:
    val TASTY = termName("TASTY")
    val Scala = termName("Scala")
    val ScalaSig = termName("ScalaSig")
    val InnerClasses = termName("InnerClasses")
    val MethodParameters = termName("MethodParameters")
    val RuntimeVisibleAnnotations = termName("RuntimeVisibleAnnotations") // RetentionPolicy.RUNTIME
    val RuntimeInvisibleAnnotations = termName("RuntimeInvisibleAnnotations") // RetentionPolicy.CLASS
    val RuntimeVisibleParameterAnnotations = termName("RuntimeVisibleParameterAnnotations")
    val RuntimeInvisibleParameterAnnotations = termName("RuntimeInvisibleParameterAnnotations")
    val Signature = termName("Signature")
  end attr

  object annot:
    val ScalaSignature = termName("Lscala/reflect/ScalaSignature;")
    val ScalaLongSignature = termName("Lscala/reflect/ScalaLongSignature;")
  end annot
end Constants
