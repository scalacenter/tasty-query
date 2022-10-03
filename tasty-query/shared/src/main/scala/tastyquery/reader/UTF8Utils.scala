package tastyquery.reader

import scala.annotation.targetName

import java.nio.charset.StandardCharsets

private[reader] object UTF8Utils:
  def decode(bytes: Array[Byte], offset: Int, len: Int): String =
    new String(bytes, offset, len, StandardCharsets.UTF_8)

  @targetName("decodeFromIArray")
  def decode(bytes: IArray[Byte], offset: Int, len: Int): String =
    decode(bytes.asInstanceOf[Array[Byte]], offset, len)
end UTF8Utils
