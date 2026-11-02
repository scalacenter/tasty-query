package tastyquery.reader.tasties

import scala.collection.mutable

import TastyReader.Addr

class CommentUnpicklerTest extends munit.FunSuite:

  private def writeNat(buf: mutable.ArrayBuffer[Byte], value: Int): Unit =
    if value < 128 then buf += (value | 0x80).toByte
    else
      buf += ((value >>> 7) & 0x7f).toByte
      buf += ((value & 0x7f) | 0x80).toByte

  private def commentSection(entries: (Int, String, Int)*): TastyReader =
    val buf = new mutable.ArrayBuffer[Byte]
    for (addr, comment, span) <- entries do
      writeNat(buf, addr)
      val bytes = comment.getBytes("UTF-8")
      writeNat(buf, bytes.length)
      buf ++= bytes
      buf += ((span & 0x7f) | 0x80).toByte
    new TastyReader(buf.toArray)

  test("empty section has no comments") {
    val unpickler = new CommentUnpickler(commentSection())
    assertEquals(unpickler.commentAt(Addr(0)), None)
  }

  test("reads comments by address and ignores spans") {
    val unpickler = new CommentUnpickler(commentSection((3, "/** first */", 10), (7, "/** deuxième */", 42)))

    assertEquals(unpickler.commentAt(Addr(3)), Some("/** first */"))
    assertEquals(unpickler.commentAt(Addr(7)), Some("/** deuxième */"))
    assertEquals(unpickler.commentAt(Addr(4)), None)
  }

  test("reads comments whose length spans multiple bytes") {
    val comment = "/** " + ("x" * 200) + " */"
    val unpickler = new CommentUnpickler(commentSection((1, comment, 0)))

    assertEquals(unpickler.commentAt(Addr(1)), Some(comment))
  }

  test("returns the same comment on repeated queries") {
    val unpickler = new CommentUnpickler(commentSection((5, "/** doc */", 0)))

    assertEquals(unpickler.commentAt(Addr(5)), Some("/** doc */"))
    assertEquals(unpickler.commentAt(Addr(5)), Some("/** doc */"))
  }
end CommentUnpicklerTest
