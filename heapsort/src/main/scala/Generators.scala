import scala.util.Random

object Generators {

  val arrays: Map[String, Long => Array[Int]] = Map(
    "random" -> ((n: Long) => Array[Int](random(n) :_*)),
    "sorted" -> ((n: Long) => Array[Int](sorted(n) :_*)))

  val sequences: Map[String, Long => Seq[Int]] =
    arrays.mapValues(gen => n => gen(n).toSeq)

  def sorted(n: Long): Seq[Int] =
    random(n).sorted

  def random(n: Long): Seq[Int] =
    (1L to n).map(_ => Random.nextInt(100))

}
