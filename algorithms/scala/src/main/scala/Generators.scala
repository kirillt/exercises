import scala.util.Random

object Generators {

  val arrays: Map[String, Int => Array[Int]] = Map(
    "sorted" -> ((n: Int) => Array[Int](1 to n :_*)),
    "random" -> ((n: Int) => Array[Int]((1 to n)
      .map(_ => Random.nextInt(100)) :_*)))

  val sequences: Map[String, Int => Seq[Int]] =
    arrays.mapValues(gen => n => gen(n).toSeq)

}
