import scala.util.Random
import scalax.chart.module.Charting

object Benchmark extends App with Charting {

  val N = 10000
  val Step = 1000

  val sortings = Map(
    "bubble" -> BubbleSort.sort
  )

  def verify(sort: Array[Int] => Unit): Unit = {
    for (n <- 1 to 1000) {
      val array = Generators.arrays("random")(n)
      sort(array)
      for (Array(x,y) <- array.sliding(2, 1)) {
        assert(x <= y)
      }
    }
  }

  for ((_, algorithm) <- sortings) {
    verify(algorithm)
  }

  val plot =
    for {
      (algorithmLabel, sort) <- sortings.toSeq
      (generatorLabel, generator) <- Generators.arrays.toSeq
    } yield {
      val label = s"$algorithmLabel-$generatorLabel"

      val line = for (n <- (1 to N / Step).map(_ * Step)) yield {
        val array = generator(n)
        println(s"$n $label")

        val start = System.nanoTime()
        sort(array)
        val time = System.nanoTime() - start

        (n, time)
      }

      label -> line
    }

  def sqr(n: Int): Long = {
    val k: Long = n
    k * k
  }

  val marks = Seq(
    "O(n)"  -> (1 to N).map(n => (n, n * N.asInstanceOf[Long])),
    "O(n²)" -> (1 to N).map(n => (n, sqr(n))))

  val chart = XYLineChart(plot ++ marks)
  //chart.saveAsPNG(s"/home/kirillt/Desktop/bubble.png", (1024,1024))
  chart.saveAsPNG(s"chart.png", (1024,1024))

}
