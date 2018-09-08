import scalax.chart.module.Charting

object Benchmark extends App with Charting {

  val N: Long = 100000
  val Step: Long = 200

  def verify(sort: Array[Int] => Unit): Unit = {
    for (n <- 1 to 1000) {
      val array = Generators.arrays("random")(n)
      sort(array)
      for (Array(x,y) <- array.sliding(2, 1)) {
        assert(x <= y)
      }
    }
  }

  for ((_, algorithm) <- Sortings.algorithms) {
    verify(algorithm)
  }

  val plots =
    for {
      (algorithmLabel, sort) <- Sortings.algorithms.toSeq
      (generatorLabel, generator) <- Generators.arrays.toSeq
    } yield {
      val label = s"$algorithmLabel-$generatorLabel"

      val line = for (n <- 0L.to(N, Step).updated(0,1L)) yield {
        val array = generator(n)
        println(s"$n $label")

        val start = System.nanoTime()
        sort(array)
        val time = System.nanoTime() - start

        (n, time)
      }

      label -> line
    }

  val K = plots.map(_._2).flatMap(_.map(_._2)).max

  val chart = XYLineChart(plots ++ Marks.lines(N, K))
  chart.saveAsPNG(s"chart.png")

}
