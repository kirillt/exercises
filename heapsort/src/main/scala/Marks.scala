import language.postfixOps

object Marks {

  type Line = Seq[(Long, Long)]

  def lines(N: Long, K: Long): Map[String, Line] = {
    def scale(line: Line, ratio: Long) = line.map {
      case (x, y) => (x, y * ratio)
    }

    def crop(line: Line) = line.filter {
      case (x, y) => y <= K
    }

    Map("10 * n" -> scale(n(N), 10),
        "10 * n log² n" -> scale(nSqrLog(N), 10),
        "10 * n log n" -> scale(nLog(N), 10),
        "n²" -> sqr(N))
      .mapValues(crop)
  }

  def n(N: Long): Line =
    (1L to N).map { x => x -> x }

  def sqr(N: Long): Line =
    (1L to N).map { x => x -> x * x }

  def nLog(N: Long): Line =
    n(N).map { case (x,y) =>
      x -> Math.round(y * Math.log(x))
    }

  def nSqrLog(N: Long): Line =
    n(N).map { case (x,y) =>
      val l = Math.log(x)
      x -> Math.round(y * l * l)
    }

}
