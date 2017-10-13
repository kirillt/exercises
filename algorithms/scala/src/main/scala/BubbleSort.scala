object BubbleSort {

  def sort: Array[Int] => Unit = {
    array =>
      val n = array.length
      for (i <- array.indices) {
        for (j <- i+1 until n) {
          val ai = array(i)
          val aj = array(j)
          if (ai > aj) {
            array(i) = aj
            array(j) = ai
          }
        }
      }
  }

}
