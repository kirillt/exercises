object Sortings {

  val default: Array[Int] => Unit = { array =>
    array.sorted.copyToArray(array)
  }

  val algorithms: Map[String, Array[Int] => Unit] =
    Map("standard" -> default,
        "heapsort" -> HeapSort.sort,
        "bubble" -> BubbleSort.sort)

}
