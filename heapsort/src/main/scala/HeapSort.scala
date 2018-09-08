object HeapSort {

  val sort: Array[Int] => Unit = {
    array =>
      val heap = BinaryHeap(array)
      for (i <- array.indices.reverse) {
        array(i) = heap.pop()
      }
  }

}
