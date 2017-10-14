object HeapSort {

  def sort: Array[Int] => Unit = {
    array =>
      val heap = BinaryHeap[Int](array)
      for (i <- array.indices.reverse) {
        array(i) = heap.pop()
      }
  }

}
