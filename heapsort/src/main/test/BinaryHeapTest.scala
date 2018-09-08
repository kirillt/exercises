object BinaryHeapTest extends App {

  val N = 100

  for (n <- 1 to N; _ <- 1 to 10) {
    val input = Generators.sequences("random")(n)
    val heap = BinaryHeap(input)
    val sorted = input.sortWith(_ > _)
    for (x <- sorted) {
      assert(heap.pop() == x)
    }
  }

}
