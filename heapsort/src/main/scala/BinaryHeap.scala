class BinaryHeap extends PriorityQueue {

  private var array: Array[Int] = Array()
  private var limit: Int = 0
  private var size: Int = 0

  override def isEmpty: Boolean = limit < 0

  override def push(w: Int): BinaryHeap = {
    if (limit >= size) {
      resize(size * 2)
    }

    var i = limit
    limit += 1

    array(i) = w
    var p = parent(i)
    while (i > 0 && array(p) < array(i)) {
      swap(p, i)
      i = p
      p = parent(i)
    }
    this
  }

  override def pop(): Int = {
    val value = array(0)

    limit -= 1
    array(0) = array(limit)
    if (limit < size / 2) {
      resize(size / 2)
    }

    var p = 0
    var m = largest(p)
    while (p < limit && p != m) {
      swap(p, m)
      p = m
      m = largest(p)
    }

    value
  }

  private def resize(n: Int): BinaryHeap = {
    val fresh: Array[Int] = Array.ofDim(n)
    array.copyToArray(fresh, 0, Math.min(n, size))
    array = fresh
    size = n
    this
  }

  private def parent(i: Int): Int =
    (i - 1) / 2

  private def left(p: Int): Int =
    p * 2 + 1

  private def right(p: Int): Int =
    (p + 1) * 2

  private def largest(p: Int): Int = {
    val l = left(p)
    val r = right(p)
    var k = p
    if (l < limit && array(l) > array(k)) k = l
    if (r < limit && array(r) > array(k)) k = r
    k
  }

  private def swap(i: Int, j : Int) = {
    array(i) = array(i) ^ array(j)
    array(j) = array(i) ^ array(j)
    array(i) = array(i) ^ array(j)
  }

}

object BinaryHeap {

  def apply(): BinaryHeap =
    BinaryHeap(4)

  def apply(size: Int): BinaryHeap =
    new BinaryHeap().resize(size)

  def apply(ws: Seq[Int]): BinaryHeap = {
    val heap = BinaryHeap(ws.size)
    for (w <- ws) {
      heap.push(w)
    }
    heap
  }

}
