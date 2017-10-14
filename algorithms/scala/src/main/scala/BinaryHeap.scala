import scala.reflect.ClassTag

class BinaryHeap[T](implicit ord: T => Ordered[T], ct: ClassTag[T]) extends PriorityQueue[T] {

  private var array: Array[T] = Array[T]()
  private var limit: Int = 0
  private var size: Int = 0

  override def isEmpty: Boolean = limit < 0

  override def push(w: T): Unit = {
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
  }

  override def pop(): T = {
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

  private def resize(n: Int): BinaryHeap[T] = {
    val fresh: Array[T] = Array.ofDim[T](n)
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
    val x = array(i)
    array(i) = array(j)
    array(j) = x
  }

}

object BinaryHeap {

  def apply[T]()
      (implicit ord: T => Ordered[T], ct: ClassTag[T]): BinaryHeap[T] =
    BinaryHeap[T](4)

  def apply[T](size: Int)
      (implicit ord: T => Ordered[T], ct: ClassTag[T]): BinaryHeap[T] =
    new BinaryHeap[T]().resize(size)

  def apply[T](ws: Seq[T])
      (implicit ord: T => Ordered[T], ct: ClassTag[T]): BinaryHeap[T] = {
    val heap = BinaryHeap[T](ws.size)
    for (w <- ws) {
      heap.push(w)
    }
    heap
  }

}
