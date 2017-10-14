trait PriorityQueue[T] {

  def isEmpty: Boolean

  def push(weight: T): Unit

  def pop(): T

}