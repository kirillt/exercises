trait PriorityQueue {

  def isEmpty: Boolean

  def push(weight: Int): PriorityQueue

  def pop(): Int

}