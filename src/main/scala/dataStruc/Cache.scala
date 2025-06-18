package dataStruc
/** code récupéré de Luidnel */
object Cache {
  class IndexedElement[E] (
       var index: Int, var element: E, var next: Cache.IndexedElement[E]) {
  }
}

class Cache[E] {
   var nextIndex = 0
   var top: Cache.IndexedElement[E] = null
  def reset()={ nextIndex = 0;top=null}
  def push(element: E): Unit = {
    var i = 16
    if (nextIndex % i == 0) {
      i = i * 2
      top = new Cache.IndexedElement[E](nextIndex, element, top)
      var e = top
        while (e.next != null && e.next.index % i == 0) {
        i = i * 2
        e = e.next
      }
      if (e.next != null) e.next = e.next.next
    }
    nextIndex += 1
  }

  def pop(n: Int): E = {
    while (top != null && top.index >= nextIndex - n) top = top.next
    nextIndex = if (top == null) 0
    else top.index + 1
     top.element

  }


  //def nextIndex: Int = nextIndex

  def size: Int = {
    var counter = 0
    var e = top
    while (e != null) {
      counter += 1
      e = e.next
    }
    counter
  }
}
