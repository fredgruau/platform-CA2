package dataStruc


trait Vertex[V<: Vertex[V,E],E<:Edge[V,E]] {
  def  inNeighbors: List[E]
  var  outNeighbors: List[E]=List()
  def neighbors=inNeighbors++outNeighbors
  def neighborsV: List[V] =inNeighbors.map(e=> e.in ) ++ outNeighbors.map(e=> e.out)
  def InNeighborsV: Seq[V] =   inNeighbors.map(e => e.in )
  def setInNeighborsV:   Set[V] = Set.empty ++ inNeighbors.map(e=> e.in )
   def neighborsEV:  List[(E, V)] =neighbors.zip(neighborsV)
  /** used to make a sorted list of vertices */
  var visited=false
  def name:String
}

trait Edge[V<: Vertex[V,E],E<:Edge[V,E]] {
  def in:V
  def out: V
  /** used to make a sorted list of edges */
  var visited=false
}

/**
 *
 * @param nodes the graph's node
 * @param edges all the graph's edges
 * @tparam V the type of the node
 * @tparam E the type of the edge
 */
class Graph[V<: Vertex[V,E],E<:Edge[V,E]]( val nodes:List[V],val edges:List[E]){
}

object Graph{
  /** @param maximals nodes that do not have output neighbors, except among themselves
   * @return Graph with node topologically sorted from input to ouput, (if there is no cycles)
   */
  def apply[V <: Vertex[V, E], E <: Edge[V, E]](maximals: List[V]): Graph[V, E] = {
    var listEdge: List[E] = List();
    var listVertex: List[V] = List();
    val pointedByMaximal = maximals.map(_.setInNeighborsV).reduce((x, y) => x.union(y))
    val trueMaximals = maximals.filter(!pointedByMaximal.contains(_))
    var listVertexCur = trueMaximals
    while (!listVertexCur.isEmpty) {
      listVertexCur.map(_.visited = true);
      listVertex = listVertexCur ++ listVertex
      val newEdges = listVertexCur.flatMap(_.inNeighbors).filter(!_.visited)
      listEdge = newEdges ++ listEdge;
      newEdges.map(_.visited = true)
      listVertexCur = newEdges.map(_.in)
      if (!listVertexCur.filter(_.visited).isEmpty) throw new RuntimeException("there is a cycle between zones" + listVertexCur) //we must look more in details
      listVertexCur = listVertexCur.filter(!_.visited)
    };
    new Graph(listVertex, listEdge)
  }
  /**
   *
   * @param maximals nodes that do not have output neighbors, except among themselves
   *                 hence we need to first compute trueMaximals.
   * @tparam V type of nodes
   * @tparam E type of edges
   * @return
   */
  def getSmaller[V<: Vertex[V,E],E<:Edge[V,E]](maximals: List[V] ):(List[E], List[V]) =
  { var listEdge:List[E]=List();
    var listVertex:List[V]=List();
    val pointedByMaximal= maximals.map(_.setInNeighborsV).reduce((x,y)=>x.union(y))
    val trueMaximals=maximals.filter(!pointedByMaximal.contains(_))
    var listVertexCur=trueMaximals
    while(!listVertexCur.isEmpty){
      listVertexCur.map(_.visited=true);
      listVertex = listVertexCur ++ listVertex
      val newEdges=listVertexCur.flatMap(_.inNeighbors).filter(!_.visited)
      listEdge=newEdges ++ listEdge;  newEdges.map(_.visited=true)
      listVertexCur=newEdges.map(_.in)
      if (!listVertexCur.filter(_.visited).isEmpty )  throw new RuntimeException("there is a cycle between zones"+listVertexCur) //we must look more in details
      listVertexCur= listVertexCur.filter(!_.visited)
    } ; (listEdge,listVertex)
  }
   //def getSmallerInIncreasingOrder[V<: Vertex[V,E],E<:Edge[V,E]](maximals: List[V] ):Tuple2[List[E],List[V]] =
  // { val (e,v)= getSmaller(maximals);(e.reverse,v.reverse) }
}
