package compiler

/**A Connected component of affectations either of spatial type transfer (<:TT) or E,V,T, whose schedule are aligned:
 * the spatial mu component are evaluated one after the   other for all the instructions */

import scala.collection._

class Zone[+T<:Locus](//val affs:Iterable[Affect[_<:T]],val root: Affect[_<:T], a zone does not need to know its instructions, apriori.
   val neighbor:immutable.HashSet[Zone[_]]){
}