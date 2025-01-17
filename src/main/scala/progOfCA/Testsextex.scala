package progOfCA

import compiler.ASTBfun.andRedop
import compiler.ASTLfun.{concatR, e, elt, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, UintV, UintVe}
import compiler.{B, E, V}
import dataStruc.BranchNamed
import sdn.Util.{addLt, addSym, addSymUI, randUintV}

/** tests the lt macro, containts a bugif */
class   Testsextex() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 // val rand1 = new Rand();  val rand2 = new Rand()
  val prioRand = randUintV(3) //rand1::rand2
  val toto=addLt(prioRand)
  val voisins: UintVe =addSymUI(e(prioRand)).symUI  // symUI est un boolVe qui  va contenir les voisins
 val nasI: UintV = concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
 val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
 val (n6, n7, n8, n9, n10, n11) =(elt(6, nasI),elt(7, nasI),elt(8, nasI),elt(9, nasI),elt(10, nasI),elt(11, nasI))  //aprés on les numérote
 val(n12, n13, n14, n15, n16, n17)=(elt(12, nasI),elt(13, nasI),elt(14, nasI),elt(15, nasI),elt(16, nasI),elt(17, nasI)) // aprés on les numérote
 val (east,se,sw)=(n0.asInstanceOf[UintV]::n1::n2, n3.asInstanceOf[UintV]::n4::n5,n6.asInstanceOf[UintV]::n7::n8) //puis on fait les paquets
 val (west,nw,ne)=(n9.asInstanceOf[UintV]::n10::n11, n12.asInstanceOf[UintV]::n13::n14,n15.asInstanceOf[UintV]::n16::n17)
//a ce stade on a reconstruit les 6 voisins.
 //on calcule les comparaison deux a deux des couples de voisin adjacent: (east,se) (sw,w) (nw,ne)
 //d'abord le résultat des comparaisons


 show(voisins,nasI,prioRand,east,se,sw,west,nw,ne)
 //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
 //val (lt,eq)= Grad.slopeLt(prioRand)
//,toto.eq,toto.lt,toto.gt);
} //root classe compilable

