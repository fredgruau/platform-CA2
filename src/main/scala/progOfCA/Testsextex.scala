package progOfCA

import compiler.ASTB.False
import compiler.ASTBfun.andRedop
import compiler.ASTL.send
import compiler.ASTLfun.{concatR, cond, e, elt, lt2, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV, BoolVe, UintV, UintVe}
import compiler.{ASTLt, B, E, V}
import dataStruc.BranchNamed
import sdn.Util.{addLt, addSym, addSymUI, randUintV}
import compiler.ASTLfun._
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
 val eastlt=lt2(east,se)
 val eastmin=cond(eastlt,east,se)
 val westlt=lt2(sw,west)
 val westmin=cond(westlt,sw,west)
 val northlt=lt2(nw,ne)
 val northmin=cond(northlt,nw,ne)
 val southlt=lt2(eastmin, westmin)
 val southmin=cond(southlt,eastmin,westmin)
 val allLt=lt2(southmin,northmin)
 //val firstStage=Array(~eastlt,eastlt,~westlt,westlt,~northlt,northlt)
val f:BoolV=false
 val firstStage: Array[ASTLt[V, B]]=Array(f,f,f,f,northlt,~northlt)
 val secondStage: Array[ASTLt[V, B]] =Array(southlt,~southlt)
 val thirdStage=Array(allLt,~allLt)
 val sextexInt=(0 to 5).map((i:Int)=>{ //on traite pas encore correctement les cas d'égalité, ca va venir, un peu de patience
  val stage1=firstStage(i)
  val stage2=if(i>3)stage1 else stage1 & secondStage(i/2)
  val stage3=stage2 & thirdStage(i/4)
  stage1 //represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, y en a 6, on peut "l'envoyer" avec send
 }).toList
 val sextex:BoolVe = send(firstStage.toList)

 // val sextex:BoolVe = send(sextexInt)



 //a ce stade on a reconstruit les 6 voisins.
 //on calcule les comparaison deux a deux des couples de voisin adjacent: (east,se) (sw,w) (nw,ne)
 //d'abord le résultat des comparaisons


 show(voisins,nasI,prioRand,east,se,sw,west,nw,ne)
 show(eastlt,westlt,northlt,sextex)
 //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)
 //val (lt,eq)= Grad.slopeLt(prioRand)
//,toto.eq,toto.lt,toto.gt);
} //root classe compilable

