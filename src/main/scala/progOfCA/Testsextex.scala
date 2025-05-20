package progOfCA

import compiler.ASTB.{False, True}
import compiler.ASTBfun.{andRedop, eqUI2}
import compiler.ASTL.send
import compiler.ASTLfun.{concatR, cond, e, elt, lt2, reduce}
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolE, BoolV, BoolVe, UintV, UintVe}
import compiler.{AST, ASTLt, B, E, UI, V}
import dataStruc.BranchNamed
import sdn.Util.{addLt, addSym, addSymUI, oneThirdRandBit, randConstUintV, randUintV}
import compiler.ASTLfun._
import progOfmacros.Compute.{ concat3V}
import progOfmacros.Wrapper.{condL, ltUI2L, neqUI2L, not}
import sdn.Globals.root4naming
/** tests the lt macro, containts a bugif */
class   Testsextex() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 //we want a constant random to check that selected direction changes of time when two
 //or more vertices reach the minimum.
  val prioRand = randConstUintV(3) //rand1::rand2
  //val toto=addLt(prioRand) //pourquoi c'était la ca?
  val voisins: UintVe =addSymUI(e(prioRand)).symUI  // symUI est un boolVe qui  va contenir les voisins
 val nasI: UintV =  concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
 val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
 val (n6, n7, n8, n9, n10, n11) =(elt(6, nasI),elt(7, nasI),elt(8, nasI),elt(9, nasI),elt(10, nasI),elt(11, nasI))  //aprés on les numérote
 val(n12, n13, n14, n15, n16, n17)=(elt(12, nasI),elt(13, nasI),elt(14, nasI),elt(15, nasI),elt(16, nasI),elt(17, nasI)) // aprés on les numérote
 //val (east,se,sw)=(n0.asInstanceOf[UintV]::n1::n2, n3.asInstanceOf[UintV]::n4::n5,n6.asInstanceOf[UintV]::n7::n8) //puis on fait les paquets de 3bits
 // val (west,nw,ne)=(n9.asInstanceOf[UintV]::n10::n11, n12.asInstanceOf[UintV]::n13::n14,n15.asInstanceOf[UintV]::n16::n17) //puis on fait les paquets de 3bits
 val (east,se,sw)=(concat3V(n0, n1, n2),concat3V(n3, n4, n5),concat3V(n6, n7, n8))
 val (west,nw,ne)=(concat3V(n9,n10,n11),concat3V(n12,n13,n14),concat3V(n15,n16,n17))

 /**
  *
  * @param arg1 first unsigned int
  * @param arg2 second unsigned int
  * @param r random bit used to decide in case of equality
  * @return sharplt decide between arg1 and arg2, min is the minimum
  */
 def sharpCmp(arg1: UintV, arg2:UintV, r:BoolV): (ASTLt[V, UI], ASTLt[V, B]) ={
  val lt=ltUI2L(arg1,arg2)
  val eq=not(neqUI2L(arg1,arg2))
  val ltSharp=condL(eq, r, lt)
  val min=condL(lt,arg1,arg2)
  (min,ltSharp)
 }

 /**
  *
  * @param arg1 first unsigned int
  * @param arg2 second unsigned int
  * @return  first boolean is sharplt  which decide between arg1 and arg2, with arg1 being selected two times more often in case of equality
  * second  boolean is true if no failure encountered,
  */
 def sharpCmpOneThird(arg1: UintV, arg2:UintV): (BoolV,BoolV) ={
  val lt=ltUI2L(arg1,arg2)
  val neq: BoolV =neqUI2L(arg1,arg2) //true if arg1 and arg2 are not equal, there is 3 out of 8 chances
  val (r:BoolV,success: BoolV)= oneThirdRandBit()
  val ltSharp=condL(neq,  lt, r)
  (ltSharp,success | neq) //no failure if either oneThirdRandBit suceed, or if it was not needed anyway
 }


 val (eastmin,eastltSharp)=sharpCmp(east,se,root4naming.addRandBit().asInstanceOf[BoolV])
 val (westmin,westltSharp)=sharpCmp(sw,west,root4naming.addRandBit().asInstanceOf[BoolV])
 val (northmin,northltSharp)=sharpCmp(nw,ne,root4naming.addRandBit().asInstanceOf[BoolV])
 val (southmin,southltSharp)=sharpCmp(eastmin,westmin,root4naming.addRandBit().asInstanceOf[BoolV])
 //south encompass four direction, whereas north, only two, therefore, in case of equality southmin=norhmin,
 //the random bit should be 0 with proba two third, 1 with proba one third,
 // we use fourbits, cancel if all null, and compare to 10.

 val (allltSharp,success)=sharpCmpOneThird(southmin,northmin)

 val firstStage=Array(eastltSharp,not(eastltSharp),westltSharp,not(westltSharp),northltSharp,not(northltSharp))
 //val f:BoolV=false
 //val firstStage: Array[ASTLt[V, B]]=Array(f,f,f,f,northlt,~northlt)
 val secondStage: Array[ASTLt[V, B]] =Array(southltSharp,not(southltSharp))
 val thirdStage=Array(allltSharp,not(allltSharp))
 val sextexInt: List[ASTLt[V, B]] =(0 to 5).map((i:Int)=>{ //on traite pas encore correctement les cas d'égalité, ca va venir, un peu de patience
  val stage1=firstStage(i)  ////stage 1 a trois bits a un
  val stage2=if(i>3) stage1 else stage1 & secondStage(i/2) //stage 2 a seulement 2 bits a 1
  /** represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, possiblement zero en cas de failure.
   sur les 6, un seul est vrai. on peut "l'envoyer" avec send   */
  val stage3=stage2 & thirdStage(i/4)   //stage 3 a un seul bit a 1,
  stage3 & success
 }).toList
show(success) //neccesary to avoid cycles
  val sextex:BoolVe = send(sextexInt)



 //a ce stade on a reconstruit les 6 voisins.
 //on calcule les comparaison deux a deux des couples de voisin adjacent: (east,se) (sw,w) (nw,ne)
 //d'abord le résultat des comparaisons

//show(northmin);

 show(root4naming.rands(6),root4naming.rands(7))
 show(voisins,nasI,prioRand,east,se,sw,west,nw,ne)
 show(eastltSharp,sextex, southmin)//,eqeSe)
 //shoow(sloplt,level,twoLt,dopp,se,grad3,grad6)th
 //val (lt,eq)= Grad.slopeLt(prioRand)
//,toto.eq,toto.lt,toto.gt);
} //root classe compilable

