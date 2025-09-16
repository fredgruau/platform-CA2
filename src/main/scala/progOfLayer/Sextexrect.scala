package progOfLayer

import compiler.ASTL.send
import compiler.ASTLfun._
import compiler.ASTLt.ConstLayer
import compiler.SpatialType.{BoolV, BoolVe, SintV, UintV, UintVe, UintVx}
import compiler.{ASTLt, B, UI, V}
import dataStruc.BranchNamed
import progOfLayer.Sextexrect.{chooseMaxOf, sharpCmpNoMin, weakCmpProdZero, weakCmpProdtwo}

import progOfmacros.Compute.concat3V
import progOfmacros.Wrapper.{condL, ltUI2L, neqUI2L, not}
import sdn.Globals.root4naming
import sdn.Util.{addSymUI, oneThirdRandBit, randConstUintV}

/** tests the lt macro, containts a bugif */

class   Sextexrect() extends ConstLayer[V, B](1, "global")  with BranchNamed{
 //we want a constant random to check that selected direction changes of time when two
 //or more vertices reach the minimum.
  val prioRand = randConstUintV(3) //rand1::rand2
  val choose=chooseMaxOf(prioRand)
 show(prioRand,choose)

 /*
  //val toto=addLt(prioRand) //pourquoi c'était la ca?
  val voisins: UintVe =addSymUI(e(prioRand)).symUI  // symUI est un boolVe qui  va contenir les voisins
 val nasI: UintV =  concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
 val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
 val (n6, n7, n8, n9, n10, n11) =(elt(6, nasI),elt(7, nasI),elt(8, nasI),elt(9, nasI),elt(10, nasI),elt(11, nasI))  //aprés on les numérote
 val(n12, n13, n14, n15, n16, n17)=(elt(12, nasI),elt(13, nasI),elt(14, nasI),elt(15, nasI),elt(16, nasI),elt(17, nasI)) // aprés on les numérote
  val (east,se,sw)=(concat3V(n0, n1, n2),concat3V(n3, n4, n5),concat3V(n6, n7, n8))
 val (west,nw,ne)=(concat3V(n9,n10,n11),concat3V(n12,n13,n14),concat3V(n15,n16,n17))
 /** Two here means that if arg1 = arg2 we expand in both directions, going from a singleton to a tripleton */
 val (northmin,nwnw,nene)=weakCmpProdtwo(nw,ne)
 val (southmin,swsw,sese)=weakCmpProdtwo(sw,se)
 val (horizMin,heast,hwest)=weakCmpProdZero(east,west)
 val (vertmin,nn,ss)=weakCmpProdZero(northmin,southmin)
 val  vertltsharp=sharpCmpNoMin(vertmin,horizMin,root4naming.addRandBit().asInstanceOf[BoolV])
 val firstStage=Array(heast,sese,swsw,hwest,nwnw,nene) //peut y avoir plusieurs bit a 1. faudra refaire des "ET" logique
 val south = ss & vertltsharp
 val north = nn & vertltsharp
 val secondStage: Array[ASTLt[V, B]] =Array(~vertltsharp,south,south, ~vertltsharp,north,north)
 /** a seulement un bits a 1 sauf pour etendre vers le haut ou  vers le bas, ou la ca marche sur deux bits.*/
 val sextexInt: List[ASTLt[V, B]] =(0 to 5).map((i:Int)=>{ firstStage(i)  & secondStage(i)}).toList
 /** represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, possiblement zero en cas de failure.
   sur les 6, un seul est vrai ou deux adjacents. on peut "l'envoyer" avec send   */
    //val success=sextexInt.reduce(_|_);show(success) //monitor if there is actual move.
 val sextex:BoolVe = send(sextexInt)
 show(voisins,nasI,prioRand,east,se,sw,west,nw,ne)
 show(sextex, southmin)//,eqeSe)*/
} //root classe compilable
object Sextexrect {
 def weakCmpProdtwo(arg1: UintV, arg2: UintV): (ASTLt[V, UI], ASTLt[V, B], ASTLt[V, B]) = {
  val lt = ltUI2L(arg1, arg2)
  val eq = not(neqUI2L(arg1, arg2))
  val le = lt | eq
  val ge = ~lt | eq
  val max = condL(ge, arg1, arg2)
  (max, ge, le)
 }

 /** "Zero" here means that if arg1 = arg2 we do not expand at all */
 def weakCmpProdZero(arg1: UintV, arg2: UintV): (ASTLt[V, UI], ASTLt[V, B], ASTLt[V, B]) = {
  val lt = ltUI2L(arg1, arg2)
  val eq = not(neqUI2L(arg1, arg2))
  val gt = ~lt & ~eq
  val max = condL(gt, arg1, arg2)
  (max, gt, lt)
 }

 /** here we need only the result, we are not interested in getting the minimum, using a random bit we manage to allways split. */
 private def sharpCmpNoMin(arg1: UintV, arg2: UintV, r: BoolV): ASTLt[V, B] = {
  val lt = ltUI2L(arg1, arg2)
  val eq = not(neqUI2L(arg1, arg2))
  val ltSharp = condL(eq, r, lt)
  ltSharp
 }

 /** utilise un bit rand en plus, on veut pas. */
 def chooseMinOfRand(prio: UintV): BoolVe = {
  val voisins: UintVe = addSymUI(e(prio)).symUI // symUI est un boolVe qui  va contenir les voisins
  val nasI: UintV = concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
  val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
  val (n6, n7, n8, n9, n10, n11) = (elt(6, nasI), elt(7, nasI), elt(8, nasI), elt(9, nasI), elt(10, nasI), elt(11, nasI)) //aprés on les numérote
  val (n12, n13, n14, n15, n16, n17) = (elt(12, nasI), elt(13, nasI), elt(14, nasI), elt(15, nasI), elt(16, nasI), elt(17, nasI)) // aprés on les numérote
  val (east, se, sw) = (concat3V(n0, n1, n2), concat3V(n3, n4, n5), concat3V(n6, n7, n8))
  val (west, nw, ne) = (concat3V(n9, n10, n11), concat3V(n12, n13, n14), concat3V(n15, n16, n17))
  /** Two here means that if arg1 = arg2 we expand in both directions, going from a singleton to a tripleton */
  val (northmin, nwnw, nene) = weakCmpProdtwo(nw, ne)
  val (southmin, swsw, sese) = weakCmpProdtwo(sw, se)
  val (horizMin, heast, hwest) = weakCmpProdZero(east, west)
  val (vertmin, nn, ss) = weakCmpProdZero(northmin, southmin)
  val vertltsharp: BoolV = sharpCmpNoMin(vertmin, horizMin, root4naming.addRandBit().asInstanceOf[BoolV])
  val firstStage = Array(heast, sese, swsw, hwest, nwnw, nene) //peut y avoir plusieurs bit a 1. faudra refaire des "ET" logique
  val south = ss & vertltsharp
  val north = nn & vertltsharp
  val secondStage: Array[ASTLt[V, B]] = Array(~vertltsharp, south, south, ~vertltsharp, north, north)
  /** a seulement un bits a 1 sauf pour etendre vers le haut ou  vers le bas, ou la ca marche sur deux bits. */
  val sextexInt: List[ASTLt[V, B]] = (0 to 5).map((i: Int) => {
   firstStage(i) & secondStage(i)
  }).toList
  /** represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, possiblement zero en cas de failure.
   * sur les 6, un seul est vrai ou deux adjacents. on peut "l'envoyer" avec send */
  //val success=sextexInt.reduce(_|_);show(success) //monitor if there is actual move.
  val sextex: BoolVe = send(sextexInt)
  sextex
 }

 def chooseMaxOf(prio: UintV): BoolVe={
 val voisins: UintVe = addSymUI(e(prio)).symUI // symUI est un boolVe qui  va contenir les voisins
 val nasI: UintV = concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
 val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
 val (n6, n7, n8, n9, n10, n11) = (elt(6, nasI), elt(7, nasI), elt(8, nasI), elt(9, nasI), elt(10, nasI), elt(11, nasI)) //aprés on les numérote
 val (n12, n13, n14, n15, n16, n17) = (elt(12, nasI), elt(13, nasI), elt(14, nasI), elt(15, nasI), elt(16, nasI), elt(17, nasI)) // aprés on les numérote
 val (east, se, sw) = (concat3V(n0, n1, n2), concat3V(n3, n4, n5), concat3V(n6, n7, n8))
 val west = concat3V(n9, n10, n11)
 val nwest = concat3V(n12, n13, n14)
 val neast = concat3V(n15, n16, n17)
 /** Two here means that if arg1 = arg2 we expand in both directions, going from a singleton to a tripleton */
 val (northmin, nwnw, nene) = weakCmpProdtwo(nwest, neast)
 //  shoow(northmin,nwnw,nene)
 val (southmin, swsw, sese) = weakCmpProdtwo(sw, se)
 val (horizMin, heast, hwest) = weakCmpProdZero(east, west)
 val (vertmin, nn, ss) = weakCmpProdZero(northmin, southmin)
 //shoow(nn,ss)
 val (toto, vert, horiz) = weakCmpProdZero(vertmin, horizMin)

 //shoow(vert,horiz)
 val firstStage = Array(heast, sese, swsw, hwest, nwnw, nene) //peut y avoir plusieurs bit a 1. faudra refaire des "ET" logique
 val south = ss & vert
 val north = nn & vert
 val secondStage: Array[ASTLt[V, B]] = Array(horiz, south, south, horiz, north, north)
 /** a seulement un bits a 1 sauf pour etendre vers le haut ou  vers le bas, ou la ca marche sur deux bits. */
 val sextexInt: List[ASTLt[V, B]] = (0 to 5).map((i: Int) => {
  firstStage(i) & secondStage(i)
 }).toList
 /** represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, possiblement zero en cas de failure.
  * sur les 6, un seul est vrai ou deux adjacents. on peut "l'envoyer" avec send */
 //val success=sextexInt.reduce(_|_);show(success) //monitor if there is actual move.
 val sextex: BoolVe = send(sextexInt)
 sextex
}
 def chooseMinOfOld(prio:UintV):BoolVe={
  val voisins: UintVe =addSymUI(e(prio)).symUI  // symUI est un boolVe qui  va contenir les voisins
  val nasI: UintV =  concatR(voisins) //on récupére 18 bits a la suite pour 6 voisins, chacun 3 bits,
  val (n0, n1, n2, n3, n4, n5) = (elt(0, nasI), elt(1, nasI), elt(2, nasI), elt(3, nasI), elt(4, nasI), elt(5, nasI)) // aprés on les numérote
  val (n6, n7, n8, n9, n10, n11) =(elt(6, nasI),elt(7, nasI),elt(8, nasI),elt(9, nasI),elt(10, nasI),elt(11, nasI))  //aprés on les numérote
  val(n12, n13, n14, n15, n16, n17)=(elt(12, nasI),elt(13, nasI),elt(14, nasI),elt(15, nasI),elt(16, nasI),elt(17, nasI)) // aprés on les numérote
  val (east,se,sw)=(concat3V(n0, n1, n2),concat3V(n3, n4, n5),concat3V(n6, n7, n8))
  val (west,nw,ne)=(concat3V(n9,n10,n11),concat3V(n12,n13,n14),concat3V(n15,n16,n17))
  /** Two here means that if arg1 = arg2 we expand in both directions, going from a singleton to a tripleton */
  val (northmin,nwnw,nene)=weakCmpProdtwo(nw,ne)
  val (southmin,swsw,sese)=weakCmpProdtwo(sw,se)
  val (horizMin,heast,hwest)=weakCmpProdZero(east,west)
  val (vertmin,nn,ss)=weakCmpProdZero(northmin,southmin)
  val  (toto,vert,horiz) =weakCmpProdZero(vertmin,horizMin)
  val firstStage=Array(heast,sese,swsw,hwest,nwnw,nene) //peut y avoir plusieurs bit a 1. faudra refaire des "ET" logique
  val south = ss & vert
  val north = nn & vert
  val secondStage: Array[ASTLt[V, B]] =Array(horiz,south,south, horiz,north,north)
  /** a seulement un bits a 1 sauf pour etendre vers le haut ou  vers le bas, ou la ca marche sur deux bits.*/
  val sextexInt: List[ASTLt[V, B]] =(0 to 5).map((i:Int)=>{ firstStage(i)  & secondStage(i)}).toList
  /** represente un uint sur 6 bit qui est le code unaire d'un nombre compris entre 0 et 5, possiblement zero en cas de failure.
   sur les 6, un seul est vrai ou deux adjacents. on peut "l'envoyer" avec send   */
  //val success=sextexInt.reduce(_|_);show(success) //monitor if there is actual move.
  val sextex:BoolVe = send(sextexInt)
  sextex
 }
}
