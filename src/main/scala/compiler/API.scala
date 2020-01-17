//package compiler
// 
//import ASTB._
//
//
//trait API  {
//type Field[L <: Locus, +R <: Ring]<:{ val c :Circuit   }
////type fun[L <: Locus, R <: Ring]=Field[L,R]=>Field[L,R]
//type  Layer [L <: Locus, R <: Ring]  <: Field[L,R]  
//def displayableIn(l:Layer[_<:Locus,_<:Ring] ,f:Field[_<:Locus,_<:Ring])  
//def displayIn(l:Layer[_<:Locus,_<:Ring] ,f:Field[_<:Locus,_<:Ring]) 
//def bugIfIn(l:Layer[_<:Locus,_<:Ring] ,f:Field[_<:Locus,B]) 
//def layer[L<:Locus,R<:Ring](c:Circuit,nbit:Int )(implicit m : repr[L]):Layer[L,R]
///**called  systematically after defining next, a bit boring, but I did not find better solution */ 
//def setNext[L<:Locus,R<:Ring](l:Layer[L,R],f:Field[L,R])  
//def const[L<:Locus,R<:Ring](c:Circuit ,cte:ASTB[R])(implicit m : repr[L]) :Field[L,R] ; 
//def transfer[S1<:S,S2<:S,R<:Ring](arg : Field[T[S1,S2],R])(implicit m : repr[T[S2,S1]]):Field[T[S2,S1],R]  ;
//def sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : Field[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) :Field[T[S2,S3],R]   ;  
//def v[S1<:S, R<:Ring](arg : Field[S1 ,R])(implicit m : repr[T[S1,V]],  m2 : repr[T[V,S1]]):Field[T[S1,V],R] ; // for broadcast, we want to specify 
//def e[S1<:S, R<:Ring](arg : Field[S1,R])(implicit m : repr[T[S1,E]],  m2 : repr[T[E,S1]]):Field[T[S1,E],R]  ; // only the direction where broadcasting takes place. 
//def f[S1<:S, R<:Ring](arg : Field[S1,R])(implicit m : repr[T[S1,F]],  m2 : repr[T[F,S1]]):Field[T[S1,F],R];  //this is done using three function e,v,f. 
////def castB2R[L<:Locus,R<:I]( arg: Field[L,B] )(implicit m : repr[L]) : Field[L,R];
//def neg[L<:Locus, R<:Ring] ( arg : Field[L,R]) (implicit m : repr[L]) : Field[L,R]  ;
///**returns a signed int */
//def opp[L<:Locus] ( arg : Field[L,SI]) (implicit m : repr[L]) :  Field[L,SI]  ;
//def elt[L<:Locus, R<:I]   (i:Int , arg :  Field[L,R])    (implicit m : repr[L]) :  Field[L,B]   ;
///**Used to transform a sign which is on 2bits, before adding it to a 3 bits int. 
// * @i is the new number of bits of the extended integer */
//def extend[L<:Locus, R<:I]   (i:Int , arg :  Field[L,R])    (implicit m : repr[L]) :  Field[L,R]   ;
//def sign[L<:Locus] ( arg1 : Field[L,SI] )(implicit m : repr[L]) :Field[L,SI] ; 
//def halve[L<:Locus, R<:I] ( arg1 : Field[L,R] )(implicit m : repr[L]) :Field[L,R] ; 
//def orScanRight[L<:Locus, R<:I] ( arg1 : Field[L,R] )(implicit m : repr[L]) :Field[L,R] ; 
//def gt[L<:Locus] ( arg1 : Field[L,SI] )(implicit m : repr[L]) :Field[L,B] ; 
////	def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  ; //faild attempt to currify
//def orL[L<:Locus, R<:Ring]( arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R];
//def andL[L<:Locus, R<:Ring]( arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R];
//def xorL[L<:Locus, R<:Ring]( arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R];
//def andLB2R [L<:Locus,R<:I]( arg1 : Field[L,B],arg2 : Field[L,R])(implicit m : repr[L]):Field[L,R] 
//def concat[L<:Locus,R<:I]( arg1 : Seq[AST[L,B]])(implicit m : repr[L]) :Field[L,R] 
//def addL[L<:Locus,R<:I] ( arg1 : Field[L,R], arg2 : Field[L,R])(implicit m : repr[L]) : Field[L,R] ;
//def orR[S1<:S,S2<:S,R<:Ring] (arg : Field[T[S1,S2],R])(implicit m : repr[S1]): Field[S1,R] ;   
//def xorR[S1<:S,S2<:S,R<:Ring] (arg : Field[T[S1,S2],R])(implicit m : repr[S1]): Field[S1,R] ;   
//def minR[S1<:S,S2<:S,R<:I] (arg :  Field[T[S1,S2],R])(implicit m : repr[S1]) : Field[S1,R] ; 
//	/** signL is defined only for signed Int */
// def xorR2[S1<:S,S2<:S,S2new<:S,R<:Ring] (arg : Field[T[S1,S2],R])(implicit m : repr[T[S1,S2new]]):Field[T[S1,S2new],R]  ;   
// def delayed[L<:Locus,R<:Ring](arg: =>Field[L,R],c:Circuit, nbit:Int)(implicit m:repr[L]):Field[L,R];
//	
//	
//	/**Wrapper for layer, used whenever API user wants to declare a layer. */
//  abstract class LayerUsr[L <: Locus, R <: Ring](c:Circuit,nbit:Int)(implicit m : repr[L]) extends Named{
//    val  pred=layer[L,R](c,nbit );    val next:Field[L,R]  
//    def displayable(f:Field[_<:Locus,_<:Ring]){displayableIn(pred,f)}
//def display(f:Field[_<:Locus,_<:Ring]) { displayIn(pred,f)}
//def bugIf(f:Field[_<:Locus,B]) {bugIfIn(pred,f)}
//    
//  }
//}
//
//	/**Wrapper for layer, used whenever API user wants to declare a layer. */
//  abstract class LayerUsr[L <: Locus, R <: Ring](c:Circuit,nbit:Int)(implicit m : repr[L]) extends APIstdlib with Named  {
//    val  pred=layer[L,R](c,nbit );    val next:Field[L,R]  
//    def displayable(f:Field[_<:Locus,_<:Ring]){displayableIn(pred,f)}
//def display(f:Field[_<:Locus,_<:Ring]) { displayIn(pred,f)}
//def bugIf(f:Field[_<:Locus,B]) {bugIfIn(pred,f)}
//    
//  }
//
///** Also contains the possible fields type, which combine a locus and a ring type.*/
//trait APIstdlib extends API  { 
//  type IntV = Field[V,SI]; type IntE = Field[E,SI]; type IntF = Field[F,SI];
//	type IntvE = Field[T[E,V],SI]; type InteV = Field[T[V,E],SI];
//	type IntvF = Field[T[F,V],SI]; type IntfV = Field[T[V,F],SI];
//	type IntfE = Field[T[E,F],SI]; type InteF = Field[T[F,E],SI];
//  type UintV = Field[V,UI]; type UintE = Field[E,UI]; type UintF = Field[F,UI];
//	type UintvE = Field[T[E,V],UI]; type UinteV = Field[T[V,E],UI];
//	type UintvF = Field[T[F,V],UI]; type UintfV = Field[T[V,F],UI];
//	type UintfE = Field[T[E,F],UI]; type UinteF = Field[T[F,E],UI];  
//	type BoolV = Field[V,B]; type BoolE = Field[E,B]; type BoolF = Field[F,B];
//	type BooleV = Field[T[V,E],B]; type BoolvE = Field[T[E,V],B];
//	type BoolvF = Field[T[F,V],B]; type BoolfV = Field[T[V,F],B];
//	type BoolfE = Field[T[E,F],B]; type BooleF = Field[T[F,E],B];
//  def cond[L<:Locus,R<:I] (b:Field[L,B],  arg1 : Field[L,R] , arg2 : Field[L,R])(implicit m : repr[L])= orL(andLB2R[L,R](b,arg1),andLB2R(neg(b),arg2))
//  	/**  defined only for signed Int */
//  def minusL[L<:Locus] ( arg1 :  Field[L,SI], arg2 : Field[L,SI])(implicit m : repr[L]) = addL( arg1,opp(arg2)) ;
//  
//  def mstb[L<:Locus,R<:I] (arg1:Field[L,R])(implicit m : repr[L]): Field[L,R] = { val y:Field[L,R]= orScanRight[L,R](arg1); 
//    xorL(y,halve(y)) }  
//}
// 
//
///**suffix L,R,R2 for locus, reduction, reduction to two */
//trait LanguageImpl extends API { 
//  type Field[L <: Locus, +R <: Ring] = AST[L,R]
//  type Layer[L <: Locus, R <: Ring] = LayerAST[L,R]
// def displayableIn(l:LayerAST[_<:Locus,_<:Ring] ,f:AST[_<:Locus,_<:Ring]) = l.displayable(f)
//def displayIn(l:LayerAST[_<:Locus,_<:Ring] ,f:AST[_<:Locus,_<:Ring]) = l.display(f)
//def bugIfIn(l:LayerAST[_<:Locus,_<:Ring] ,f:AST[_<:Locus,B]) = l.bugIf(f)
// def layer[L<:Locus,R<:Ring](c:Circuit,nbit:Int )(implicit m : repr[L])=  LayerAST(c,nbit)
////def setPred[L<:Locus,R<:Ring](l:LayerAST[L,R],f:AST[L,R]){l.setPred(f)}
//  def setNext[L<:Locus,R<:Ring](l:LayerAST[L,R],f:AST[L,R]){l.setNext(f)}
//  def const[L<:Locus,R<:Ring](c:Circuit ,cte:ASTB[R])(implicit m : repr[L])     = Const(c,cte)(m) ;
// // def layer[L<:Locus,R<:Ring]( c:Circuit )(implicit m : repr[L])   =  Layer (c)(m)
// def transfer[S1<:S,S2<:S,R<:Ring](arg : Field[T[S1,S2],R])(implicit m : repr[T[S2,S1]]) = Transfer(arg)(m)  ;
// def sym[S1<:S,S2<:S,S3<:S, R<:Ring](arg : Field[T[S2,S1],R])(implicit m : repr[T[S2,S3]], t : CentralSym[S1,S2,S3]) = Sym(arg)(m,t)   ;
// def v[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,V]],  m2 : repr[T[V,S1]])=Broadcast[S1,V,R](arg); // for broadcast, we want to specify only the direction where broadcasting takes place.
//	def e[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,E]],  m2 : repr[T[E,S1]])=Broadcast[S1,E,R](arg); // this is done using three function e,v,f. 
//	def f[S1<:S, R<:Ring](arg : AST[S1,R])(implicit m : repr[T[S1,F]],  m2 : repr[T[F,S1]])=Broadcast[S1,F,R](arg);
//	//def castB2R[L<:Locus,R<:I]( arg: AST[L,B] )(implicit m : repr[L])  = Unop[L,B,R] (castB2RN[R],arg );
//	def neg[L<:Locus, R<:Ring] ( arg : AST[L,R]) (implicit m : repr[L]) = Unop[L,R,R](negN[R],arg)   ;
//	def opp[L<:Locus ] ( arg : AST[L,SI]) (implicit m : repr[L]) = Unop[L,SI,SI](oppN,arg)   ;
//	def elt[L<:Locus, R<:I]   (i:Int , arg : AST[L,R]  ) (implicit m : repr[L]) = Unop[L,R,B](eltN[R](i),arg)   ;
//	def extend[L<:Locus, R<:I]   (i:Int , arg : AST[L,R]  ) (implicit m : repr[L]) = Unop[L,R,R](extendN[R](i),arg)   ;
//	def sign[L<:Locus] ( arg1 : AST[L,SI] )(implicit m : repr[L]) = Unop[L,SI,SI ](signN,arg1 );
//	def halve[L<:Locus, R<:I] ( arg1 : Field[L,R] )(implicit m : repr[L])  = Unop[L,R,R ](halveN,arg1 )
//def orScanRight[L<:Locus, R<:I] ( arg1 : Field[L,R] )(implicit m : repr[L])    = Unop[L,R,R ](orScanRightN,arg1 )
//
//def gt[L<:Locus] ( arg1 : AST[L,SI] )(implicit m : repr[L]) = Unop[L,SI,B ](gtN,arg1 );
//	//def binop [L<:Locus, R<:Ring] (implicit m : repr[L]) = Binop[L,R,R,R] _  ;
//	def orL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R])(implicit m : repr[L]) = Binop[L,R,R,R](orN,arg1,arg2 );
//	def andL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R]) (implicit m : repr[L]) = Binop[L,R,R,R](andN,arg1,arg2 );
//	def xorL[L<:Locus, R<:Ring]( arg1 : AST[L,R] , arg2 : AST[L,R]) (implicit m : repr[L]) = Binop[L,R,R,R](xorN,arg1,arg2 );
//	/** We avoid casting boolean to integer, instead we define operation taking an int and a  bool, and computing a new int, by mapping the and operation*/
//	def andLB2R [L<:Locus,R<:I]( arg1 : Field[L,B],arg2 : Field[L,R])(implicit m : repr[L]) = Binop[L,B,R,R]( andLB2RN,arg1 ,arg2);
//def concat[L<:Locus,R<:I]( arg1 : Seq[AST[L,B]])(implicit m : repr[L])=  Multop[L,B,R](concatN, arg1 );
//	def addL[L<:Locus,R<:I] ( arg1 : AST[L,R], arg2 : AST[L,R])(implicit m : repr[L]):AST[L,R] = Binop[L,R,R,R](addN,arg1,arg2 ) ;
//	def orR[S1<:S,S2<:S, R<:Ring] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((orN[R],False[R](arg.nbit)),arg );   
//	def xorR[S1<:S,S2<:S, R<:Ring] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((xorN[R],False[R](arg.nbit)),arg );   
//  def xorR2[S1<:S,S2<:S,S2new<:S, R<:Ring] (arg : AST[T[S1,S2],R])(implicit m : repr[T[S1,S2new]]) = Redop2[S1,S2,S2new,R] ((xorN[R],False[R](arg.nbit)),arg );   
//	def minR[S1<:S,S2<:S,R<:I] (arg : AST[T[S1,S2],R])(implicit m : repr[S1]) = Redop[S1,S2,R] ((minN[R],ConstInt[R](0,1)),arg );
//	/** Delete uses a trick found on the net, to have a call by name, together with a case class necessary to make the match*/
//	def delayed[L<:Locus,R<:Ring](_arg: => AST[L,R],c:Circuit,nbit:Int )(implicit m : repr[L]): AST[L,R] = {
//  lazy val delayed = _arg  ;  Delayed(() => delayed,c,nbit) }
//}
// 
//
// 
