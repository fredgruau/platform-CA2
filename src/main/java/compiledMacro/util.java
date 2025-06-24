package compiledMacro;
 import simulator.PrShift;
 public class util{
 
public static int torusify_1_1GateCount=0;
 public static void torusify_1_1(PrShift p,int [] prandmiror,int [] resultCA){
 


for (int i = 1; i < prandmiror.length -1; i++) {
 resultCA[i]= prandmiror[i] ;
  }
p.torusify(resultCA);
/*  p.mirror(resultCA);
p.prepareBit(resultCA)*/
 ;
  }
public static int rand_1_1GateCount=5;
 public static void rand_1_1(PrShift p,int [] prandNeigh,int [] utilrand){
 

// initialisation 
 int auxL53=0,auxL54=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,tmun23=0,tmun24=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL54  <<  1 );auxL54= prandNeigh[i] ;neighborasInt$2= auxL54 ;neighborasInt$3=( auxL54  >>>  1 );
 neighborasInt$4=( auxL53  >>>  1 );neighborasInt$5= tmun23 ;tmun23= auxL53 ;neighborasInt$0= tmun24 ;
 tmun24=( auxL53  <<  1 );auxL53= auxL54 ;r0= neighborasInt$4 ;r1= neighborasInt$5 ;
 r2= neighborasInt$2 ;r3= neighborasInt$1 ;r4= neighborasInt$0 ;r5= neighborasInt$3 ;
 utilrand[i-1]=((((( r4  &  r3 ) |  r2 ) ^  r5 ) ^  r0 ) ^  r1 );
  }
  p.mirror(utilrand);
p.prepareBit(utilrand)
 ;
  }}