package compiledMacro;
 import simulator.PrShift;
 public class util{
 
public static int torusify_1_1GateCount=0;
 public static void torusify_1_1(PrShift p,int [] prandmiror,int [] resultCA){
 


for (int i = 1; i < prandmiror.length -1; i++) {
 resultCA[i]= prandmiror[i] ;
  }
  ;

 ;
  }
public static int rand_1_1GateCount=5;
 public static void rand_1_1(PrShift p,int [] prandNeigh,int [] utilrand){
 

// initialisation 
 int auxL08=0,auxL09=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,tmun00$0=0,tmun00$1=0,tmun00$2=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 auxL09= prandNeigh[i] ;neighborasInt$0= tmun00$0 ;neighborasInt$1= tmun00$1 ;neighborasInt$2= tmun00$2 ;
 neighborasInt$3= auxL09 ;neighborasInt$4=( auxL09  >>>  1 );neighborasInt$5=( auxL08  >>>  1 );tmun00$0=( auxL09  <<  1 );
 tmun00$1= auxL08 ;tmun00$2=( auxL08  <<  1 );auxL08= auxL09 ;r0= neighborasInt$1 ;
 r1= neighborasInt$4 ;r2= neighborasInt$3 ;r3= neighborasInt$5 ;r4= neighborasInt$2 ;
 r5= neighborasInt$0 ;utilrand[i-1]=((((( r5  |  r0 ) |  r4 ) ^  r2 ) ^  r1 ) ^  r3 );
  }
  p.mirror(utilrand,compiler.Locus.locusV());
p.prepareBit(utilrand)
 ;
  }}