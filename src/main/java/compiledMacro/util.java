package compiledMacro;
 import simulator.PrShift;
 public class util{
 
public static int rand_1_1GateCount=5;
 public static void rand_1_1(PrShift p,int [] prandNeigh,int [] utilrand){
 
// initialisation 
 int auxL01=0,auxL02=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,tmun00=0,tmun01=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL02  <<  1 );auxL02= prandNeigh[i] ;neighborasInt$2= auxL02 ;neighborasInt$3=( auxL02  >>>  1 );
 neighborasInt$4=( auxL01  >>>  1 );neighborasInt$5= tmun00 ;tmun00= auxL01 ;neighborasInt$0= tmun01 ;
 tmun01=( auxL01  <<  1 );auxL01= auxL02 ;r0= neighborasInt$1 ;r1= neighborasInt$5 ;
 r2= neighborasInt$0 ;r3= neighborasInt$4 ;r4= neighborasInt$2 ;r5= neighborasInt$3 ;
 utilrand[i-1]=((((( r2  |  r0 ) |  r4 ) ^  r5 ) ^  r3 ) ^  r1 );
   } }
public static int randN12_1_1GateCount=35;
 public static void randN12_1_1(PrShift p,int [] prandNeigh,int [][] utilrandN12){
 int[] utilrandN12$e=utilrandN12[0],utilrandN12$se=utilrandN12[1],utilrandN12$sw=utilrandN12[2],utilrandN12$w=utilrandN12[3],utilrandN12$nw=utilrandN12[4],utilrandN12$ne=utilrandN12[5];
p.mirror(prandNeigh,compiler.Locus.locusV());
p.prepareBit(prandNeigh)
 ;
// initialisation 
 int auxL00$0=0,auxL00$1=0,auxL00$2=0,auxL00$3=0,auxL00$4=0,auxL00$5=0,auxL00$6=0,auxL01$0=0,auxL01$1=0,auxL01$2=0,auxL01$3=0,auxL01$4=0,auxL01$5=0,auxL02$0=0,auxL02$1=0,auxL02$2=0,auxL03=0,auxL04=0,auxL05=0,auxL06=0,auxL07=0,auxL08=0,auxL09=0,auxL19=0,auxL20=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,r6=0,tmun03=0,tmun04=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL20  <<  1 );auxL20= prandNeigh[i] ;neighborasInt$2= auxL20 ;neighborasInt$3=( auxL20  >>>  1 );
 neighborasInt$4=( auxL19  >>>  1 );neighborasInt$5= tmun03 ;tmun03= auxL19 ;neighborasInt$0= tmun04 ;
 tmun04=( auxL19  <<  1 );auxL19= auxL20 ;r0= neighborasInt$4 ;auxL09= r0 ;
 r0= neighborasInt$3 ;auxL03= r0 ;r0= neighborasInt$2 ;auxL04= r0 ;
 r0= neighborasInt$0 ;auxL08= r0 ;auxL07=~ auxL08 ;r0= neighborasInt$1 ;
 auxL06= r0 ;auxL05=~ auxL06 ;r0=( auxL07  &  auxL05 );auxL02$0=(( r0  & ( auxL04  &  auxL03 )) | ( auxL08  &  auxL06 ));
 auxL02$1=(( r0  & (~ auxL04  &  auxL03 )) | ( auxL07  &  auxL06 ));auxL02$2=(( r0  & ( auxL04  & ~ auxL03 )) | ( auxL08  &  auxL05 ));r0=~ auxL09 ;auxL01$0=( auxL09  &  auxL02$0 );
 auxL01$1=( auxL09  &  auxL02$1 );auxL01$2=( auxL09  &  auxL02$2 );auxL01$3=( r0  &  auxL02$0 );auxL01$4=( r0  &  auxL02$1 );
 auxL01$5=( r0  &  auxL02$2 );r0= neighborasInt$5 ;r2=(r4= auxL01$5 );r6=(r4= auxL01$4 );
 r5=(r4= auxL01$3 );r3=(r4= auxL01$2 );r1= auxL01$1 ;r4= auxL01$0 ;
 auxL00$0=( auxL01$0  | ( r0  &  r1 ));auxL00$1=( auxL01$1  | ( r0  &  r3 ));auxL00$2=( auxL01$2  | ( r0  &  r5 ));auxL00$3=( auxL01$3  | ( r0  &  r6 ));
 auxL00$4=( auxL01$4  | ( r0  &  r2 ));auxL00$5= auxL01$5 ;auxL00$6=( r0  &  r4 );r0= auxL00$5 ;
 utilrandN12$e[i-1]= r0 ;r0= auxL00$4 ;utilrandN12$se[i-1]= r0 ;r0= auxL00$3 ;
 utilrandN12$sw[i-1]= r0 ;r0= auxL00$2 ;utilrandN12$w[i-1]= r0 ;r0= auxL00$1 ;
 utilrandN12$nw[i-1]= r0 ;r0= auxL00$0 ;utilrandN12$ne[i-1]= r0 ;
   } }}