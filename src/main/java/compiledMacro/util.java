package compiledMacro;
 import simulator.PrShift;
 public class util{
 
public static int randN12_1_1GateCount=35;
 public static void randN12_1_1(PrShift p,int [] prandNeigh,int [][] utilrandN12){
 int[] utilrandN12$e=utilrandN12[0],utilrandN12$se=utilrandN12[1],utilrandN12$sw=utilrandN12[2],utilrandN12$w=utilrandN12[3],utilrandN12$nw=utilrandN12[4],utilrandN12$ne=utilrandN12[5];

// initialisation 
 int auxL01$0=0,auxL01$1=0,auxL01$2=0,auxL01$3=0,auxL01$4=0,auxL01$5=0,auxL01$6=0,auxL02$0=0,auxL02$1=0,auxL02$2=0,auxL02$3=0,auxL02$4=0,auxL02$5=0,auxL03$0=0,auxL03$1=0,auxL03$2=0,auxL04=0,auxL05=0,auxL06=0,auxL07=0,auxL08=0,auxL09=0,auxL10=0,auxL26=0,auxL27=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,r6=0,r7=0,tmun09=0,tmun10=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL27  <<  1 );auxL27= prandNeigh[i] ;neighborasInt$2= auxL27 ;neighborasInt$3=( auxL27  >>>  1 );
 neighborasInt$4=( auxL26  >>>  1 );neighborasInt$5= tmun09 ;tmun09= auxL26 ;neighborasInt$0= tmun10 ;
 tmun10=( auxL26  <<  1 );auxL26= auxL27 ;r0= neighborasInt$3 ;auxL04= r0 ;
 r0= neighborasInt$2 ;auxL05= r0 ;r0= neighborasInt$1 ;auxL07= r0 ;
 auxL06=~ auxL07 ;r0= neighborasInt$0 ;auxL09= r0 ;auxL08=~ auxL09 ;
 r0=( auxL08  &  auxL06 );auxL03$0=(( r0  & ( auxL05  &  auxL04 )) | ( auxL09  &  auxL07 ));auxL03$1=(( r0  & (~ auxL05  &  auxL04 )) | ( auxL08  &  auxL07 ));auxL03$2=(( r0  & ( auxL05  & ~ auxL04 )) | ( auxL09  &  auxL06 ));
 r0= neighborasInt$4 ;auxL10= r0 ;r0=~ auxL10 ;auxL02$0=( auxL10  &  auxL03$0 );
 auxL02$1=( auxL10  &  auxL03$1 );auxL02$2=( auxL10  &  auxL03$2 );auxL02$3=( r0  &  auxL03$0 );auxL02$4=( r0  &  auxL03$1 );
 auxL02$5=( r0  &  auxL03$2 );r0= neighborasInt$5 ;r1= auxL02$0 ;r7=(r4= auxL02$5 );
 r6=(r4= auxL02$4 );r5=(r4= auxL02$3 );r3=(r4= auxL02$2 );r2= auxL02$1 ;
 auxL01$0=( auxL02$0  | ( r0  &  r2 ));auxL01$1=( auxL02$1  | ( r0  &  r3 ));auxL01$2=( auxL02$2  | ( r0  &  r5 ));auxL01$3=( auxL02$3  | ( r0  &  r6 ));
 auxL01$4=( auxL02$4  | ( r0  &  r7 ));auxL01$5= auxL02$5 ;auxL01$6=( r0  &  r1 );r0= auxL01$0 ;
 utilrandN12$e[i-1]= r0 ;r0= auxL01$1 ;utilrandN12$se[i-1]= r0 ;r0= auxL01$2 ;
 utilrandN12$sw[i-1]= r0 ;r0= auxL01$3 ;utilrandN12$w[i-1]= r0 ;r0= auxL01$4 ;
 utilrandN12$nw[i-1]= r0 ;r0= auxL01$5 ;utilrandN12$ne[i-1]= r0 ;
  }
  ;
 ;
  }
public static int rand_1_1GateCount=5;
 public static void rand_1_1(PrShift p,int [] prandNeigh,int [] utilrand){
 

// initialisation 
 int auxL11=0,auxL12=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,tmun00=0,tmun01=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL12  <<  1 );auxL12= prandNeigh[i] ;neighborasInt$2= auxL12 ;neighborasInt$3=( auxL12  >>>  1 );
 neighborasInt$4=( auxL11  >>>  1 );neighborasInt$5= tmun00 ;tmun00= auxL11 ;neighborasInt$0= tmun01 ;
 tmun01=( auxL11  <<  1 );auxL11= auxL12 ;r0= neighborasInt$1 ;r1= neighborasInt$5 ;
 r2= neighborasInt$0 ;r3= neighborasInt$4 ;r4= neighborasInt$2 ;r5= neighborasInt$3 ;
 utilrand[i-1]=((((( r2  |  r0 ) |  r4 ) ^  r5 ) ^  r3 ) ^  r1 );
  }
  p.border(utilrand);
 ;
  }}