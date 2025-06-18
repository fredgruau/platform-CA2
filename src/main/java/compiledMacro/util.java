package compiledMacro;
 import simulator.PrShift;
 public class util{
 
public static int torusify_1_1GateCount=0;
 public static void torusify_1_1(PrShift p,int [] prandmiror,int [] resultCA){
 


for (int i = 1; i < prandmiror.length -1; i++) {
 resultCA[i]= prandmiror[i] ;
  }
  p.border(resultCA);
 ;
  }
public static int rand_1_1GateCount=5;
 public static void rand_1_1(PrShift p,int [] prandNeigh,int [] utilrand){
 

// initialisation 
 int auxL00=0,auxL01=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,tmun00=0,tmun01=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL01  <<  1 );auxL01= prandNeigh[i] ;neighborasInt$2= auxL01 ;neighborasInt$3=( auxL01  >>>  1 );
 neighborasInt$4=( auxL00  >>>  1 );neighborasInt$5= tmun00 ;tmun00= auxL00 ;neighborasInt$0= tmun01 ;
 tmun01=( auxL00  <<  1 );auxL00= auxL01 ;r0= neighborasInt$1 ;r1= neighborasInt$5 ;
 r2= neighborasInt$4 ;r3= neighborasInt$2 ;r4= neighborasInt$3 ;r5= neighborasInt$0 ;
 utilrand[i-1]=((((( r5  &  r0 ) |  r3 ) ^  r4 ) ^  r2 ) ^  r1 );
  }
  p.border(utilrand);
 ;
  }
public static int randN12_1_1GateCount=35;
 public static void randN12_1_1(PrShift p,int [] prandNeigh,int [][] utilrandN12){
 int[] utilrandN12$e=utilrandN12[0],utilrandN12$se=utilrandN12[1],utilrandN12$sw=utilrandN12[2],utilrandN12$w=utilrandN12[3],utilrandN12$nw=utilrandN12[4],utilrandN12$ne=utilrandN12[5];

// initialisation 
 int auxL01$0=0,auxL01$1=0,auxL01$2=0,auxL01$3=0,auxL01$4=0,auxL01$5=0,auxL01$6=0,auxL02$0=0,auxL02$1=0,auxL02$2=0,auxL02$3=0,auxL02$4=0,auxL02$5=0,auxL03$0=0,auxL03$1=0,auxL03$2=0,auxL04=0,auxL05=0,auxL06=0,auxL07=0,auxL08=0,auxL09=0,auxL10=0,auxL24=0,auxL25=0,neighborasInt$0=0,neighborasInt$1=0,neighborasInt$2=0,neighborasInt$3=0,neighborasInt$4=0,neighborasInt$5=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0,r6=0,tmun07=0,tmun08=0;
for (int i = 1; i < prandNeigh.length -1; i++) {
 neighborasInt$1=( auxL25  <<  1 );auxL25= prandNeigh[i] ;neighborasInt$2= auxL25 ;neighborasInt$3=( auxL25  >>>  1 );
 neighborasInt$4=( auxL24  >>>  1 );neighborasInt$5= tmun07 ;tmun07= auxL24 ;neighborasInt$0= tmun08 ;
 tmun08=( auxL24  <<  1 );auxL24= auxL25 ;r0= neighborasInt$4 ;auxL10= r0 ;
 r0= neighborasInt$2 ;auxL05= r0 ;r0= neighborasInt$3 ;auxL04= r0 ;
 r0= neighborasInt$1 ;auxL07= r0 ;auxL06=~ auxL07 ;r0= neighborasInt$0 ;
 auxL09= r0 ;auxL08=~ auxL09 ;r0=( auxL08  &  auxL06 );auxL03$0=(( r0  & ( auxL05  &  auxL04 )) | ( auxL09  &  auxL07 ));
 auxL03$1=(( r0  & (~ auxL05  &  auxL04 )) | ( auxL08  &  auxL07 ));auxL03$2=(( r0  & ( auxL05  & ~ auxL04 )) | ( auxL09  &  auxL06 ));r0=~ auxL10 ;auxL02$0=( auxL10  &  auxL03$0 );
 auxL02$1=( auxL10  &  auxL03$1 );auxL02$2=( auxL10  &  auxL03$2 );auxL02$3=( r0  &  auxL03$0 );auxL02$4=( r0  &  auxL03$1 );
 auxL02$5=( r0  &  auxL03$2 );r0=(r4= auxL02$5 );r3=(r4= auxL02$4 );r2=(r4= auxL02$3 );
 r5=(r4= auxL02$2 );r1= auxL02$1 ;r4= neighborasInt$5 ;r6= auxL02$0 ;
 auxL01$0=( auxL02$0  | ( r4  &  r1 ));auxL01$1=( auxL02$1  | ( r4  &  r5 ));auxL01$2=( auxL02$2  | ( r4  &  r2 ));auxL01$3=( auxL02$3  | ( r4  &  r3 ));
 auxL01$4=( auxL02$4  | ( r4  &  r0 ));auxL01$5= auxL02$5 ;auxL01$6=( r4  &  r6 );r0= auxL01$0 ;
 utilrandN12$e[i-1]= r0 ;r0= auxL01$1 ;utilrandN12$se[i-1]= r0 ;r0= auxL01$2 ;
 utilrandN12$sw[i-1]= r0 ;r0= auxL01$3 ;utilrandN12$w[i-1]= r0 ;r0= auxL01$4 ;
 utilrandN12$nw[i-1]= r0 ;r0= auxL01$5 ;utilrandN12$ne[i-1]= r0 ;
  }
  ;
 ;
  }}