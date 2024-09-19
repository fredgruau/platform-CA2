package compiledCA;

import compiledMacro.*;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;
import java.util.ArrayList;
import java.util.HashMap;
import static simulator.Util.*;

public final class MvCA implements CAloops2 {
 public static void _fun2(PrShift p,int [][] mvBNbcc,int [] mvBMeeteside,int [] mvBMeet){
 int[] mvBNbcc$0=mvBNbcc[0],mvBNbcc$1=mvBNbcc[1];
p.mirror(mvBNbcc,compiler.Locus.locusV());p.mirror(mvBMeeteside,compiler.Locus.locusV());
p.prepareBit(mvBNbcc);p.prepareBit(mvBMeeteside)
 ;
// initialisation 
 int r0=0,r1=0,r2=0,r3=0,r4=0;
for (int i = 1; i < mvBNbcc$0.length -1; i++) {
 r0=~ mvBNbcc$0[i] ;r1= mvBNbcc$1[i] ;r3=((r4=(r2= r1 )) &  mvBNbcc$1[i] );r3=( r3  | ((~ r4  & ( r2  |  r0 )) &  mvBNbcc$0[i] ));
 mvBMeet[i]=( r3  |  mvBMeeteside[i] );
   } }
 public static void _fun3(PrShift p,int [][] auxC00,int [][] defEf,int [] mv,int [][] mvDoubleton){
 int[] mvDoubleton$h=mvDoubleton[0],mvDoubleton$d=mvDoubleton[1],mvDoubleton$ad=mvDoubleton[2],auxC00$h=auxC00[0],auxC00$d=auxC00[1],auxC00$ad=auxC00[2],defEf$h1=defEf[0],defEf$h2=defEf[1],defEf$d1=defEf[2],defEf$d2=defEf[3],defEf$ad1=defEf[4],defEf$ad2=defEf[5];
p.mirror(auxC00,compiler.Locus.locusE());p.mirror(defEf,compiler.Locus.locusEf());p.mirror(mv,compiler.Locus.locusV());
p.prepareBit(auxC00);p.prepareBit(defEf);p.prepareBit(mv)
 ;
// initialisation 
 int auxL27=0,auxL28=0,auxL29=0,auxO02=0,pdefEf=0,tmun08=0,tmun09=0,tmun10=0,tmun11=0,tmun12=0,tmun13=0,tmun14=0,tmun15=0,tmun16=0,tmun17=0,tmun18=0,tmun19=0,tmun20=0,tmun21=0,tmun22=0,tmun23=0,tmun24=0;
for (int i = 1; i < auxC00$h.length -1; i++) {
 pdefEf= defEf$h2[i] ;auxL29= mv[i] ;auxO02=(( tmun09  &  auxL29 ) |  tmun08 );tmun09= pdefEf ;
 pdefEf= defEf$h1[i] ;mvDoubleton$h[i-1]=( tmun13  & ~( auxO02  | (( tmun12  &  tmun11 ) |  tmun10 )));tmun12= pdefEf ;tmun13= auxC00$h[i] ;
 tmun11=( auxL28  <<  1 );pdefEf= defEf$d1[i] ;auxO02=(( tmun16  &  tmun15 ) |  tmun14 );tmun15=( auxL29  <<  1 );
 tmun16= pdefEf ;pdefEf= defEf$d2[i] ;mvDoubleton$d[i-1]=( tmun19  & ~( auxO02  | (( tmun18  & ( auxL29  >>>  1 )) |  tmun17 )));tmun18= pdefEf ;
 tmun19= auxC00$d[i] ;pdefEf= defEf$ad1[i] ;auxO02=(( tmun21  &  auxL29 ) |  tmun20 );tmun21= pdefEf ;
 pdefEf= defEf$ad2[i] ;mvDoubleton$ad[i-1]=( tmun24  & ~( auxO02  | (( tmun23  & ( auxL28  >>>  1 )) |  tmun22 )));tmun23= pdefEf ;tmun24= auxC00$ad[i] ;
 auxL28= auxL29 ;
   } }
 public static void _fun0(PrShift p,int [][] mvDoubleton,int [] mvSingleton,int [][] mvForcesyyy0RRanddir,int [][] mvForcesyyy0RRandside,int [][] mvMPush){
 int[] mvMPush$e=mvMPush[0],mvMPush$se=mvMPush[1],mvMPush$sw=mvMPush[2],mvMPush$w=mvMPush[3],mvMPush$nw=mvMPush[4],mvMPush$ne=mvMPush[5],mvDoubleton$h=mvDoubleton[0],mvDoubleton$d=mvDoubleton[1],mvDoubleton$ad=mvDoubleton[2],mvForcesyyy0RRanddir$e=mvForcesyyy0RRanddir[0],mvForcesyyy0RRanddir$se=mvForcesyyy0RRanddir[1],mvForcesyyy0RRanddir$sw=mvForcesyyy0RRanddir[2],mvForcesyyy0RRanddir$w=mvForcesyyy0RRanddir[3],mvForcesyyy0RRanddir$nw=mvForcesyyy0RRanddir[4],mvForcesyyy0RRanddir$ne=mvForcesyyy0RRanddir[5],mvForcesyyy0RRandside$h1=mvForcesyyy0RRandside[0],mvForcesyyy0RRandside$h2=mvForcesyyy0RRandside[1],mvForcesyyy0RRandside$d1=mvForcesyyy0RRandside[2],mvForcesyyy0RRandside$d2=mvForcesyyy0RRandside[3],mvForcesyyy0RRandside$ad1=mvForcesyyy0RRandside[4],mvForcesyyy0RRandside$ad2=mvForcesyyy0RRandside[5];
p.mirror(mvDoubleton,compiler.Locus.locusE());p.mirror(mvSingleton,compiler.Locus.locusV());p.mirror(mvForcesyyy0RRanddir,compiler.Locus.locusVe());p.mirror(mvForcesyyy0RRandside,compiler.Locus.locusEv());
p.prepareBit(mvDoubleton);p.prepareBit(mvSingleton);p.prepareBit(mvForcesyyy0RRanddir);p.prepareBit(mvForcesyyy0RRandside)
 ;
// initialisation 
 int auxL32=0,auxL33=0,auxL34=0,auxL35=0,tmun25=0,tmun26=0;
for (int i = 1; i < mvDoubleton$h.length -1; i++) {
 auxL34= mvSingleton[i] ;auxL32= mvDoubleton$d[i] ;mvMPush$e[i]=(( auxL32  &  mvForcesyyy0RRandside$d2[i] ) | ( auxL34  &  mvForcesyyy0RRanddir$e[i] ));auxL33= mvDoubleton$ad[i] ;
 mvMPush$se[i]=(( auxL33  &  mvForcesyyy0RRandside$ad2[i] ) | ( auxL34  &  mvForcesyyy0RRanddir$se[i] ));auxL35= mvDoubleton$h[i] ;mvMPush$sw[i]=((( auxL35  &  mvForcesyyy0RRandside$h1[i] ) >>>  1 ) | ( auxL34  &  mvForcesyyy0RRanddir$sw[i] ));mvMPush$w[i]=( tmun25  | ( auxL34  &  mvForcesyyy0RRanddir$w[i] ));
 tmun25=( auxL32  &  mvForcesyyy0RRandside$d1[i] );mvMPush$nw[i]=( tmun26  | ( auxL34  &  mvForcesyyy0RRanddir$nw[i] ));tmun26=(( auxL33  &  mvForcesyyy0RRandside$ad1[i] ) <<  1 );mvMPush$ne[i]=(( auxL35  &  mvForcesyyy0RRandside$h2[i] ) | ( auxL34  &  mvForcesyyy0RRanddir$ne[i] ));
   } }
 public static void _fun1(PrShift p,int [][] mvBrdin,int [] mvBMeet,int [] mvInvade,int [] mv,int [][] defVe,int [] llmv){
 int[] mvBrdin$e=mvBrdin[0],mvBrdin$se=mvBrdin[1],mvBrdin$sw=mvBrdin[2],mvBrdin$w=mvBrdin[3],mvBrdin$nw=mvBrdin[4],mvBrdin$ne=mvBrdin[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvBrdin,compiler.Locus.locusVe());p.mirror(mvBMeet,compiler.Locus.locusV());p.mirror(mvInvade,compiler.Locus.locusV());p.mirror(mv,compiler.Locus.locusV());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvBrdin);p.prepareBit(mvBMeet);p.prepareBit(mvInvade);p.prepareBit(mv);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL36=0,mvBrdv=0,pdefVe=0;
for (int i = 1; i < mvBrdin$e.length -1; i++) {
 pdefVe= defVe$e[i] ;mvBrdv=( pdefVe  &  mvBrdin$e[i] );pdefVe= defVe$se[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$se[i] ));
 pdefVe= defVe$sw[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$sw[i] ));pdefVe= defVe$w[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$w[i] ));
 pdefVe= defVe$nw[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$nw[i] ));pdefVe= defVe$ne[i] ;llmv[i]=( mv[i]  | ((( mvBrdv  | ( pdefVe  &  mvBrdin$ne[i] )) & ~ mvBMeet[i] ) &  mvInvade[i] ));
   } }
 public static void _fun6(PrShift p,int [][] mvMPush,int [][] defVe,int [] mvInvadeR){
 int[] mvMPush$e=mvMPush[0],mvMPush$se=mvMPush[1],mvMPush$sw=mvMPush[2],mvMPush$w=mvMPush[3],mvMPush$nw=mvMPush[4],mvMPush$ne=mvMPush[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvMPush,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvMPush);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL37=0,mvInvade=0,pdefVe=0,tmun27=0,tmun28=0,tmun29=0,tmun30=0,tmun31=0,tmun32=0,tmun33=0,tmun34=0,tmun35=0,tmun36=0,tmun37=0,tmun38=0,tmun39=0,tmun40=0,tmun41=0,tmun42=0,tmun43=0,tmun44=0;
for (int i = 1; i < mvMPush$e.length -1; i++) {
 pdefVe= defVe$e[i] ;mvInvade=(( tmun29  &  tmun28 ) |  tmun27 );tmun29= pdefVe ;tmun28=( mvMPush$w[i]  <<  1 );
 pdefVe= defVe$se[i] ;mvInvade=( mvInvade  | (( tmun31  &  mvMPush$nw[i] ) |  tmun30 ));tmun31= pdefVe ;pdefVe= defVe$sw[i] ;
 mvInvade=( mvInvade  | (( tmun33  & ( mvMPush$ne[i]  >>>  1 )) |  tmun32 ));tmun33= pdefVe ;pdefVe= defVe$w[i] ;mvInvade=( mvInvade  | (( tmun36  & ( tmun35  >>>  1 )) |  tmun34 ));
 tmun35= mvMPush$e[i] ;tmun36= pdefVe ;pdefVe= defVe$nw[i] ;mvInvade=( mvInvade  | (( tmun40  &  tmun38 ) |  tmun37 ));
 tmun40= pdefVe ;tmun38= tmun39 ;tmun39= mvMPush$se[i] ;pdefVe= defVe$ne[i] ;
 mvInvadeR[i-1]=( mvInvade  | (( tmun44  &  tmun42 ) |  tmun41 ));tmun44= pdefVe ;tmun42=( tmun43  <<  1 );tmun43= mvMPush$sw[i] ;
   } }
 public static void _fun7(PrShift p,int [][] mvBrdin,int [][] defVe,int [] auxC01R){
 int[] mvBrdin$e=mvBrdin[0],mvBrdin$se=mvBrdin[1],mvBrdin$sw=mvBrdin[2],mvBrdin$w=mvBrdin[3],mvBrdin$nw=mvBrdin[4],mvBrdin$ne=mvBrdin[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvBrdin,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvBrdin);p.prepareBit(defVe)
 ;
// initialisation 
 int auxC01=0,auxL39=0,pdefVe=0;
for (int i = 1; i < mvBrdin$e.length -1; i++) {
 pdefVe= defVe$e[i] ;auxC01=( pdefVe  &  mvBrdin$e[i] );pdefVe= defVe$se[i] ;auxC01=( auxC01  | ( pdefVe  &  mvBrdin$se[i] ));
 pdefVe= defVe$sw[i] ;auxC01=( auxC01  | ( pdefVe  &  mvBrdin$sw[i] ));pdefVe= defVe$w[i] ;auxC01=( auxC01  | ( pdefVe  &  mvBrdin$w[i] ));
 pdefVe= defVe$nw[i] ;auxC01=( auxC01  | ( pdefVe  &  mvBrdin$nw[i] ));pdefVe= defVe$ne[i] ;auxC01R[i]=( auxC01  | ( pdefVe  &  mvBrdin$ne[i] ));
   } }
 public static void _fun4(PrShift p,int [] mv,int [][] defVe,int [] mvSingleton){
 int[] defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mv,compiler.Locus.locusV());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mv);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL40=0,auxL41=0,auxL42=0,auxO04=0,pdefVe=0,pmv=0,tmun45=0,tmun46=0,tmun47=0,tmun48=0,tmun49=0,tmun50=0,tmun51=0,tmun52=0,tmun53=0,tmun54=0,tmun55=0,tmun56=0,tmun57=0,tmun58=0,tmun59=0,tmun60=0;
for (int i = 1; i < mv.length -1; i++) {
 pdefVe= defVe$e[i] ;pmv= mv[i] ;auxL42=~ pmv ;auxO04=(( tmun47  &  tmun46 ) |  tmun45 );
 tmun47= pdefVe ;tmun46=( auxL42  <<  1 );pdefVe= defVe$se[i] ;auxO04=( auxO04  & (( tmun49  &  auxL42 ) |  tmun48 ));
 tmun49= pdefVe ;pdefVe= defVe$sw[i] ;auxO04=( auxO04  & (( tmun51  & ( auxL42  >>>  1 )) |  tmun50 ));tmun51= pdefVe ;
 pdefVe= defVe$w[i] ;auxO04=( auxO04  & (( tmun53  & ( auxL41  >>>  1 )) |  tmun52 ));tmun53= pdefVe ;pdefVe= defVe$nw[i] ;
 auxO04=( auxO04  & (( tmun56  &  tmun55 ) |  tmun54 ));tmun56= pdefVe ;tmun55= auxL41 ;pdefVe= defVe$ne[i] ;
 mvSingleton[i-1]=(( auxO04  & (( tmun60  &  tmun59 ) |  tmun58 )) &  tmun57 );tmun59=( auxL41  <<  1 );tmun60= pdefVe ;tmun57= pmv ;
 auxL41= auxL42 ;
   } }
 public static void _fun5(PrShift p,int [][] auxC02,int [][] mvBTwoadjblob,int [][] mvBMeete){
 int[] mvBMeete$h=mvBMeete[0],mvBMeete$d=mvBMeete[1],mvBMeete$ad=mvBMeete[2],auxC02$e=auxC02[0],auxC02$se=auxC02[1],auxC02$sw=auxC02[2],auxC02$w=auxC02[3],auxC02$nw=auxC02[4],auxC02$ne=auxC02[5],mvBTwoadjblob$h=mvBTwoadjblob[0],mvBTwoadjblob$d=mvBTwoadjblob[1],mvBTwoadjblob$ad=mvBTwoadjblob[2];
p.mirror(auxC02,compiler.Locus.locusVe());p.mirror(mvBTwoadjblob,compiler.Locus.locusE());
p.prepareBit(auxC02);p.prepareBit(mvBTwoadjblob)
 ;
// initialisation 
 int tmun61=0,tmun62=0,tmun63=0,tmun64=0,tmun65=0,tmun66=0;
for (int i = 1; i < auxC02$e.length -1; i++) {
 mvBMeete$h[i-1]=(~ tmun62  &  tmun61 );tmun61= mvBTwoadjblob$h[i] ;tmun62=(( auxC02$w[i]  <<  1 ) |  auxC02$e[i] );mvBMeete$d[i-1]=(~( tmun64  |  auxC02$nw[i] ) &  tmun63 );
 tmun64= auxC02$se[i] ;tmun63= mvBTwoadjblob$d[i] ;mvBMeete$ad[i-1]=(~( tmun66  | ( auxC02$ne[i]  >>>  1 )) &  tmun65 );tmun65= mvBTwoadjblob$ad[i] ;
 tmun66= auxC02$sw[i] ;
   } }
public int CAmemWidth() {return 64;}

@Override public ArrayList<String> theLoops(PrShift p,int[][] m) {ArrayList<String> bugs=new ArrayList<>();
int[]mvForcesyyy0R=m[42],mvSingleton=m[32],llbugV=m[12],mv=m[15],mvBMeeteside=m[43],mvBMeet=m[33],mvForcesyyy0RNext=m[36],llmvForcesyyy0R=m[14],llmv=m[13],mvInvade=m[16],auxC01=m[42];
int[][]mvBTwoadjblob= new int[][]{m[43],m[44],m[51]},defVe= new int[][]{m[41],m[40],m[39],m[38],m[37],m[36]},mvDoubleton= new int[][]{m[23],m[24],m[25]},mvBNbcc= new int[][]{m[34],m[35]},lldefVe= new int[][]{m[0],m[1],m[2],m[3],m[4],m[5]},mvBrdin= new int[][]{m[45],m[46],m[47],m[48],m[49],m[50]},auxC03= new int[][]{m[42],m[52],m[53],m[54],m[55],m[56]},mvForcesyyy0RRandside= new int[][]{m[26],m[27],m[28],m[29],m[30],m[31]},mvBMeete= new int[][]{m[42],m[52],m[53]},auxC02= new int[][]{m[57],m[58],m[59],m[60],m[61],m[62]},auxC00= new int[][]{m[55],m[56],m[57]},defEf= new int[][]{m[63],m[62],m[61],m[60],m[59],m[58]},mvMPush= new int[][]{m[17],m[18],m[19],m[20],m[21],m[22]},mvForcesyyy0RRanddir= new int[][]{m[43],m[44],m[51],m[52],m[53],m[54]},lldefEf= new int[][]{m[6],m[7],m[8],m[9],m[10],m[11]},mvBrd= new int[][]{m[42],m[43],m[44]};

copy(llmv,mv);
copy(lldefVe,defVe);
redsxorb.ve_1(p,mv,mvBrd);
topo.brdin_1_1(p,mvBrd,mv,mvBrdin,lldefVe);
_fun7(p,mvBrdin,defVe,auxC01);
redsandb.ve_1(p,auxC01,mvBTwoadjblob);
redT.enlargeEF_1(p,mvBrdin,auxC03);
redT.enlargeFE_1(p,auxC03,auxC02);
_fun5(p,auxC02,mvBTwoadjblob,mvBMeete);
redsorb.ev_1(p,mvBMeete,mvBMeeteside,lldefVe);
topo.nbcc_1(p,mvBrdin,mvBNbcc);
_fun2(p,mvBNbcc,mvBMeeteside,mvBMeet);
_fun4(p,mv,defVe,mvSingleton);
copy(llmvForcesyyy0R,mvForcesyyy0R);
util.randN12_1(p,mvForcesyyy0R,mvForcesyyy0RRanddir);
util.randE2_1(p,mvForcesyyy0R,mvForcesyyy0RRandside);
redsandb.ve_1(p,mv,auxC00);
copy(lldefEf,defEf);
_fun3(p,auxC00,defEf,mv,mvDoubleton);
_fun0(p,mvDoubleton,mvSingleton,mvForcesyyy0RRanddir,mvForcesyyy0RRandside,mvMPush);
_fun6(p,mvMPush,defVe,mvInvade);
_fun1(p,mvBrdin,mvBMeet,mvInvade,mv,defVe,llmv);
util.rand_1(p,mvForcesyyy0R,mvForcesyyy0RNext);
memo(mvForcesyyy0RNext,llmvForcesyyy0R);
show(mvBNbcc);
show(mvBMeet);
show(mvInvade);
show(mvSingleton);
show(mvForcesyyy0RRandside);
show(mvDoubleton);
show(mv);
show(mvMPush); return bugs;}



@Override public HashMap<String, List<Integer>> fieldOffset() {HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
map.put("mvBTwoadjblob", li(43,44,51));
map.put("mvBNbcc", li(34,35));
map.put("llbugV", li(12));
map.put("lldefVe", li(0,1,2,3,4,5));
map.put("mvBMeet", li(33));
map.put("mvInvade", li(16));
map.put("mvForcesyyy0RRandside", li(26,27,28,29,30,31));
map.put("mvBMeete", li(42,52,53));
map.put("auxC00", li(55,56,57));
map.put("mvForcesyyy0RNext", li(36));
map.put("mvForcesyyy0RRanddir", li(43,44,51,52,53,54));
map.put("llmvForcesyyy0R", li(14));
map.put("llmv", li(13));
map.put("lldefEf", li(6,7,8,9,10,11));
map.put("mvBrd", li(42,43,44));
map.put("mvForcesyyy0R", li(42));
map.put("mvDoubleton", li(23,24,25));
map.put("mv", li(15));
map.put("mvBMeeteside", li(43));
map.put("mvBrdin", li(45,46,47,48,49,50));
map.put("auxC03", li(42,52,53,54,55,56));
map.put("auxC01", li(42));
map.put("auxC02", li(57,58,59,60,61,62));
map.put("mvSingleton", li(32));
map.put("mvMPush", li(17,18,19,20,21,22)); return (map);}
@Override public HashMap<String, Locus> fieldLocus() {HashMap<String, Locus> map = new HashMap<>();
 map.put("mvForcesyyy0R",compiler.Locus.locusV());
 map.put("auxC01",compiler.Locus.locusV());
 map.put("mvBMeeteside",compiler.Locus.locusV());
 map.put("lldefEf",compiler.Locus.locusEf());
 map.put("mvSingleton",compiler.Locus.locusV());
 map.put("auxC03",compiler.Locus.locusVf());
 map.put("defEf",compiler.Locus.locusEf());
 map.put("defVe",compiler.Locus.locusVe());
 map.put("mvBMeete",compiler.Locus.locusE());
 map.put("mvForcesyyy0RRanddir",compiler.Locus.locusVe());
 map.put("mvForcesyyy0RRandside",compiler.Locus.locusEv());
 map.put("lldefVe",compiler.Locus.locusVe());
 map.put("mvBrdin",compiler.Locus.locusVe());
 map.put("mvBNbcc",compiler.Locus.locusV());
 map.put("mvBrd",compiler.Locus.locusE());
 map.put("mvBMeet",compiler.Locus.locusV());
 map.put("auxC02",compiler.Locus.locusVe());
 map.put("auxC00",compiler.Locus.locusE());
 map.put("mvDoubleton",compiler.Locus.locusE());
 map.put("mvForcesyyy0RNext",compiler.Locus.locusV());
 map.put("mvBTwoadjblob",compiler.Locus.locusE());
 map.put("mvMPush",compiler.Locus.locusVe());
 map.put("llbugV",compiler.Locus.locusV());
 map.put("llmv",compiler.Locus.locusV());
 map.put("mvInvade",compiler.Locus.locusV());
 map.put("mv",compiler.Locus.locusV());
 map.put("llmvForcesyyy0R",compiler.Locus.locusV()); return (map);}
@Override public HashMap<String, Integer> fieldBitSize() { HashMap<String, Integer> map = new HashMap<>();
 map.put("mvBNbcc",2); return (map); }
@Override  public String displayableLayerHierarchy() { return "mv(mvForcesyyy0(mvForcesyyy0R(mvForcesyyy0RRandside)))(mvB(mvBNbcc)(mvBMeet))(mvM(mvMPush))(mvDoubleton)(mvSingleton)(mvInvade).";}
@Override public HashMap<String, String> init() {HashMap<String, String> map = new HashMap<>();
  map.put("lldefVe","def");
 map.put("lldefEf","def");
 map.put("llbugV","false");
 map.put("llmv","global");
 map.put("llmvForcesyyy0R","random");
 return (map);}
@Override public int gateCount(){return (238 );}

}
