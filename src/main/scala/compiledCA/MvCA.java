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
 public static void _fun2(PrShift p,int [][] auxC03,int [][] defEf,int [] mv,int [][] mvDoubleton){
 int[] mvDoubleton$h=mvDoubleton[0],mvDoubleton$d=mvDoubleton[1],mvDoubleton$ad=mvDoubleton[2],auxC03$h=auxC03[0],auxC03$d=auxC03[1],auxC03$ad=auxC03[2],defEf$h1=defEf[0],defEf$h2=defEf[1],defEf$d1=defEf[2],defEf$d2=defEf[3],defEf$ad1=defEf[4],defEf$ad2=defEf[5];
p.mirror(auxC03,compiler.Locus.locusE());p.mirror(defEf,compiler.Locus.locusEf());p.mirror(mv,compiler.Locus.locusV());
p.prepareBit(auxC03);p.prepareBit(defEf);p.prepareBit(mv)
 ;
// initialisation 
 int auxL27=0,auxL28=0,auxL29=0,auxO02=0,pdefEf=0,tmun08=0,tmun09=0,tmun10=0,tmun11=0,tmun12=0,tmun13=0,tmun14=0,tmun15=0,tmun16=0,tmun17=0,tmun18=0,tmun19=0,tmun20=0,tmun21=0,tmun22=0,tmun23=0,tmun24=0;
for (int i = 1; i < auxC03$h.length -1; i++) {
 pdefEf= defEf$h2[i] ;auxL29= mv[i] ;auxO02=(( tmun09  &  auxL29 ) |  tmun08 );tmun09= pdefEf ;
 pdefEf= defEf$h1[i] ;mvDoubleton$h[i-1]=( tmun13  & ~( auxO02  | (( tmun12  &  tmun11 ) |  tmun10 )));tmun12= pdefEf ;tmun13= auxC03$h[i] ;
 tmun11=( auxL28  <<  1 );pdefEf= defEf$d1[i] ;auxO02=(( tmun16  &  tmun15 ) |  tmun14 );tmun15=( auxL29  <<  1 );
 tmun16= pdefEf ;pdefEf= defEf$d2[i] ;mvDoubleton$d[i-1]=( tmun19  & ~( auxO02  | (( tmun18  & ( auxL29  >>>  1 )) |  tmun17 )));tmun18= pdefEf ;
 tmun19= auxC03$d[i] ;pdefEf= defEf$ad1[i] ;auxO02=(( tmun21  &  auxL29 ) |  tmun20 );tmun21= pdefEf ;
 pdefEf= defEf$ad2[i] ;mvDoubleton$ad[i-1]=( tmun24  & ~( auxO02  | (( tmun23  & ( auxL28  >>>  1 )) |  tmun22 )));tmun24= auxC03$ad[i] ;tmun23= pdefEf ;
 auxL28= auxL29 ;
   } }
 public static void _fun3(PrShift p,int [][] auxC01,int [][] mvBTwoadjblob,int [][] mvBMeete){
 int[] mvBMeete$h=mvBMeete[0],mvBMeete$d=mvBMeete[1],mvBMeete$ad=mvBMeete[2],auxC01$e=auxC01[0],auxC01$se=auxC01[1],auxC01$sw=auxC01[2],auxC01$w=auxC01[3],auxC01$nw=auxC01[4],auxC01$ne=auxC01[5],mvBTwoadjblob$h=mvBTwoadjblob[0],mvBTwoadjblob$d=mvBTwoadjblob[1],mvBTwoadjblob$ad=mvBTwoadjblob[2];
p.mirror(auxC01,compiler.Locus.locusVe());p.mirror(mvBTwoadjblob,compiler.Locus.locusE());
p.prepareBit(auxC01);p.prepareBit(mvBTwoadjblob)
 ;
// initialisation 
 int tmun25=0,tmun26=0,tmun27=0,tmun28=0,tmun29=0,tmun30=0;
for (int i = 1; i < auxC01$e.length -1; i++) {
 mvBMeete$h[i-1]=(~ tmun26  &  tmun25 );tmun26=(( auxC01$w[i]  <<  1 ) |  auxC01$e[i] );tmun25= mvBTwoadjblob$h[i] ;mvBMeete$d[i-1]=(~( tmun28  |  auxC01$nw[i] ) &  tmun27 );
 tmun27= mvBTwoadjblob$d[i] ;tmun28= auxC01$se[i] ;mvBMeete$ad[i-1]=(~( tmun30  | ( auxC01$ne[i]  >>>  1 )) &  tmun29 );tmun29= mvBTwoadjblob$ad[i] ;
 tmun30= auxC01$sw[i] ;
   } }
 public static void _fun0(PrShift p,int [][] mvBrdin,int [][] defVe,int [] auxC00R){
 int[] mvBrdin$e=mvBrdin[0],mvBrdin$se=mvBrdin[1],mvBrdin$sw=mvBrdin[2],mvBrdin$w=mvBrdin[3],mvBrdin$nw=mvBrdin[4],mvBrdin$ne=mvBrdin[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvBrdin,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvBrdin);p.prepareBit(defVe)
 ;
// initialisation 
 int auxC00=0,auxL32=0,pdefVe=0;
for (int i = 1; i < mvBrdin$e.length -1; i++) {
 pdefVe= defVe$e[i] ;auxC00=( pdefVe  &  mvBrdin$e[i] );pdefVe= defVe$se[i] ;auxC00=( auxC00  | ( pdefVe  &  mvBrdin$se[i] ));
 pdefVe= defVe$sw[i] ;auxC00=( auxC00  | ( pdefVe  &  mvBrdin$sw[i] ));pdefVe= defVe$w[i] ;auxC00=( auxC00  | ( pdefVe  &  mvBrdin$w[i] ));
 pdefVe= defVe$nw[i] ;auxC00=( auxC00  | ( pdefVe  &  mvBrdin$nw[i] ));pdefVe= defVe$ne[i] ;auxC00R[i]=( auxC00  | ( pdefVe  &  mvBrdin$ne[i] ));
   } }
 public static void _fun1(PrShift p,int [][] mvMPush,int [][] defVe,int [] mvInvadeR){
 int[] mvMPush$e=mvMPush[0],mvMPush$se=mvMPush[1],mvMPush$sw=mvMPush[2],mvMPush$w=mvMPush[3],mvMPush$nw=mvMPush[4],mvMPush$ne=mvMPush[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvMPush,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvMPush);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL33=0,mvInvade=0,pdefVe=0,tmun31=0,tmun32=0,tmun33=0,tmun34=0,tmun35=0,tmun36=0,tmun37=0,tmun38=0,tmun39=0,tmun40=0,tmun41=0,tmun42=0,tmun43=0,tmun44=0,tmun45=0,tmun46=0,tmun47=0,tmun48=0;
for (int i = 1; i < mvMPush$e.length -1; i++) {
 pdefVe= defVe$e[i] ;mvInvade=(( tmun33  &  tmun32 ) |  tmun31 );tmun32=( mvMPush$w[i]  <<  1 );tmun33= pdefVe ;
 pdefVe= defVe$se[i] ;mvInvade=( mvInvade  | (( tmun35  &  mvMPush$nw[i] ) |  tmun34 ));tmun35= pdefVe ;pdefVe= defVe$sw[i] ;
 mvInvade=( mvInvade  | (( tmun37  & ( mvMPush$ne[i]  >>>  1 )) |  tmun36 ));tmun37= pdefVe ;pdefVe= defVe$w[i] ;mvInvade=( mvInvade  | (( tmun40  & ( tmun39  >>>  1 )) |  tmun38 ));
 tmun39= mvMPush$e[i] ;tmun40= pdefVe ;pdefVe= defVe$nw[i] ;mvInvade=( mvInvade  | (( tmun44  &  tmun42 ) |  tmun41 ));
 tmun44= pdefVe ;tmun42= tmun43 ;tmun43= mvMPush$se[i] ;pdefVe= defVe$ne[i] ;
 mvInvadeR[i-1]=( mvInvade  | (( tmun48  &  tmun46 ) |  tmun45 ));tmun48= pdefVe ;tmun46=( tmun47  <<  1 );tmun47= mvMPush$sw[i] ;
   } }
 public static void _fun6(PrShift p,int [] mv,int [][] defVe,int [] mvSingleton){
 int[] defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mv,compiler.Locus.locusV());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mv);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL34=0,auxL35=0,auxL36=0,auxO00=0,pdefVe=0,pmv=0,tmun49=0,tmun50=0,tmun51=0,tmun52=0,tmun53=0,tmun54=0,tmun55=0,tmun56=0,tmun57=0,tmun58=0,tmun59=0,tmun60=0,tmun61=0,tmun62=0,tmun63=0,tmun64=0;
for (int i = 1; i < mv.length -1; i++) {
 pmv= mv[i] ;pdefVe= defVe$e[i] ;auxL36=~ pmv ;auxO00=(( tmun51  &  tmun50 ) |  tmun49 );
 tmun51= pdefVe ;tmun50=( auxL36  <<  1 );pdefVe= defVe$se[i] ;auxO00=( auxO00  & (( tmun53  &  auxL36 ) |  tmun52 ));
 tmun53= pdefVe ;pdefVe= defVe$sw[i] ;auxO00=( auxO00  & (( tmun55  & ( auxL36  >>>  1 )) |  tmun54 ));tmun55= pdefVe ;
 pdefVe= defVe$w[i] ;auxO00=( auxO00  & (( tmun57  & ( auxL35  >>>  1 )) |  tmun56 ));tmun57= pdefVe ;pdefVe= defVe$nw[i] ;
 auxO00=( auxO00  & (( tmun60  &  tmun59 ) |  tmun58 ));tmun59= auxL35 ;tmun60= pdefVe ;pdefVe= defVe$ne[i] ;
 mvSingleton[i-1]=(( auxO00  & (( tmun64  &  tmun63 ) |  tmun62 )) &  tmun61 );tmun61= pmv ;tmun64= pdefVe ;tmun63=( auxL35  <<  1 );
 auxL35= auxL36 ;
   } }
 public static void _fun7(PrShift p,int [][] mvDoubleton,int [] mvSingleton,int [][] mvForcesyyy0RRanddir,int [][] mvForcesyyy0RRandside,int [][] mvMPush){
 int[] mvMPush$e=mvMPush[0],mvMPush$se=mvMPush[1],mvMPush$sw=mvMPush[2],mvMPush$w=mvMPush[3],mvMPush$nw=mvMPush[4],mvMPush$ne=mvMPush[5],mvDoubleton$h=mvDoubleton[0],mvDoubleton$d=mvDoubleton[1],mvDoubleton$ad=mvDoubleton[2],mvForcesyyy0RRanddir$e=mvForcesyyy0RRanddir[0],mvForcesyyy0RRanddir$se=mvForcesyyy0RRanddir[1],mvForcesyyy0RRanddir$sw=mvForcesyyy0RRanddir[2],mvForcesyyy0RRanddir$w=mvForcesyyy0RRanddir[3],mvForcesyyy0RRanddir$nw=mvForcesyyy0RRanddir[4],mvForcesyyy0RRanddir$ne=mvForcesyyy0RRanddir[5],mvForcesyyy0RRandside$h1=mvForcesyyy0RRandside[0],mvForcesyyy0RRandside$h2=mvForcesyyy0RRandside[1],mvForcesyyy0RRandside$d1=mvForcesyyy0RRandside[2],mvForcesyyy0RRandside$d2=mvForcesyyy0RRandside[3],mvForcesyyy0RRandside$ad1=mvForcesyyy0RRandside[4],mvForcesyyy0RRandside$ad2=mvForcesyyy0RRandside[5];
p.mirror(mvDoubleton,compiler.Locus.locusE());p.mirror(mvSingleton,compiler.Locus.locusV());p.mirror(mvForcesyyy0RRanddir,compiler.Locus.locusVe());p.mirror(mvForcesyyy0RRandside,compiler.Locus.locusEv());
p.prepareBit(mvDoubleton);p.prepareBit(mvSingleton);p.prepareBit(mvForcesyyy0RRanddir);p.prepareBit(mvForcesyyy0RRandside)
 ;
// initialisation 
 int auxL38=0,auxL39=0,auxL40=0,auxL41=0,tmun65=0,tmun66=0;
for (int i = 1; i < mvDoubleton$h.length -1; i++) {
 auxL40= mvSingleton[i] ;auxL38= mvDoubleton$d[i] ;mvMPush$e[i]=(( auxL38  &  mvForcesyyy0RRandside$d2[i] ) | ( auxL40  &  mvForcesyyy0RRanddir$e[i] ));auxL39= mvDoubleton$ad[i] ;
 mvMPush$se[i]=(( auxL39  &  mvForcesyyy0RRandside$ad2[i] ) | ( auxL40  &  mvForcesyyy0RRanddir$se[i] ));auxL41= mvDoubleton$h[i] ;mvMPush$sw[i]=((( auxL41  &  mvForcesyyy0RRandside$h1[i] ) >>>  1 ) | ( auxL40  &  mvForcesyyy0RRanddir$sw[i] ));mvMPush$w[i]=( tmun65  | ( auxL40  &  mvForcesyyy0RRanddir$w[i] ));
 tmun65=( auxL38  &  mvForcesyyy0RRandside$d1[i] );mvMPush$nw[i]=( tmun66  | ( auxL40  &  mvForcesyyy0RRanddir$nw[i] ));tmun66=(( auxL39  &  mvForcesyyy0RRandside$ad1[i] ) <<  1 );mvMPush$ne[i]=(( auxL41  &  mvForcesyyy0RRandside$h2[i] ) | ( auxL40  &  mvForcesyyy0RRanddir$ne[i] ));
   } }
 public static void _fun4(PrShift p,int [][] mvBrdin,int [] mvBMeet,int [] mvInvade,int [] mv,int [][] defVe,int [] llmv){
 int[] mvBrdin$e=mvBrdin[0],mvBrdin$se=mvBrdin[1],mvBrdin$sw=mvBrdin[2],mvBrdin$w=mvBrdin[3],mvBrdin$nw=mvBrdin[4],mvBrdin$ne=mvBrdin[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(mvBrdin,compiler.Locus.locusVe());p.mirror(mvBMeet,compiler.Locus.locusV());p.mirror(mvInvade,compiler.Locus.locusV());p.mirror(mv,compiler.Locus.locusV());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(mvBrdin);p.prepareBit(mvBMeet);p.prepareBit(mvInvade);p.prepareBit(mv);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL42=0,mvBrdv=0,pdefVe=0;
for (int i = 1; i < mvBrdin$e.length -1; i++) {
 pdefVe= defVe$e[i] ;mvBrdv=( pdefVe  &  mvBrdin$e[i] );pdefVe= defVe$se[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$se[i] ));
 pdefVe= defVe$sw[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$sw[i] ));pdefVe= defVe$w[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$w[i] ));
 pdefVe= defVe$nw[i] ;mvBrdv=( mvBrdv  | ( pdefVe  &  mvBrdin$nw[i] ));pdefVe= defVe$ne[i] ;llmv[i]=( mv[i]  | ((( mvBrdv  | ( pdefVe  &  mvBrdin$ne[i] )) & ~ mvBMeet[i] ) &  mvInvade[i] ));
   } }
 public static void _fun5(PrShift p,int [][] mvBNbcc,int [] mvBMeeteside,int [] mvBMeet){
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
public int CAmemWidth() {return 64;}

@Override public ArrayList<String> theLoops(PrShift p,int[][] m) {ArrayList<String> bugs=new ArrayList<>();
int[]auxC00=m[43],mvForcesyyy0R=m[36],mvSingleton=m[32],llbugV=m[12],mv=m[15],mvBMeeteside=m[44],mvBMeet=m[29],mvForcesyyy0RNext=m[37],llmvForcesyyy0R=m[14],llmv=m[13],mvInvade=m[16];
int[][]mvBTwoadjblob= new int[][]{m[44],m[45],m[52]},defVe= new int[][]{m[42],m[41],m[40],m[39],m[38],m[37]},mvDoubleton= new int[][]{m[33],m[34],m[35]},mvBNbcc= new int[][]{m[30],m[31]},lldefVe= new int[][]{m[0],m[1],m[2],m[3],m[4],m[5]},mvBrdin= new int[][]{m[46],m[47],m[48],m[49],m[50],m[51]},auxC03= new int[][]{m[43],m[44],m[45]},auxC01= new int[][]{m[58],m[59],m[60],m[61],m[62],m[63]},mvForcesyyy0RRandside= new int[][]{m[23],m[24],m[25],m[26],m[27],m[28]},mvBMeete= new int[][]{m[43],m[53],m[54]},auxC02= new int[][]{m[43],m[53],m[54],m[55],m[56],m[57]},defEf= new int[][]{m[42],m[41],m[40],m[39],m[38],m[37]},mvMPush= new int[][]{m[17],m[18],m[19],m[20],m[21],m[22]},mvForcesyyy0RRanddir= new int[][]{m[43],m[44],m[45],m[52],m[53],m[54]},lldefEf= new int[][]{m[6],m[7],m[8],m[9],m[10],m[11]},mvBrd= new int[][]{m[43],m[44],m[45]};

copy(llmvForcesyyy0R,mvForcesyyy0R);
util.rand_1(p,mvForcesyyy0R,mvForcesyyy0RNext);
memo(mvForcesyyy0RNext,llmvForcesyyy0R);
copy(llmv,mv);
copy(lldefEf,defEf);
redsandb.ve_1(p,mv,auxC03);
_fun2(p,auxC03,defEf,mv,mvDoubleton);
show(mvDoubleton);
copy(lldefVe,defVe);
_fun6(p,mv,defVe,mvSingleton);
show(mvSingleton);
redsxorb.ve_1(p,mv,mvBrd);
topo.brdin_1_1(p,mvBrd,mv,mvBrdin,lldefVe);
topo.nbcc_1(p,mvBrdin,mvBNbcc);
show(mvBNbcc);
_fun0(p,mvBrdin,defVe,auxC00);
redsandb.ve_1(p,auxC00,mvBTwoadjblob);
redT.enlargeEF_1(p,mvBrdin,auxC02);
redT.enlargeFE_1(p,auxC02,auxC01);
_fun3(p,auxC01,mvBTwoadjblob,mvBMeete);
redsorb.ev_1(p,mvBMeete,mvBMeeteside,lldefVe);
_fun5(p,mvBNbcc,mvBMeeteside,mvBMeet);
show(mvBMeet);
util.randE2_1(p,mvForcesyyy0R,mvForcesyyy0RRandside);
show(mvForcesyyy0RRandside);
util.randN12_1(p,mvForcesyyy0R,mvForcesyyy0RRanddir);
_fun7(p,mvDoubleton,mvSingleton,mvForcesyyy0RRanddir,mvForcesyyy0RRandside,mvMPush);
_fun1(p,mvMPush,defVe,mvInvade);
_fun4(p,mvBrdin,mvBMeet,mvInvade,mv,defVe,llmv);
show(mv);
show(mvMPush);
show(mvInvade); return bugs;}



@Override public HashMap<String, List<Integer>> fieldOffset() {HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
map.put("mvBTwoadjblob", li(44,45,52));
map.put("mvBNbcc", li(30,31));
map.put("llbugV", li(12));
map.put("lldefVe", li(0,1,2,3,4,5));
map.put("mvBMeet", li(29));
map.put("mvInvade", li(16));
map.put("mvForcesyyy0RRandside", li(23,24,25,26,27,28));
map.put("mvBMeete", li(43,53,54));
map.put("auxC00", li(43));
map.put("mvForcesyyy0RNext", li(37));
map.put("mvForcesyyy0RRanddir", li(43,44,45,52,53,54));
map.put("llmvForcesyyy0R", li(14));
map.put("llmv", li(13));
map.put("lldefEf", li(6,7,8,9,10,11));
map.put("mvBrd", li(43,44,45));
map.put("mvForcesyyy0R", li(36));
map.put("mvDoubleton", li(33,34,35));
map.put("mv", li(15));
map.put("mvBMeeteside", li(44));
map.put("mvBrdin", li(46,47,48,49,50,51));
map.put("auxC03", li(43,44,45));
map.put("auxC01", li(58,59,60,61,62,63));
map.put("auxC02", li(43,53,54,55,56,57));
map.put("mvSingleton", li(32));
map.put("mvMPush", li(17,18,19,20,21,22)); return (map);}
@Override public HashMap<String, Locus> fieldLocus() {HashMap<String, Locus> map = new HashMap<>();
 map.put("mvForcesyyy0R",compiler.Locus.locusV());
 map.put("auxC01",compiler.Locus.locusVe());
 map.put("mvBMeeteside",compiler.Locus.locusV());
 map.put("lldefEf",compiler.Locus.locusEf());
 map.put("mvSingleton",compiler.Locus.locusV());
 map.put("auxC03",compiler.Locus.locusE());
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
 map.put("auxC02",compiler.Locus.locusVf());
 map.put("auxC00",compiler.Locus.locusV());
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
