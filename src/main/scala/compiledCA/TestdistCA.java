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

public final class TestdistCA implements CAloops2 {
 public static void _fun2(PrShift p,int [][] testdistDSloplt,int [][] defVe,int [] auxC00R){
 int[] testdistDSloplt$e=testdistDSloplt[0],testdistDSloplt$se=testdistDSloplt[1],testdistDSloplt$sw=testdistDSloplt[2],testdistDSloplt$w=testdistDSloplt[3],testdistDSloplt$nw=testdistDSloplt[4],testdistDSloplt$ne=testdistDSloplt[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(testdistDSloplt,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(testdistDSloplt);p.prepareBit(defVe)
 ;
// initialisation 
 int auxC00=0,auxL03=0,pdefVe=0;
for (int i = 1; i < testdistDSloplt$e.length -1; i++) {
 pdefVe= defVe$e[i] ;auxC00=(( pdefVe  &  testdistDSloplt$e[i] ) | ~ pdefVe );pdefVe= defVe$se[i] ;auxC00=( auxC00  | (( pdefVe  &  testdistDSloplt$se[i] ) | ~ pdefVe ));
 pdefVe= defVe$sw[i] ;auxC00=( auxC00  | (( pdefVe  &  testdistDSloplt$sw[i] ) | ~ pdefVe ));pdefVe= defVe$w[i] ;auxC00=( auxC00  | (( pdefVe  &  testdistDSloplt$w[i] ) | ~ pdefVe ));
 pdefVe= defVe$nw[i] ;auxC00=( auxC00  | (( pdefVe  &  testdistDSloplt$nw[i] ) | ~ pdefVe ));pdefVe= defVe$ne[i] ;auxC00R[i]=( auxC00  | (( pdefVe  &  testdistDSloplt$ne[i] ) | ~ pdefVe ));
   } }
 public static void _fun3(PrShift p,int [][] testdistDDelta,int [] testdist,int [][] testdistD,int [][] lltestdistD){
 int[] lltestdistD$0=lltestdistD[0],lltestdistD$1=lltestdistD[1],lltestdistD$2=lltestdistD[2],testdistDDelta$0=testdistDDelta[0],testdistDDelta$1=testdistDDelta[1],testdistD$0=testdistD[0],testdistD$1=testdistD[1],testdistD$2=testdistD[2];
p.mirror(testdistDDelta,compiler.Locus.locusV());p.mirror(testdist,compiler.Locus.locusV());p.mirror(testdistD,compiler.Locus.locusV());
p.prepareBit(testdistDDelta);p.prepareBit(testdist);p.prepareBit(testdistD)
 ;
// initialisation 
 int ptestdist=0,ptestdistD$0=0,ptestdistD$1=0,ptestdistD$2=0,r0=0,r1=0,r2=0,r3=0,r4=0,r5=0;
for (int i = 1; i < testdistDDelta$0.length -1; i++) {
 ptestdist= testdist[i] ;ptestdistD$0= testdistD$0[i] ;ptestdistD$1= testdistD$1[i] ;ptestdistD$2= testdistD$2[i] ;
 r0=~ ptestdist ;r1=(r2= ptestdistD$0 );r1=( r1  | (r2=((r3=~ ptestdistD$0 ) ^ ~ ptestdistD$1 )));r1=( r1  | (r2=(( r3  & ~ ptestdistD$1 ) ^ ~ ptestdistD$2 )));
 r4= r2 ;lltestdistD$0[i]=( ptestdistD$0  ^ (r3=(( ptestdist  &  r1 ) | ( r0  &  testdistDDelta$0[i] ))));lltestdistD$1[i]=(((r2=( r3  &  ptestdistD$0 )) ^  ptestdistD$1 ) ^ (r3=(r5=(( ptestdist  &  r4 ) | ( r0  &  testdistDDelta$1[i] )))));lltestdistD$2[i]=(((( r2  &  ptestdistD$1 ) | ( r3  & ( r2  |  ptestdistD$1 ))) ^  ptestdistD$2 ) ^  r5 );
   } }
 public static void _fun0(PrShift p,int [][] testdistDSloplt,int [][] testdistDVortexR){
 int[] testdistDVortexR$do=testdistDVortexR[0],testdistDVortexR$up=testdistDVortexR[1],testdistDSloplt$e=testdistDSloplt[0],testdistDSloplt$se=testdistDSloplt[1],testdistDSloplt$sw=testdistDSloplt[2],testdistDSloplt$w=testdistDSloplt[3],testdistDSloplt$nw=testdistDSloplt[4],testdistDSloplt$ne=testdistDSloplt[5];
p.mirror(testdistDSloplt,compiler.Locus.locusVe());
p.prepareBit(testdistDSloplt)
 ;
// initialisation 
 int auxL04=0,ptestdistDSloplt=0,shiftptestdistDSloplt=0,testdistDVortex$do=0,testdistDVortex$dotm1=0,testdistDVortex$up=0,tmun00=0;
for (int i = 1; i < testdistDSloplt$e.length -1; i++) {
 auxL04= testdistDSloplt$nw[i] ;ptestdistDSloplt= testdistDSloplt$ne[i] ;testdistDVortex$do=( testdistDVortex$dotm1  & ( ptestdistDSloplt  ^  auxL04 ));shiftptestdistDSloplt= ptestdistDSloplt ;
 ptestdistDSloplt= testdistDSloplt$e[i] ;testdistDVortex$up=(( ptestdistDSloplt  ^  shiftptestdistDSloplt ) >>>  1 );shiftptestdistDSloplt= ptestdistDSloplt ;ptestdistDSloplt= testdistDSloplt$se[i] ;
 testdistDVortex$dotm1=( ptestdistDSloplt  ^  shiftptestdistDSloplt );shiftptestdistDSloplt= ptestdistDSloplt ;ptestdistDSloplt= testdistDSloplt$sw[i] ;testdistDVortex$up=( testdistDVortex$up  &  tmun00 );
 tmun00=( ptestdistDSloplt  ^  shiftptestdistDSloplt );shiftptestdistDSloplt= ptestdistDSloplt ;ptestdistDSloplt= testdistDSloplt$w[i] ;testdistDVortex$dotm1=( testdistDVortex$dotm1  & (( ptestdistDSloplt  ^  shiftptestdistDSloplt ) <<  1 ));
 shiftptestdistDSloplt= ptestdistDSloplt ;testdistDVortexR$do[i-1]= testdistDVortex$do ;testdistDVortexR$up[i-1]=( testdistDVortex$up  & ( auxL04  ^  shiftptestdistDSloplt ));
   } }
 public static void _fun1(PrShift p,int [][] auxC01,int [][] testdistDBTwoadjblob,int [][] testdistDBMeete){
 int[] testdistDBMeete$h=testdistDBMeete[0],testdistDBMeete$d=testdistDBMeete[1],testdistDBMeete$ad=testdistDBMeete[2],auxC01$e=auxC01[0],auxC01$se=auxC01[1],auxC01$sw=auxC01[2],auxC01$w=auxC01[3],auxC01$nw=auxC01[4],auxC01$ne=auxC01[5],testdistDBTwoadjblob$h=testdistDBTwoadjblob[0],testdistDBTwoadjblob$d=testdistDBTwoadjblob[1],testdistDBTwoadjblob$ad=testdistDBTwoadjblob[2];
p.mirror(auxC01,compiler.Locus.locusVe());p.mirror(testdistDBTwoadjblob,compiler.Locus.locusE());
p.prepareBit(auxC01);p.prepareBit(testdistDBTwoadjblob)
 ;
// initialisation 
 int tmun01=0,tmun02=0,tmun03=0,tmun04=0,tmun05=0,tmun06=0;
for (int i = 1; i < auxC01$e.length -1; i++) {
 testdistDBMeete$h[i-1]=(~ tmun02  &  tmun01 );tmun02=(( auxC01$w[i]  <<  1 ) |  auxC01$e[i] );tmun01= testdistDBTwoadjblob$h[i] ;testdistDBMeete$d[i-1]=(~( tmun04  |  auxC01$nw[i] ) &  tmun03 );
 tmun04= auxC01$se[i] ;tmun03= testdistDBTwoadjblob$d[i] ;testdistDBMeete$ad[i-1]=(~( tmun06  | ( auxC01$ne[i]  >>>  1 )) &  tmun05 );tmun06= auxC01$sw[i] ;
 tmun05= testdistDBTwoadjblob$ad[i] ;
   } }
 public static void _fun4(PrShift p,int [][] testdistDBNbcc,int [] testdistDBMeetv){
 int[] testdistDBNbcc$0=testdistDBNbcc[0],testdistDBNbcc$1=testdistDBNbcc[1];
p.mirror(testdistDBNbcc,compiler.Locus.locusV());
p.prepareBit(testdistDBNbcc)
 ;
// initialisation 
 int r0=0,r1=0,r2=0,r3=0,r4=0;
for (int i = 1; i < testdistDBNbcc$0.length -1; i++) {
 r1=~ testdistDBNbcc$0[i] ;r0= testdistDBNbcc$1[i] ;r4=((r2=(r3= r0 )) &  testdistDBNbcc$1[i] );r4=( r4  | ((~ r2  & ( r3  |  r1 )) &  testdistDBNbcc$0[i] ));
 testdistDBMeetv[i]= r4 ;
   } }
public int CAmemWidth() {return 48;}

@Override public ArrayList<String> theLoops(PrShift p,int[][] m) {ArrayList<String> bugs=new ArrayList<>();
int[]auxC00=m[47],testdist=m[11],llbugV=m[0],testdistDBMeetv=m[14],lltestdist=m[10];
int[][]testdistDBNbcc= new int[][]{m[35],m[36]},defVe= new int[][]{m[40],m[39],m[38],m[37],m[36],m[35]},testdistD= new int[][]{m[32],m[33],m[34]},testdistDVortex= new int[][]{m[12],m[13]},lldefVe= new int[][]{m[1],m[2],m[3],m[4],m[5],m[6]},lltestdistD= new int[][]{m[7],m[8],m[9]},auxC01= new int[][]{m[41],m[42],m[43],m[44],m[45],m[46]},auxC02= new int[][]{m[35],m[36],m[37],m[38],m[39],m[40]},testdistDBTwoadjblob= new int[][]{m[35],m[36],m[37]},testdistDGap= new int[][]{m[27],m[28],m[29]},testdistDLevel= new int[][]{m[24],m[25],m[26]},testdistDSloplt= new int[][]{m[18],m[19],m[20],m[21],m[22],m[23]},testdistDDelta= new int[][]{m[30],m[31]},testdistDBMeete= new int[][]{m[15],m[16],m[17]};

copy(lltestdist,testdist);
show(testdist);
copy(lltestdistD,testdistD);
show(testdistD);
grad.slopDelta_3_1_2_1_1(p,testdistD,testdistDSloplt,testdistDDelta,testdistDLevel,testdistDGap,lldefVe);// 191 gate
redT.enlargeEF_1_1(p,testdistDSloplt,auxC02);// 6 gate
redT.enlargeFE_1_1(p,auxC02,auxC01);// 6 gate
copy(lldefVe,defVe);
_fun2(p,testdistDSloplt,defVe,auxC00);// 23 gate
redsandb.ve_1_1(p,auxC00,testdistDBTwoadjblob);// 3 gate
_fun1(p,auxC01,testdistDBTwoadjblob,testdistDBMeete);// 9 gate
show(testdistDBMeete);
topo.nbcc_1_2(p,testdistDSloplt,testdistDBNbcc);// 21 gate
_fun4(p,testdistDBNbcc,testdistDBMeetv);// 7 gate
show(testdistDBMeetv);
show(testdistDDelta);
show(testdistDGap);
show(testdistDLevel);
show(testdistDSloplt);
_fun0(p,testdistDSloplt,testdistDVortex);// 10 gate
show(testdistDVortex);
_fun3(p,testdistDDelta,testdist,testdistD,lltestdistD);// 26 gate
 return bugs;}



@Override public HashMap<String, List<Integer>> fieldOffset() {HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
map.put("testdistDBNbcc", li(35,36));
map.put("testdistD", li(32,33,34));
map.put("testdistDVortex", li(12,13));
map.put("llbugV", li(0));
map.put("lldefVe", li(1,2,3,4,5,6));
map.put("lltestdistD", li(7,8,9));
map.put("auxC01", li(41,42,43,44,45,46));
map.put("testdistDBMeetv", li(14));
map.put("auxC02", li(35,36,37,38,39,40));
map.put("testdistDBTwoadjblob", li(35,36,37));
map.put("auxC00", li(47));
map.put("testdist", li(11));
map.put("testdistDGap", li(27,28,29));
map.put("testdistDLevel", li(24,25,26));
map.put("testdistDSloplt", li(18,19,20,21,22,23));
map.put("testdistDDelta", li(30,31));
map.put("testdistDBMeete", li(15,16,17));
map.put("lltestdist", li(10)); return (map);}
@Override public HashMap<String, Locus> fieldLocus() {HashMap<String, Locus> map = new HashMap<>();
 map.put("testdistDGap",compiler.Locus.locusE());
 map.put("testdistDDelta",compiler.Locus.locusV());
 map.put("lltestdist",compiler.Locus.locusV());
 map.put("lldefVe",compiler.Locus.locusVe());
 map.put("lltestdistD",compiler.Locus.locusV());
 map.put("testdistDBMeetv",compiler.Locus.locusV());
 map.put("testdist",compiler.Locus.locusV());
 map.put("testdistD",compiler.Locus.locusV());
 map.put("testdistDLevel",compiler.Locus.locusE());
 map.put("testdistDBNbcc",compiler.Locus.locusV());
 map.put("testdistDSloplt",compiler.Locus.locusVe());
 map.put("llbugV",compiler.Locus.locusV());
 map.put("defVe",compiler.Locus.locusVe());
 map.put("auxC01",compiler.Locus.locusVe());
 map.put("testdistDBTwoadjblob",compiler.Locus.locusE());
 map.put("auxC02",compiler.Locus.locusVf());
 map.put("auxC00",compiler.Locus.locusV());
 map.put("testdistDBMeete",compiler.Locus.locusE());
 map.put("testdistDVortex",compiler.Locus.locusF()); return (map);}
@Override public HashMap<String, Integer> fieldBitSize() { HashMap<String, Integer> map = new HashMap<>();
 map.put("testdistDDelta",2);
 map.put("lltestdistD",3);
 map.put("testdistD",3);
 map.put("testdistDBNbcc",2); return (map); }
@Override  public String displayableLayerHierarchy() { return "testdist(testdistD(testdistDGap)(testdistDDelta)(testdistDLevel)(testdistDVortex)(testdistDB(testdistDBMeetv)(testdistDBMeete))(testdistDSloplt)).";}
@Override public HashMap<String, String> init() {HashMap<String, String> map = new HashMap<>();
  map.put("lltestdist","global");
 map.put("lldefVe","def");
 map.put("lltestdistD","0");
 map.put("llbugV","false");
 return (map);}
@Override public int gateCount(){return (302 );}

}
