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

public final class     TestvoronoiCA implements CAloops2 {
 public static void _fun2(PrShift p,int [][] testvoronoiEv,int [][] testvoronoiER){
 int[] testvoronoiER$h=testvoronoiER[0],testvoronoiER$d=testvoronoiER[1],testvoronoiER$ad=testvoronoiER[2],testvoronoiEv$h1=testvoronoiEv[0],testvoronoiEv$h2=testvoronoiEv[1],testvoronoiEv$d1=testvoronoiEv[2],testvoronoiEv$d2=testvoronoiEv[3],testvoronoiEv$ad1=testvoronoiEv[4],testvoronoiEv$ad2=testvoronoiEv[5];
p.mirror(testvoronoiEv,compiler.Locus.locusEv());
p.prepareBit(testvoronoiEv)
 ;

for (int i = 1; i < testvoronoiEv$h1.length -1; i++) {
 testvoronoiER$h[i]=( testvoronoiEv$h1[i]  |  testvoronoiEv$h2[i] );testvoronoiER$d[i]=( testvoronoiEv$d1[i]  |  testvoronoiEv$d2[i] );testvoronoiER$ad[i]=( testvoronoiEv$ad1[i]  |  testvoronoiEv$ad2[i] );
   } }
 public static void _fun3(PrShift p,int [][] testvoronoiFv,int [][] testvoronoiFR){
 int[] testvoronoiFR$do=testvoronoiFR[0],testvoronoiFR$up=testvoronoiFR[1],testvoronoiFv$dop=testvoronoiFv[0],testvoronoiFv$dob1=testvoronoiFv[1],testvoronoiFv$dob2=testvoronoiFv[2],testvoronoiFv$upp=testvoronoiFv[3],testvoronoiFv$upb1=testvoronoiFv[4],testvoronoiFv$upb2=testvoronoiFv[5];
p.mirror(testvoronoiFv,compiler.Locus.locusFv());
p.prepareBit(testvoronoiFv)
 ;

for (int i = 1; i < testvoronoiFv$dop.length -1; i++) {
 testvoronoiFR$do[i]=(( testvoronoiFv$dop[i]  |  testvoronoiFv$dob1[i] ) |  testvoronoiFv$dob2[i] );testvoronoiFR$up[i]=(( testvoronoiFv$upp[i]  |  testvoronoiFv$upb1[i] ) |  testvoronoiFv$upb2[i] );
   } }
 public static void _fun0(PrShift p,int [][] testvoronoi,int [][] testvoronoiEv){
 int[] testvoronoiEv$h1=testvoronoiEv[0],testvoronoiEv$h2=testvoronoiEv[1],testvoronoiEv$d1=testvoronoiEv[2],testvoronoiEv$d2=testvoronoiEv[3],testvoronoiEv$ad1=testvoronoiEv[4],testvoronoiEv$ad2=testvoronoiEv[5],testvoronoi$e=testvoronoi[0],testvoronoi$se=testvoronoi[1],testvoronoi$sw=testvoronoi[2],testvoronoi$w=testvoronoi[3],testvoronoi$nw=testvoronoi[4],testvoronoi$ne=testvoronoi[5];
p.mirror(testvoronoi,compiler.Locus.locusVe());
p.prepareBit(testvoronoi)
 ;

for (int i = 1; i < testvoronoi$e.length -1; i++) {
 testvoronoiEv$h1[i]= testvoronoi$e[i] ;testvoronoiEv$h2[i]=( testvoronoi$w[i]  <<  1 );testvoronoiEv$d1[i]= testvoronoi$se[i] ;testvoronoiEv$d2[i-1]= testvoronoi$nw[i] ;
 testvoronoiEv$ad1[i]= testvoronoi$sw[i] ;testvoronoiEv$ad2[i-1]=( testvoronoi$ne[i]  >>>  1 );
   } }
 public static void _fun1(PrShift p,int [][] testvoronoiEf,int [][] testvoronoiFe){
 int[] testvoronoiFe$dob=testvoronoiFe[0],testvoronoiFe$dos1=testvoronoiFe[1],testvoronoiFe$dos2=testvoronoiFe[2],testvoronoiFe$upb=testvoronoiFe[3],testvoronoiFe$ups1=testvoronoiFe[4],testvoronoiFe$ups2=testvoronoiFe[5],testvoronoiEf$h1=testvoronoiEf[0],testvoronoiEf$h2=testvoronoiEf[1],testvoronoiEf$d1=testvoronoiEf[2],testvoronoiEf$d2=testvoronoiEf[3],testvoronoiEf$ad1=testvoronoiEf[4],testvoronoiEf$ad2=testvoronoiEf[5];
p.mirror(testvoronoiEf,compiler.Locus.locusEf());
p.prepareBit(testvoronoiEf)
 ;

for (int i = 1; i < testvoronoiEf$h1.length -1; i++) {
 testvoronoiFe$dob[i]= testvoronoiEf$h2[i] ;testvoronoiFe$dos1[i]=( testvoronoiEf$ad2[i]  <<  1 );testvoronoiFe$dos2[i]= testvoronoiEf$d1[i] ;testvoronoiFe$upb[i-1]=( testvoronoiEf$h1[i]  >>>  1 );
 testvoronoiFe$ups1[i]= testvoronoiEf$ad1[i] ;testvoronoiFe$ups2[i]= testvoronoiEf$d2[i] ;
   } }
 public static void _fun6(PrShift p,int [][] testvoronoi,int [][] defVe,int [] testvoronoiVR){
 int[] testvoronoi$e=testvoronoi[0],testvoronoi$se=testvoronoi[1],testvoronoi$sw=testvoronoi[2],testvoronoi$w=testvoronoi[3],testvoronoi$nw=testvoronoi[4],testvoronoi$ne=testvoronoi[5],defVe$e=defVe[0],defVe$se=defVe[1],defVe$sw=defVe[2],defVe$w=defVe[3],defVe$nw=defVe[4],defVe$ne=defVe[5];
p.mirror(testvoronoi,compiler.Locus.locusVe());p.mirror(defVe,compiler.Locus.locusVe());
p.prepareBit(testvoronoi);p.prepareBit(defVe)
 ;
// initialisation 
 int auxL00=0,pdefVe=0,testvoronoiV=0;
for (int i = 1; i < testvoronoi$e.length -1; i++) {
 pdefVe= defVe$e[i] ;testvoronoiV=( pdefVe  &  testvoronoi$e[i] );pdefVe= defVe$se[i] ;testvoronoiV=( testvoronoiV  | ( pdefVe  &  testvoronoi$se[i] ));
 pdefVe= defVe$sw[i] ;testvoronoiV=( testvoronoiV  | ( pdefVe  &  testvoronoi$sw[i] ));pdefVe= defVe$w[i] ;testvoronoiV=( testvoronoiV  | ( pdefVe  &  testvoronoi$w[i] ));
 pdefVe= defVe$nw[i] ;testvoronoiV=( testvoronoiV  | ( pdefVe  &  testvoronoi$nw[i] ));pdefVe= defVe$ne[i] ;testvoronoiVR[i]=( testvoronoiV  | ( pdefVe  &  testvoronoi$ne[i] ));
   } }
 public static void _fun7(PrShift p,int [][] testvoronoi,int [][] testvoronoiVf){
 int[] testvoronoiVf$es=testvoronoiVf[0],testvoronoiVf$s=testvoronoiVf[1],testvoronoiVf$ws=testvoronoiVf[2],testvoronoiVf$wn=testvoronoiVf[3],testvoronoiVf$n=testvoronoiVf[4],testvoronoiVf$en=testvoronoiVf[5],testvoronoi$e=testvoronoi[0],testvoronoi$se=testvoronoi[1],testvoronoi$sw=testvoronoi[2],testvoronoi$w=testvoronoi[3],testvoronoi$nw=testvoronoi[4],testvoronoi$ne=testvoronoi[5];
p.mirror(testvoronoi,compiler.Locus.locusVe());
p.prepareBit(testvoronoi)
 ;

for (int i = 1; i < testvoronoi$e.length -1; i++) {
 testvoronoiVf$es[i]= testvoronoi$se[i] ;testvoronoiVf$s[i]= testvoronoi$sw[i] ;testvoronoiVf$ws[i]= testvoronoi$w[i] ;testvoronoiVf$wn[i]= testvoronoi$nw[i] ;
 testvoronoiVf$n[i]= testvoronoi$ne[i] ;testvoronoiVf$en[i]= testvoronoi$e[i] ;
   } }
 public static void _fun4(PrShift p,int [][] testvoronoiEv,int [][] testvoronoiEf){
 int[] testvoronoiEf$h1=testvoronoiEf[0],testvoronoiEf$h2=testvoronoiEf[1],testvoronoiEf$d1=testvoronoiEf[2],testvoronoiEf$d2=testvoronoiEf[3],testvoronoiEf$ad1=testvoronoiEf[4],testvoronoiEf$ad2=testvoronoiEf[5],testvoronoiEv$h1=testvoronoiEv[0],testvoronoiEv$h2=testvoronoiEv[1],testvoronoiEv$d1=testvoronoiEv[2],testvoronoiEv$d2=testvoronoiEv[3],testvoronoiEv$ad1=testvoronoiEv[4],testvoronoiEv$ad2=testvoronoiEv[5];
p.mirror(testvoronoiEv,compiler.Locus.locusEv());
p.prepareBit(testvoronoiEv)
 ;

for (int i = 1; i < testvoronoiEv$h1.length -1; i++) {
 testvoronoiEf$h1[i]= testvoronoiEv$h1[i] ;testvoronoiEf$h2[i]= testvoronoiEv$h2[i] ;testvoronoiEf$d1[i]= testvoronoiEv$d1[i] ;testvoronoiEf$d2[i]= testvoronoiEv$d2[i] ;
 testvoronoiEf$ad1[i]= testvoronoiEv$ad1[i] ;testvoronoiEf$ad2[i]= testvoronoiEv$ad2[i] ;
   } }
 public static void _fun5(PrShift p,int [][] testvoronoiVf,int [][] testvoronoiFv){
 int[] testvoronoiFv$dop=testvoronoiFv[0],testvoronoiFv$dob1=testvoronoiFv[1],testvoronoiFv$dob2=testvoronoiFv[2],testvoronoiFv$upp=testvoronoiFv[3],testvoronoiFv$upb1=testvoronoiFv[4],testvoronoiFv$upb2=testvoronoiFv[5],testvoronoiVf$es=testvoronoiVf[0],testvoronoiVf$s=testvoronoiVf[1],testvoronoiVf$ws=testvoronoiVf[2],testvoronoiVf$wn=testvoronoiVf[3],testvoronoiVf$n=testvoronoiVf[4],testvoronoiVf$en=testvoronoiVf[5];
p.mirror(testvoronoiVf,compiler.Locus.locusVf());
p.prepareBit(testvoronoiVf)
 ;

for (int i = 1; i < testvoronoiVf$es.length -1; i++) {
 testvoronoiFv$dop[i-1]= testvoronoiVf$n[i] ;testvoronoiFv$dob1[i]=( testvoronoiVf$ws[i]  <<  1 );testvoronoiFv$dob2[i]= testvoronoiVf$es[i] ;testvoronoiFv$upp[i]= testvoronoiVf$s[i] ;
 testvoronoiFv$upb1[i-1]=( testvoronoiVf$en[i]  >>>  1 );testvoronoiFv$upb2[i-1]= testvoronoiVf$wn[i] ;
   } }
public int CAmemWidth() {return 61;}

@Override public ArrayList<String> theLoops(PrShift p,int[][] m) {ArrayList<String> bugs=new ArrayList<>();
int[]testvoronoiV=m[19],llbugV=m[0];
int[][]testvoronoi= new int[][]{m[13],m[14],m[15],m[16],m[17],m[18]},defVe= new int[][]{m[60],m[59],m[58],m[57],m[56],m[55]},testvoronoiE= new int[][]{m[20],m[21],m[22]},testvoronoiF= new int[][]{m[29],m[30]},testvoronoiFe= new int[][]{m[23],m[24],m[25],m[26],m[27],m[28]},testvoronoiFv= new int[][]{m[31],m[32],m[33],m[34],m[35],m[36]},testvoronoiVf= new int[][]{m[37],m[38],m[39],m[40],m[41],m[42]},lldefVe= new int[][]{m[1],m[2],m[3],m[4],m[5],m[6]},testvoronoiEv= new int[][]{m[49],m[50],m[51],m[52],m[53],m[54]},testvoronoiEf= new int[][]{m[43],m[44],m[45],m[46],m[47],m[48]},lltestvoronoi= new int[][]{m[7],m[8],m[9],m[10],m[11],m[12]};

copy(lltestvoronoi,testvoronoi);
_fun0(p,testvoronoi,testvoronoiEv);
_fun4(p,testvoronoiEv,testvoronoiEf);
show(testvoronoiEf);
show(testvoronoiEv);
show(testvoronoi);
_fun7(p,testvoronoi,testvoronoiVf);
_fun5(p,testvoronoiVf,testvoronoiFv);
_fun3(p,testvoronoiFv,testvoronoiF);
show(testvoronoiF);
_fun1(p,testvoronoiEf,testvoronoiFe);
show(testvoronoiFe);
show(testvoronoiVf);
memo(testvoronoi,lltestvoronoi);
show(testvoronoiFv);
_fun2(p,testvoronoiEv,testvoronoiE);
show(testvoronoiE);
copy(lldefVe,defVe);
_fun6(p,testvoronoi,defVe,testvoronoiV);
show(testvoronoiV); return bugs;}



@Override public HashMap<String, List<Integer>> fieldOffset() {HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
map.put("testvoronoi", li(13,14,15,16,17,18));
map.put("testvoronoiV", li(19));
map.put("testvoronoiFe", li(23,24,25,26,27,28));
map.put("testvoronoiFv", li(31,32,33,34,35,36));
map.put("testvoronoiVf", li(37,38,39,40,41,42));
map.put("llbugV", li(0));
map.put("lldefVe", li(1,2,3,4,5,6));
map.put("testvoronoiEv", li(49,50,51,52,53,54));
map.put("testvoronoiE", li(20,21,22));
map.put("testvoronoiF", li(29,30));
map.put("testvoronoiEf", li(43,44,45,46,47,48));
map.put("lltestvoronoi", li(7,8,9,10,11,12)); return (map);}
@Override public HashMap<String, Locus> fieldLocus() {HashMap<String, Locus> map = new HashMap<>();
 map.put("lldefVe",compiler.Locus.locusVe());
 map.put("testvoronoiF",compiler.Locus.locusF());
 map.put("testvoronoiFe",compiler.Locus.locusFe());
 map.put("testvoronoiVf",compiler.Locus.locusVf());
 map.put("llbugV",compiler.Locus.locusV());
 map.put("testvoronoiEf",compiler.Locus.locusEf());
 map.put("testvoronoiV",compiler.Locus.locusV());
 map.put("testvoronoiFv",compiler.Locus.locusFv());
 map.put("testvoronoi",compiler.Locus.locusVe());
 map.put("lltestvoronoi",compiler.Locus.locusVe());
 map.put("testvoronoiEv",compiler.Locus.locusEv());
 map.put("testvoronoiE",compiler.Locus.locusE());
 map.put("defVe",compiler.Locus.locusVe()); return (map);}
@Override public HashMap<String, Integer> fieldBitSize() { HashMap<String, Integer> map = new HashMap<>();
; return (map); }
@Override  public String displayableLayerHierarchy() { return "testvoronoi(testvoronoiF)(testvoronoiFe)(testvoronoiFv)(testvoronoiEv)(testvoronoiVf)(testvoronoiEf)(testvoronoiE)(testvoronoiV).";}
@Override public HashMap<String, String> init() {HashMap<String, String> map = new HashMap<>();
  map.put("lldefVe","def");
 map.put("lltestvoronoi","global");
 map.put("llbugV","false");
 return (map);}
@Override public int gateCount(){return (18 );}

}
