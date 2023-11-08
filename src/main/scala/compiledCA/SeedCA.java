package compiledCA;

import compiledMacro.integer;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static simulator.Util.*;

public final class SeedCA implements CAloops2 {
 public static void _fun0(PrShift p, int[] seed, int[][] seedDistDelta, int[][] seedDist, int[][] llseedDist) {
  int[] llseedDist$0 = llseedDist[0], llseedDist$1 = llseedDist[1], llseedDist$2 = llseedDist[2], seedDistDelta$0 = seedDistDelta[0], seedDistDelta$1 = seedDistDelta[1], seedDist$0 = seedDist[0], seedDist$1 = seedDist[1], seedDist$2 = seedDist[2];
  p.propagate4shift(seed);
  p.propagate4shift(seedDistDelta$0);
  p.propagate4shift(seedDistDelta$1);
  p.propagate4shift(seedDist$0);
  p.propagate4shift(seedDist$1);
  p.propagate4shift(seedDist$2);
// initialisation 
  int pseed = 0, pseedDist$0 = 0, pseedDist$1 = 0, pseedDist$2 = 0, r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
  for (int i = 1; i < seed.length - 1; i++) {
   pseedDist$0 = seedDist$0[i];
   pseedDist$1 = seedDist$1[i];
   pseedDist$2 = seedDist$2[i];
   pseed = seed[i];
   r3 = pseedDist$0;
   r2 = r3;
   r3 = ((r1 = ~pseedDist$0) ^ ~pseedDist$1);
   r2 = (r2 | r3);
   r0 = (r3 = ((r1 & ~pseedDist$1) ^ ~pseedDist$2));
   r2 = (r2 | r3);
   r1 = ~pseed;
   llseedDist$0[i] = (pseedDist$0 ^ (r3 = ((pseed & r2) | (r1 & seedDistDelta$0[i]))));
   llseedDist$1[i] = (((r5 = (r3 & pseedDist$0)) ^ pseedDist$1) ^ (r3 = (r4 = ((pseed & r0) | (r1 & seedDistDelta$1[i])))));
   llseedDist$2[i] = ((((r5 & pseedDist$1) | (r3 & (r5 | pseedDist$1))) ^ pseedDist$2) ^ r4);
  }
 }

 public int CAmemWidth() {
  return 27;
 }

 @Override
 public ArrayList<String> theLoops(PrShift p, int[][] m) {
  ArrayList<String> bugs = new ArrayList<>();
  int[] llseed = m[0], seed = m[11], llbugV = m[4], seedDistTopoligne = m[26];
  int[][] seedDist = new int[][]{m[14], m[13], m[12]}, seedDistSlop = new int[][]{m[15], m[16], m[17], m[18], m[19], m[20]}, seedDistDelta = new int[][]{m[21], m[22]}, llseedDist = new int[][]{m[1], m[2], m[3]}, lldefVe = new int[][]{m[5], m[6], m[7], m[8], m[9], m[10]}, seedDistLevel = new int[][]{m[23], m[24], m[25]};

  copy(llseedDist, seedDist);
  integer.slopDelta_3(p, seedDist, seedDistSlop, seedDistDelta, seedDistLevel, lldefVe);
  show(seedDistLevel);
  show(seedDist);
  copy(llseed, seed);
  show(seed);
  show(seedDistDelta);
  show(seedDistSlop);
  _fun0(p, seed, seedDistDelta, seedDist, llseedDist);
  copy(seedDist[2], seedDistTopoligne);
  show(seedDistTopoligne);
  return bugs;
 }

 @Override
 public void copyLayer(int[][] m) {
  int[] llseed = m[0], seed = m[11];
  int[][] seedDist = new int[][]{m[14], m[13], m[12]}, llseedDist = new int[][]{m[1], m[2], m[3]};
  copy(llseedDist, seedDist);
  copy(llseed, seed);
 }


 @Override
 public HashMap<String, List<Integer>> fieldOffset() {
  HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
  map.put("seedDist", li(14, 13, 12));
  map.put("llseed", li(0));
  map.put("seedDistSlop", li(15, 16, 17, 18, 19, 20));
  map.put("seedDistDelta", li(21, 22));
  map.put("seed", li(11));
  map.put("llseedDist", li(1, 2, 3));
  map.put("llbugV", li(4));
  map.put("lldefVe", li(5, 6, 7, 8, 9, 10));
  map.put("seedDistTopoligne", li(26));
  map.put("seedDistLevel", li(23, 24, 25));
  return (map);
 }

 @Override
 public HashMap<String, Locus> fieldLocus() {
  HashMap<String, Locus> map = new HashMap<>();
  map.put("llseedDist", Locus.locusV());
  map.put("lldefVe", Locus.locusVe());
  map.put("seed", Locus.locusV());
  map.put("llseed", Locus.locusV());
  map.put("seedDistTopoligne", Locus.locusV());
  map.put("seedDistDelta", Locus.locusV());
  map.put("seedDistSlop", Locus.locusVe());
  map.put("seedDistLevel", Locus.locusE());
  map.put("llbugV", Locus.locusV());
  map.put("seedDist", Locus.locusV());
  return (map);
 }

 @Override
 public HashMap<String, Integer> fieldBitSize() {
  HashMap<String, Integer> map = new HashMap<>();
  map.put("llseedDist", 3);
  map.put("seedDistDelta", 2);
  map.put("seedDist", 3);
  return (map);
 }

 @Override
 public String displayableLayerHierarchy() {
  return "seed(seedDist(seedDistTopoligne)(seedDistDelta)(seedDistSlop)(seedDistLevel)).";
 }

 @Override
 public HashMap<String, String> init() {
  HashMap<String, String> map = new HashMap<>();
  map.put("llseedDist", "0");
  map.put("lldefVe", "def");
  map.put("llseed", "global");
  map.put("llbugV", "false");
  return (map);
 }

 @Override
 public int gateCount() {
  return (187);
 }

}
