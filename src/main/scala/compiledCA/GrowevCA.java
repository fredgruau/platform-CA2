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

public final class GrowevCA implements CAloops2 {
 public static void _fun0(PrShift p, int[][] growevTransfered, int[] growevNvR, int[][] lldefVe) {
  int[] lldefVe$e = lldefVe[0], lldefVe$se = lldefVe[1], lldefVe$sw = lldefVe[2], lldefVe$w = lldefVe[3], lldefVe$nw = lldefVe[4], lldefVe$ne = lldefVe[5], growevTransfered$e = growevTransfered[0], growevTransfered$se = growevTransfered[1], growevTransfered$sw = growevTransfered[2], growevTransfered$w = growevTransfered[3], growevTransfered$nw = growevTransfered[4], growevTransfered$ne = growevTransfered[5];
  p.propagate4shift(growevTransfered$e);
  p.propagate4shift(growevTransfered$se);
  p.propagate4shift(growevTransfered$sw);
  p.propagate4shift(growevTransfered$w);
  p.propagate4shift(growevTransfered$nw);
  p.propagate4shift(growevTransfered$ne);

  for (int i = 1; i < growevTransfered$e.length - 1; i++) {
   growevNvR[i] = (((((lldefVe$e[i] & growevTransfered$e[i]) | lldefVe$se[i] & growevTransfered$se[i]) | lldefVe$sw[i] & growevTransfered$sw[i]) | lldefVe$w[i] & growevTransfered$w[i]) | lldefVe$nw[i] & growevTransfered$nw[i]) | lldefVe$ne[i] & growevTransfered$ne[i];
  }
 }

 public static void _fun1(PrShift p, int[][] growevBroadcasted, int[][] growevTransfered) {
  int[] growevTransfered$e = growevTransfered[0], growevTransfered$se = growevTransfered[1], growevTransfered$sw = growevTransfered[2], growevTransfered$w = growevTransfered[3], growevTransfered$nw = growevTransfered[4], growevTransfered$ne = growevTransfered[5], growevBroadcasted$h1 = growevBroadcasted[0], growevBroadcasted$h2 = growevBroadcasted[1], growevBroadcasted$d1 = growevBroadcasted[2], growevBroadcasted$d2 = growevBroadcasted[3], growevBroadcasted$ad1 = growevBroadcasted[4], growevBroadcasted$ad2 = growevBroadcasted[5];
  p.propagate4shift(growevBroadcasted$h1);
  p.propagate4shift(growevBroadcasted$h2);
  p.propagate4shift(growevBroadcasted$d1);
  p.propagate4shift(growevBroadcasted$d2);
  p.propagate4shift(growevBroadcasted$ad1);
  p.propagate4shift(growevBroadcasted$ad2);

  for (int i = 1; i < growevBroadcasted$h1.length - 1; i++) {
   growevTransfered$e[i] = growevBroadcasted$h1[i];
   growevTransfered$se[i] = growevBroadcasted$d1[i];
   growevTransfered$sw[i] = growevBroadcasted$ad1[i];
   growevTransfered$w[i] = growevBroadcasted$h2[i] >>> 1;
   growevTransfered$nw[i + 1] = growevBroadcasted$d2[i];
   growevTransfered$ne[i + 1] = growevBroadcasted$ad2[i] << 1;
  }
 }

 public int CAmemWidth() {
  return 29;
 }

 @Override
 public ArrayList<String> theLoops(PrShift p, int[][] m) {
  ArrayList<String> bugs = new ArrayList<>();
  int[] llbugV = m[0], growevNv = m[25];
  int[][] growev = new int[][]{m[10], m[11], m[12]}, llgrowev = new int[][]{m[1], m[2], m[3]}, lldefVe = new int[][]{m[4], m[5], m[6], m[7], m[8], m[9]}, growevTransfered = new int[][]{m[24], m[19], m[20], m[23], m[22], m[21]}, growevNext = new int[][]{m[26], m[27], m[28]}, growevBroadcasted = new int[][]{m[18], m[17], m[16], m[15], m[14], m[13]};

  copy(llgrowev, growev);
  copy(growev, growevBroadcasted);
  _fun1(p, growevBroadcasted, growevTransfered);
  _fun0(p, growevTransfered, growevNv, lldefVe);
  reds.orbve_1(p, growevNv, growevNext);
  show(growevNext);
  memo(growevNext, llgrowev);
  show(growevBroadcasted);
  show(growev);
  show(growevTransfered);
  show(growevNv);
  return bugs;
 }

 @Override
 public void copyLayer(int[][] m) {
  int[][] growev = new int[][]{m[10], m[11], m[12]}, llgrowev = new int[][]{m[1], m[2], m[3]};
  copy(llgrowev, growev);
 }


 @Override
 public HashMap<String, List<Integer>> fieldOffset() {
  HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
  map.put("growev", li(10, 11, 12));
  map.put("llbugV", li(0));
  map.put("llgrowev", li(1, 2, 3));
  map.put("lldefVe", li(4, 5, 6, 7, 8, 9));
  map.put("growevNv", li(25));
  map.put("growevTransfered", li(24, 19, 20, 23, 22, 21));
  map.put("growevNext", li(26, 27, 28));
  map.put("growevBroadcasted", li(18, 17, 16, 15, 14, 13));
  return (map);
 }

 @Override
 public HashMap<String, Locus> fieldLocus() {
  HashMap<String, Locus> map = new HashMap<>();
  map.put("llgrowev", Locus.locusE());
  map.put("lldefVe", Locus.locusVe());
  map.put("growevNv", Locus.locusV());
  map.put("growevNext", Locus.locusE());
  map.put("growev", Locus.locusE());
  map.put("growevBroadcasted", Locus.locusEv());
  map.put("growevTransfered", Locus.locusVe());
  map.put("llbugV", Locus.locusV());
  return (map);
 }

 @Override
 public HashMap<String, Integer> fieldBitSize() {
  HashMap<String, Integer> map = new HashMap<>();
  ;
  return (map);
 }

 @Override
 public String displayableLayerHierarchy() {
  return "growev(growevNv)(growevTransfered)(growevNext)(growevBroadcasted).";
 }

 @Override
 public HashMap<String, String> init() {
  HashMap<String, String> map = new HashMap<>();
  map.put("llgrowev", "global");
  map.put("lldefVe", "def");
  map.put("llbugV", "false");
  return (map);
 }

}
