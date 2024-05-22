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

public final class SeedCA implements CAloops2 {
    public static void _fun2(PrShift p, int[][] seedDistBNbcc, int[] seedDistBMeetv) {
        int[] seedDistBNbcc$0 = seedDistBNbcc[0], seedDistBNbcc$1 = seedDistBNbcc[1];
        p.mirror(seedDistBNbcc, compiler.Locus.locusV());
        p.prepareBit(seedDistBNbcc)
        ;
// initialisation 
        int r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0;
        for (int i = 1; i < seedDistBNbcc$0.length - 1; i++) {
            r1 = ~seedDistBNbcc$0[i];
            r0 = seedDistBNbcc$1[i];
            r3 = ((r4 = (r2 = r0)) & seedDistBNbcc$1[i]);
            r3 = (r3 | ((~r4 & (r2 | r1)) & seedDistBNbcc$0[i]));
            seedDistBMeetv[i] = r3;
        }
    }

    public static void _fun3(PrShift p, int[][] auxC01, int[][] seedDistBTwoadjblob, int[][] seedDistBMeete) {
        int[] seedDistBMeete$h = seedDistBMeete[0], seedDistBMeete$d = seedDistBMeete[1], seedDistBMeete$ad = seedDistBMeete[2], auxC01$e = auxC01[0], auxC01$se = auxC01[1], auxC01$sw = auxC01[2], auxC01$w = auxC01[3], auxC01$nw = auxC01[4], auxC01$ne = auxC01[5], seedDistBTwoadjblob$h = seedDistBTwoadjblob[0], seedDistBTwoadjblob$d = seedDistBTwoadjblob[1], seedDistBTwoadjblob$ad = seedDistBTwoadjblob[2];
        p.mirror(auxC01, compiler.Locus.locusVe());
        p.mirror(seedDistBTwoadjblob, compiler.Locus.locusE());
        p.prepareBit(auxC01);
        p.prepareBit(seedDistBTwoadjblob)
        ;
// initialisation 
        int tmun16 = 0, tmun17 = 0, tmun18 = 0, tmun19 = 0, tmun20 = 0, tmun21 = 0;
        for (int i = 1; i < auxC01$e.length - 1; i++) {
            seedDistBMeete$h[i - 1] = (~tmun17 & tmun16);
            tmun16 = seedDistBTwoadjblob$h[i];
            tmun17 = ((auxC01$w[i] << 1) | auxC01$e[i]);
            seedDistBMeete$d[i - 1] = (~(tmun19 | auxC01$nw[i]) & tmun18);
            tmun19 = auxC01$se[i];
            tmun18 = seedDistBTwoadjblob$d[i];
            seedDistBMeete$ad[i - 1] = (~(tmun21 | (auxC01$ne[i] >>> 1)) & tmun20);
            tmun21 = auxC01$sw[i];
            tmun20 = seedDistBTwoadjblob$ad[i];
        }
    }

    public static void _fun0(PrShift p, int[][] seedDistSloplt, int[][] defVe, int[] auxC00R) {
        int[] seedDistSloplt$e = seedDistSloplt[0], seedDistSloplt$se = seedDistSloplt[1], seedDistSloplt$sw = seedDistSloplt[2], seedDistSloplt$w = seedDistSloplt[3], seedDistSloplt$nw = seedDistSloplt[4], seedDistSloplt$ne = seedDistSloplt[5], defVe$e = defVe[0], defVe$se = defVe[1], defVe$sw = defVe[2], defVe$w = defVe[3], defVe$nw = defVe[4], defVe$ne = defVe[5];
        p.mirror(seedDistSloplt, compiler.Locus.locusVe());
        p.mirror(defVe, compiler.Locus.locusVe());
        p.prepareBit(seedDistSloplt);
        p.prepareBit(defVe)
        ;
// initialisation 
        int auxC00 = 0, auxL29 = 0, pdefVe = 0;
        for (int i = 1; i < seedDistSloplt$e.length - 1; i++) {
            pdefVe = defVe$e[i];
            auxC00 = ((pdefVe & seedDistSloplt$e[i]) | ~pdefVe);
            pdefVe = defVe$se[i];
            auxC00 = (auxC00 | ((pdefVe & seedDistSloplt$se[i]) | ~pdefVe));
            pdefVe = defVe$sw[i];
            auxC00 = (auxC00 | ((pdefVe & seedDistSloplt$sw[i]) | ~pdefVe));
            pdefVe = defVe$w[i];
            auxC00 = (auxC00 | ((pdefVe & seedDistSloplt$w[i]) | ~pdefVe));
            pdefVe = defVe$nw[i];
            auxC00 = (auxC00 | ((pdefVe & seedDistSloplt$nw[i]) | ~pdefVe));
            pdefVe = defVe$ne[i];
            auxC00R[i] = (auxC00 | ((pdefVe & seedDistSloplt$ne[i]) | ~pdefVe));
        }
    }

    public static void _fun1(PrShift p, int[] seed, int[][] seedDistDelta, int[][] seedDist, int[][] llseedDist) {
        int[] llseedDist$0 = llseedDist[0], llseedDist$1 = llseedDist[1], llseedDist$2 = llseedDist[2], seedDistDelta$0 = seedDistDelta[0], seedDistDelta$1 = seedDistDelta[1], seedDist$0 = seedDist[0], seedDist$1 = seedDist[1], seedDist$2 = seedDist[2];
        p.mirror(seed, compiler.Locus.locusV());
        p.mirror(seedDistDelta, compiler.Locus.locusV());
        p.mirror(seedDist, compiler.Locus.locusV());
        p.prepareBit(seed);
        p.prepareBit(seedDistDelta);
        p.prepareBit(seedDist)
        ;
// initialisation 
        int pseed = 0, pseedDist$0 = 0, pseedDist$1 = 0, pseedDist$2 = 0, r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
        for (int i = 1; i < seed.length - 1; i++) {
            pseedDist$0 = seedDist$0[i];
            pseedDist$1 = seedDist$1[i];
            pseedDist$2 = seedDist$2[i];
            pseed = seed[i];
            r0 = ~pseed;
            r3 = (r4 = pseedDist$0);
            r3 = (r3 | (r4 = ((r2 = ~pseedDist$0) ^ ~pseedDist$1)));
            r3 = (r3 | (r4 = ((r2 & ~pseedDist$1) ^ ~pseedDist$2)));
            r1 = r4;
            llseedDist$0[i] = (pseedDist$0 ^ (r4 = ((pseed & r3) | (r0 & seedDistDelta$0[i]))));
            llseedDist$1[i] = (((r5 = (r4 & pseedDist$0)) ^ pseedDist$1) ^ (r4 = (r2 = ((pseed & r1) | (r0 & seedDistDelta$1[i])))));
            llseedDist$2[i] = ((((r5 & pseedDist$1) | (r4 & (r5 | pseedDist$1))) ^ pseedDist$2) ^ r2);
        }
    }

    public static void _fun4(PrShift p, int[][] seedDistSloplt, int[][] seedDistVortexR) {
        int[] seedDistVortexR$do = seedDistVortexR[0], seedDistVortexR$up = seedDistVortexR[1], seedDistSloplt$e = seedDistSloplt[0], seedDistSloplt$se = seedDistSloplt[1], seedDistSloplt$sw = seedDistSloplt[2], seedDistSloplt$w = seedDistSloplt[3], seedDistSloplt$nw = seedDistSloplt[4], seedDistSloplt$ne = seedDistSloplt[5];
        p.mirror(seedDistSloplt, compiler.Locus.locusVe());
        p.prepareBit(seedDistSloplt)
        ;
// initialisation 
        int auxL31 = 0, pseedDistSloplt = 0, seedDistVortex$do = 0, seedDistVortex$dotm1 = 0, seedDistVortex$up = 0, shiftpseedDistSloplt = 0, tmun22 = 0;
        for (int i = 1; i < seedDistSloplt$e.length - 1; i++) {
            auxL31 = seedDistSloplt$nw[i];
            pseedDistSloplt = seedDistSloplt$ne[i];
            seedDistVortex$do = (seedDistVortex$dotm1 & (pseedDistSloplt ^ auxL31));
            shiftpseedDistSloplt = pseedDistSloplt;
            pseedDistSloplt = seedDistSloplt$e[i];
            seedDistVortex$up = ((pseedDistSloplt ^ shiftpseedDistSloplt) >>> 1);
            shiftpseedDistSloplt = pseedDistSloplt;
            pseedDistSloplt = seedDistSloplt$se[i];
            seedDistVortex$dotm1 = (pseedDistSloplt ^ shiftpseedDistSloplt);
            shiftpseedDistSloplt = pseedDistSloplt;
            pseedDistSloplt = seedDistSloplt$sw[i];
            seedDistVortex$up = (seedDistVortex$up & tmun22);
            tmun22 = (pseedDistSloplt ^ shiftpseedDistSloplt);
            shiftpseedDistSloplt = pseedDistSloplt;
            pseedDistSloplt = seedDistSloplt$w[i];
            seedDistVortex$dotm1 = (seedDistVortex$dotm1 & ((pseedDistSloplt ^ shiftpseedDistSloplt) << 1));
            shiftpseedDistSloplt = pseedDistSloplt;
            seedDistVortexR$do[i - 1] = seedDistVortex$do;
            seedDistVortexR$up[i - 1] = (seedDistVortex$up & (auxL31 ^ shiftpseedDistSloplt));
        }
    }

    public int CAmemWidth() {
        return 48;
    }

    @Override
    public ArrayList<String> theLoops(PrShift p, int[][] m) {
        ArrayList<String> bugs = new ArrayList<>();
        int[] auxC00 = m[47], llseed = m[0], seed = m[11], llbugV = m[4], seedDistBMeetv = m[14];
        int[][] seedDist = new int[][]{m[32], m[33], m[34]}, defVe = new int[][]{m[40], m[39], m[38], m[37], m[36], m[35]}, llseedDist = new int[][]{m[1], m[2], m[3]}, lldefVe = new int[][]{m[5], m[6], m[7], m[8], m[9], m[10]}, seedDistBMeete = new int[][]{m[15], m[16], m[17]}, seedDistSloplt = new int[][]{m[21], m[22], m[23], m[24], m[25], m[26]}, auxC01 = new int[][]{m[41], m[42], m[43], m[44], m[45], m[46]}, seedDistLevel = new int[][]{m[29], m[30], m[31]}, auxC02 = new int[][]{m[35], m[36], m[37], m[38], m[39], m[40]}, seedDistDelta = new int[][]{m[27], m[28]}, seedDistBNbcc = new int[][]{m[35], m[36]}, seedDistGap = new int[][]{m[18], m[19], m[20]}, seedDistVortex = new int[][]{m[12], m[13]}, seedDistBTwoadjblob = new int[][]{m[35], m[36], m[37]};

        copy(llseedDist, seedDist);
        grad.slopDelta_3(p, seedDist, seedDistSloplt, seedDistDelta, seedDistLevel, seedDistGap, lldefVe);
        show(seedDistLevel);
        redT.enlargeEF_1(p, seedDistSloplt, auxC02);
        redT.enlargeFE_1(p, auxC02, auxC01);
        copy(lldefVe, defVe);
        _fun0(p, seedDistSloplt, defVe, auxC00);
        redsandb.ve_1(p, auxC00, seedDistBTwoadjblob);
        _fun3(p, auxC01, seedDistBTwoadjblob, seedDistBMeete);
        show(seedDistBMeete);
        copy(llseed, seed);
        _fun1(p, seed, seedDistDelta, seedDist, llseedDist);
        topo.nbcc_1(p, seedDistSloplt, seedDistBNbcc);
        _fun2(p, seedDistBNbcc, seedDistBMeetv);
        show(seedDistBMeetv);
        _fun4(p, seedDistSloplt, seedDistVortex);
        show(seedDistVortex);
        show(seed);
        show(seedDist);
        show(seedDistDelta);
        show(seedDistSloplt);
        show(seedDistGap);
        return bugs;
    }


    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
        map.put("seedDist", li(32, 33, 34));
        map.put("llseed", li(0));
        map.put("seed", li(11));
        map.put("llseedDist", li(1, 2, 3));
        map.put("llbugV", li(4));
        map.put("lldefVe", li(5, 6, 7, 8, 9, 10));
        map.put("seedDistBMeete", li(15, 16, 17));
        map.put("seedDistSloplt", li(21, 22, 23, 24, 25, 26));
        map.put("auxC01", li(41, 42, 43, 44, 45, 46));
        map.put("seedDistLevel", li(29, 30, 31));
        map.put("auxC02", li(35, 36, 37, 38, 39, 40));
        map.put("auxC00", li(47));
        map.put("seedDistDelta", li(27, 28));
        map.put("seedDistBNbcc", li(35, 36));
        map.put("seedDistGap", li(18, 19, 20));
        map.put("seedDistVortex", li(12, 13));
        map.put("seedDistBTwoadjblob", li(35, 36, 37));
        map.put("seedDistBMeetv", li(14));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseedDist", compiler.Locus.locusV());
        map.put("lldefVe", compiler.Locus.locusVe());
        map.put("seed", compiler.Locus.locusV());
        map.put("auxC01", compiler.Locus.locusVe());
        map.put("llseed", compiler.Locus.locusV());
        map.put("seedDistBNbcc", compiler.Locus.locusV());
        map.put("seedDistGap", compiler.Locus.locusE());
        map.put("seedDistDelta", compiler.Locus.locusV());
        map.put("seedDistSloplt", compiler.Locus.locusVe());
        map.put("seedDistLevel", compiler.Locus.locusE());
        map.put("seedDistBMeetv", compiler.Locus.locusV());
        map.put("auxC02", compiler.Locus.locusVf());
        map.put("auxC00", compiler.Locus.locusV());
        map.put("seedDistVortex", compiler.Locus.locusF());
        map.put("seedDistBTwoadjblob", compiler.Locus.locusE());
        map.put("llbugV", compiler.Locus.locusV());
        map.put("defVe", compiler.Locus.locusVe());
        map.put("seedDist", compiler.Locus.locusV());
        map.put("seedDistBMeete", compiler.Locus.locusE());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        map.put("llseedDist", 3);
        map.put("seedDistBNbcc", 2);
        map.put("seedDistDelta", 2);
        map.put("seedDist", 3);
        return (map);
    }

    @Override
    public String displayableLayerHierarchy() {
        return "seed(seedDist(seedDistB(seedDistBMeetv)(seedDistBMeete))(seedDistGap)(seedDistDelta)(seedDistVortex)(seedDistSloplt)(seedDistLevel)).";
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
        return (302);
    }

}
