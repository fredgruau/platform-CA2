package compiledCA;

import compiledMacro.integer;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static simulator.Util.*;

public final class TdisCA implements CAloops2 {
    public static void _fun0(PrShift p, int[][] tdisDist, int[][] tdisDistDelta, int[] tdis, int[][] lltdisDist) {
        int[] lltdisDist$0 = lltdisDist[0], lltdisDist$1 = lltdisDist[1], lltdisDist$2 = lltdisDist[2], tdisDist$0 = tdisDist[0], tdisDist$1 = tdisDist[1], tdisDist$2 = tdisDist[2], tdisDistDelta$0 = tdisDistDelta[0], tdisDistDelta$1 = tdisDistDelta[1];
        p.propagate4shift(tdisDist$0);
        p.propagate4shift(tdisDist$1);
        p.propagate4shift(tdisDist$2);
        p.propagate4shift(tdisDistDelta$0);
        p.propagate4shift(tdisDistDelta$1);
        p.propagate4shift(tdis);
        // initialisation 
        int ptdis = 0, ptdisDist$0 = 0, ptdisDist$1 = 0, ptdisDist$2 = 0, r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0;
        for (int i = 1; i < tdisDist$0.length; i++) {
            ptdisDist$0 = tdisDist$0[i];
            ptdisDist$1 = tdisDist$1[i];
            ptdisDist$2 = tdisDist$2[i];
            ptdis = tdis[i];
            r0 = ~ptdis;
            r3 = ptdisDist$0;
            r2 = r3;
            r3 = r4 = ~ptdisDist$0 ^ ~ptdisDist$1;
            r2 = r2 | r3;
            r1 = (r3 = (r4 & ~ptdisDist$1) ^ ~ptdisDist$2);
            r2 = r2 | r3;
            lltdisDist$0[i] = ptdisDist$0 ^ (r3 = (ptdis & r2) | r0 & tdisDistDelta$0[i]);
            lltdisDist$1[i] = (r5 = r3 & ptdisDist$0 ^ ptdisDist$1) ^ (r3 = (r4 = (ptdis & r1) | r0 & tdisDistDelta$1[i]));
            lltdisDist$2[i] = (((r5 & ptdisDist$1) | r3 & r5 | ptdisDist$1) ^ ptdisDist$2) ^ r4;
        }
    }

    public static void _fun1(PrShift p, int[][] tdisDistTslope, int[][] vortexR) {
        int[] vortexR$do = vortexR[0], vortexR$up = vortexR[1], tdisDistTslope$e = tdisDistTslope[0], tdisDistTslope$se = tdisDistTslope[1], tdisDistTslope$sw = tdisDistTslope[2], tdisDistTslope$w = tdisDistTslope[3], tdisDistTslope$nw = tdisDistTslope[4], tdisDistTslope$ne = tdisDistTslope[5];
        p.propagate4shift(tdisDistTslope$e);
        p.propagate4shift(tdisDistTslope$se);
        p.propagate4shift(tdisDistTslope$sw);
        p.propagate4shift(tdisDistTslope$w);
        p.propagate4shift(tdisDistTslope$nw);
        p.propagate4shift(tdisDistTslope$ne);
        // initialisation 
        int auxL05 = 0, ptdisDistTslope = 0, shiftptdisDistTslope = 0, tmun00 = 0, vortex$do = 0, vortex$dotm1 = 0, vortex$up = 0;
        for (int i = 1; i < tdisDistTslope$e.length; i++) {
            auxL05 = tdisDistTslope$nw[i];
            ptdisDistTslope = tdisDistTslope$ne[i];
            vortex$do = vortex$dotm1 & ptdisDistTslope ^ auxL05;
            shiftptdisDistTslope = ptdisDistTslope;
            ptdisDistTslope = tdisDistTslope$e[i];
            vortex$up = (ptdisDistTslope ^ shiftptdisDistTslope) >>> 1;
            shiftptdisDistTslope = ptdisDistTslope;
            ptdisDistTslope = tdisDistTslope$se[i];
            vortex$dotm1 = ptdisDistTslope ^ shiftptdisDistTslope;
            shiftptdisDistTslope = ptdisDistTslope;
            ptdisDistTslope = tdisDistTslope$sw[i];
            vortex$up = vortex$up & tmun00;
            tmun00 = ptdisDistTslope ^ shiftptdisDistTslope;
            shiftptdisDistTslope = ptdisDistTslope;
            ptdisDistTslope = tdisDistTslope$w[i];
            vortex$dotm1 = vortex$dotm1 & (ptdisDistTslope ^ shiftptdisDistTslope) << 1;
            shiftptdisDistTslope = ptdisDistTslope;
            vortexR$do[i - 1] = vortex$do;
            vortexR$up[i - 1] = vortex$up & auxL05 ^ shiftptdisDistTslope;
        }
    }

    public int CAmemWidth() {
        return 19
                ;
    }

    public int[][] mem; //we will need to access the whole memory
    public static int[] llbugV, lltdis, tdis;
    public static int[][] llbugF, tdisDist, tdisDistDelta, lltdisDist, vortex, tdisDistTslope;

    public void anchorFieldInMem(int[][] m) {
        mem = m;
        vortex = new int[][]{m[8], m[9]};
        lltdisDist = new int[][]{m[0], m[1], m[2]};
        tdisDistTslope = new int[][]{m[16], m[17], m[15], m[13], m[11], m[18]};
        llbugV = m[3];
        llbugF = new int[][]{m[4], m[5]};
        lltdis = m[6];
        tdisDist = new int[][]{m[10], m[9], m[8]};
        tdis = m[7];
        tdisDistDelta = new int[][]{m[14], m[12]};
    }

    @Override
    public void copyLayer(int[][] m) {
        copy(lltdis, tdis);
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
        map.put("vortex", li(8, 9));
        map.put("lltdisDist", li(0, 1, 2));
        map.put("tdisDistTslope", li(16, 17, 15, 13, 11, 18));
        map.put("llbugV", li(3));
        map.put("llbugF", li(4, 5));
        map.put("lltdis", li(6));
        map.put("tdisDist", li(10, 9, 8));
        map.put("tdis", li(7));
        map.put("tdisDistDelta", li(14, 12));
        return (map);
    }

    @Override
    public ArrayList<String> theLoops(PrShift p, int[][] m) {
        ArrayList<String> bugs = new ArrayList<>();
        copy(lltdis, tdis);
        copy(lltdisDist, tdisDist);
        integer.grad_3(p, tdisDist, tdisDistTslope, tdisDistDelta);
        _fun0(p, tdisDist, tdisDistDelta, tdis, lltdisDist);
        show(tdisDist);
        show(tdisDistTslope);
        _fun1(p, tdisDistTslope, vortex);
        bug(vortex, llbugF, "vortex", bugs);
        return bugs;
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llbugF", Locus.locusF());
        map.put("tdisDist", Locus.locusV());
        map.put("tdisDistDelta", Locus.locusV());
        map.put("lltdisDist", Locus.locusV());
        map.put("lltdis", Locus.locusV());
        map.put("tdis", Locus.locusV());
        map.put("vortex", Locus.locusF());
        map.put("llbugV", Locus.locusV());
        map.put("tdisDistTslope", Locus.locusVe());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        map.put("tdisDist", 3);
        map.put("tdisDistDelta", 2);
        map.put("lltdisDist", 3);
        return (map);
    }

    @Override
    public String displayableLayerHierarchy() {
        return "tdistdisDist(tdisDistTslope)..";
    }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();
        map.put("llbugF", "false");
        map.put("lltdisDist", "0");
        map.put("lltdis", "global");
        map.put("llbugV", "false");
        return (map);
    }
}
