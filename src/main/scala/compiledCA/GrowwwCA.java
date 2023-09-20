package compiledCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static compiledMacro.RedS.*;
import static simulator.Util.*;

public final class GrowwwCA implements CAloops2 {
    public int CAmemWidth() {
        return 9
                ;
    }

    public static int[] llbugV, growNext, growww, llgrowww;
    ;
    public static int[][] E0;
    ;
    public int[][] mem; //we will need to access the whole memory


    public void anchorFieldInMem(int[][] m) {
        //global variables
        llbugV = m[0];
        growNext = m[3];
        growww = m[2];
        llgrowww = m[1];
        E0 = new int[][]{m[4], m[5], m[6]};
        mem = m;
    }


    @Override
    public HashMap<String, List<Integer>> fieldOffset() { //for layer's initialization and update, as well as displayed fields.
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("llbugV", li(0));
        map.put("growNext", li(3));
        map.put("growww", li(2));
        map.put("llgrowww", li(1));
        return (map);
    }


    @Override
    public ArrayList<String> theLoops(PrShift p) {
        ArrayList<String> bugs = new ArrayList<>();
        copy(llgrowww, growww);
        redorBVE_1(p, growww, E0);
        redandBEV_1(p, E0, mem[7]);
        redorBEV_1(p, E0, mem[8]);
        _fun0(p, mem[8], mem[7], growNext);
        show(growNext);
        memo(growNext, llgrowww);
        show(growww);
        return bugs;
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llgrowww", Locus.locusV());
        map.put("llbugV", Locus.locusV());
        map.put("growww", Locus.locusV());
        map.put("growNext", Locus.locusV());
        return (map);
    }


    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();

        return (map);
    }

    @Override
    public String displayableLayerHierarchy() {
        return "(growww)";
    }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();
        map.put("llgrowww", "global");
        map.put("llbugV", "false");

        return (map);
    }

    public static void _fun0(PrShift p, int[] auxC01, int[] auxC00, int[] neighbVV) {

        p.propagate4shift(auxC01);
        p.propagate4shift(auxC00);

        for (int i = 1; i < auxC01.length; i++) {
            neighbVV[i] = auxC01[i] | auxC00[i];
        }
    }
}
