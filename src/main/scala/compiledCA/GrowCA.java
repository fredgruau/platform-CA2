package compiledCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static compiledMacro.RedS.*;
import static simulator.Util.*;

public final class GrowCA implements CAloops2 {
    public int CAmemWidth() {
        return 9
                ;
    }

    public static int[] grow, llbugV, growNext, llgrow;
    ;
    public static int[][] E0;
    ;
    public int[][] mem; //we will need to access the whole memory


    public void anchorFieldInMem(int[][] m) {
        //global variables
        grow = m[2];
        llbugV = m[0];
        growNext = m[3];
        llgrow = m[1];
        E0 = new int[][]{m[4], m[5], m[6]};
        mem = m;
    }


    @Override
    public HashMap<String, List<Integer>> fieldOffset() { //for layer's initialization and update, as well as displayed fields.
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("grow", li(2));
        map.put("llbugV", li(0));
        map.put("growNext", li(3));
        map.put("llgrow", li(1));
        return (map);
    }


    @Override
    public ArrayList<String> theLoops(PrShift p) {
        ArrayList<String> bugs = new ArrayList<>();
        copy(llgrow, grow);
        redorBVE_1(p, grow, E0);
        redandBEV_1(p, E0, mem[7]);
        redorBEV_1(p, E0, mem[8]);
        _fun0(p, mem[8], mem[7], growNext);
        show(growNext);
        show(grow);
        memo(growNext, llgrow);
        return bugs;
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llgrow", Locus.locusV());
        map.put("grow", Locus.locusV());
        map.put("llbugV", Locus.locusV());
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
        return "(grow(growNext))";
    }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();
        map.put("llgrow", "global");
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
