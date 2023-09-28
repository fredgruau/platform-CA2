package compiledCA;
//hand generated
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static compiledMacro.BasicMoves.*;
import static simulator.Util.*;

/**
 * Example of  files that should be produced by the compiler in order to describe a CA
 * Grows is directly implemented using only 6 Ors, without computing an intermediate boolE
 * contains a bug test, using shrink
 */

public final class GrowCA2 implements CAloops2 {
    public static int[][] defVe, seedE;
    public static int[] seed, bugV, squeleton;


    public void anchorFieldInMem(int[][] mem) {
        //anchorFixedInMem(mem);//global variables
        seed = mem[0];
        bugV = mem[14];
        squeleton = mem[15];
        defVe = new int[][]{mem[3], mem[4], mem[5], mem[6], mem[7], mem[8]};
        seedE = new int[][]{mem[16], mem[17], mem[18]};
    }
    @Override
    public void copyLayer(int[][] m) {
    }

    @Override
    public ArrayList<String> theLoops(PrShift p, int[][] m) {
        ArrayList<String> bugs = new ArrayList<>();
        // grow(p, seed, defVe);
        eexistV2E_1(p, seed, seedE);
        eexistE2V_1(p, seedE, seed, defVe);
        copy(seed, squeleton);
        for (int i = 0; i < 5; i++)
            shrink(p, squeleton, defVe);
        bug(squeleton, bugV, "squeletonNonNull", bugs);
        return bugs;
    }


    public int CAmemWidth() {
        return 19;
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("llseed", CAloops.list(new Integer(0)));
        map.put("seedGab", CAloops.list(new Integer(1)));
        map.put("seedTmp2", CAloops.list(new Integer(2)));
        map.put("defVe", li(3, 4, 5, 6, 7, 8));
        map.put("seedE", CAloops.list(new Integer(16), new Integer(17), new Integer(18)));
        map.put("defE", CAloops.list(new Integer(9), new Integer(10), new Integer(11)));
        map.put("defF", CAloops.list(new Integer(12), new Integer(13)));
        map.put("bugV", CAloops.list(new Integer(14)));
        map.put("squeleton", CAloops.list(new Integer(15)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseed", Locus.locusV());
        map.put("seedGab", Locus.locusV());
        map.put("seedTmp2", Locus.locusV());
        map.put("defVe", Locus.locusVe());
        map.put("seedE", Locus.locusE());
        map.put("defE", Locus.locusE());
        map.put("defF", Locus.locusF());
        map.put("bugV", Locus.locusV());
        map.put("squeleton", Locus.locusV());
        return (map);
    }

    //     <layer init="global">llseed</layer>       <layer init="def">defE</layer>  <layer init="def">defF</layer>      <layer init="def">defVe</layer>
    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();
        map.put("llseed", "global");
        map.put("defVe", "def");
        map.put("defE", "def");
        map.put("defF", "def");
        return (map);
    }

    @Override
    public String displayableLayerHierarchy() {
        return "(layer" +
                "(seed(llseed)(squeleton)(seedE))" +
                "(def(defF)(defE)(defVe))" + ")";
    }




}


