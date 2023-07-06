package compHandCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;
import simulator.Util;

import java.util.HashMap;

import static compiledLoops.redS.orE2V;
import static compiledLoops.redS.orV2E;
import static simulator.Util.anchorFixedInMem;
/**
 * This illustrates an example of the files that should be produced by the compiler in order to describe a CA
 * THis will regroupe all the 6 reduction from one simplicial locus to the two others,
 * using whatever reduction operatior boolean or integer
 */


public final class Grow2CA implements CAloops2 {
    public int CAmemWidth() {
        return 11;
    }

    public static int[][] seedE;
    public static int[] seed;

    public void anchorFieldInMem(int[][] m) {
        anchorFixedInMem(m);//global variables
        seed = m[7];
        seedE = new int[][]{m[8], m[9], m[10]};
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("defVe", Util.li(1, 2, 3, 4, 5, 6));
        map.put("llseed", Util.li(7));
        map.put("E", Util.li(8, 9, 10));
        return (map);
    }

    @Override
    public void theLoops(PrShift p) {
        orV2E(p, seed, seedE);
        orE2V(p, seedE, seed);
        //orV2E(p,mem[7],mem[8],mem[9],mem[10]);
        //orE2V(p, mem[1], mem[2], mem[3], mem[4], mem[5], mem[6], mem[8],mem[9],mem[10],mem[7]);
        //  grow(p, mem[0], mem[3], mem[4], mem[5], mem[6], mem[7], mem[8]);
    }


    @Override
    public List<String> directInit() {
        return CAloops.list("llseed", "defVe");//
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseed", Locus.locusV());
        map.put("defVe", Locus.locusVe());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }
}


