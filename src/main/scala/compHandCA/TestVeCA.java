
package compHandCA;

import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.PrShift;

import java.util.HashMap;

import static compiledLoops.BasicMoves.etoVe;

/**
 * This illustrate an example of the files that should be produced by the compiler in order to describe a CA
 */


public final class TestVeCA implements CAloops {

    @Override
    public void theLoops(int[][] mem, PrShift p) {
        etoVe(p, mem[0], mem[1], mem[2], mem[14], mem[15], mem[16], mem[17], mem[18], mem[19]);
    }


    @Override
    public List<String> directInit() {
        return CAloops.list("llseed", "defE", "defF", "defVe");//
        // ,"defVe"
    }

    public int CAmemWidth() {
        return 20;
    }

    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>();
        map.put("llseed", CAloops.list(new Integer(0), new Integer(1), new Integer(2)));
        map.put("defVe", CAloops.list(new Integer(3), new Integer(4), new Integer(5), new Integer(6), new Integer(7), new Integer(8)));
        map.put("defE", CAloops.list(new Integer(9), new Integer(10), new Integer(11)));
        map.put("defF", CAloops.list(new Integer(12), new Integer(13)));
        map.put("Ve", CAloops.list(new Integer(14), new Integer(15), new Integer(16), new Integer(17), new Integer(18), new Integer(19)));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("llseed", Locus.locusE());
        map.put("defVe", Locus.locusVe());
        map.put("defE", Locus.locusE());
        map.put("defF", Locus.locusF());
        map.put("Ve", Locus.locusVe());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        return (map);
    }
}


