package compiledMacro;

import simulator.PrShift;

public class redsxorb {

    public static void ve_1(PrShift p, int[] ppVE, int[][] resultCAR) {
        int[] resultCAR$h = resultCAR[0], resultCAR$d = resultCAR[1], resultCAR$ad = resultCAR[2];
        p.mirror(ppVE, compiler.Locus.locusV());
        p.prepareBit(ppVE)
        ;
// initialisation 
        int auxL42 = 0, auxL43 = 0;
        for (int i = 1; i < ppVE.length - 1; i++) {
            resultCAR$h[i - 1] = ((auxL43 << 1) ^ auxL43);
            auxL43 = ppVE[i];
            resultCAR$d[i - 1] = (auxL42 ^ auxL43);
            resultCAR$ad[i - 1] = (auxL42 ^ (auxL43 >>> 1));
            auxL42 = auxL43;
        }
    }
}