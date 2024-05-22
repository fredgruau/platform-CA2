package compiledMacro;

import simulator.PrShift;

public class redsandb {

    public static void ve_1(PrShift p, int[] ppVE, int[][] resultCAR) {
        int[] resultCAR$h = resultCAR[0], resultCAR$d = resultCAR[1], resultCAR$ad = resultCAR[2];
        p.mirror(ppVE, compiler.Locus.locusV());
        p.prepareBit(ppVE)
        ;
// initialisation 
        int auxL27 = 0, auxL28 = 0;
        for (int i = 1; i < ppVE.length - 1; i++) {
            resultCAR$h[i - 1] = ((auxL28 << 1) & auxL28);
            auxL28 = ppVE[i];
            resultCAR$d[i - 1] = (auxL27 & auxL28);
            resultCAR$ad[i - 1] = (auxL27 & (auxL28 >>> 1));
            auxL27 = auxL28;
        }
    }
}