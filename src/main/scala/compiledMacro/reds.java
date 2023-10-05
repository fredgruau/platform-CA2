package compiledMacro;

import simulator.PrShift;

public class reds {
    public static void orbve_1(PrShift p, int[] ppVE, int[][] resultCAR) {
        int[] resultCAR$h = resultCAR[0], resultCAR$d = resultCAR[1], resultCAR$ad = resultCAR[2];
        p.propagate4shift(ppVE);
// initialisation 
        int auxL00 = 0, auxL01 = 0;
        for (int i = 1; i < ppVE.length - 1; i++) {
            resultCAR$h[i - 1] = auxL01 | auxL01 << 1;
            auxL01 = ppVE[i];
            resultCAR$d[i - 1] = auxL00 | auxL01;
            resultCAR$ad[i - 1] = auxL00 | auxL01 >>> 1;
            auxL00 = auxL01;
        }
    }
}