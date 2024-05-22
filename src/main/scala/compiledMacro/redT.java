package compiledMacro;

import simulator.PrShift;

public class redT {

    public static void enlargeFE_1(PrShift p, int[][] penlarge, int[][] resultCA) {
        int[] resultCA$e = resultCA[0], resultCA$se = resultCA[1], resultCA$sw = resultCA[2], resultCA$w = resultCA[3], resultCA$nw = resultCA[4], resultCA$ne = resultCA[5], penlarge$es = penlarge[0], penlarge$s = penlarge[1], penlarge$ws = penlarge[2], penlarge$wn = penlarge[3], penlarge$n = penlarge[4], penlarge$en = penlarge[5];
        p.mirror(penlarge, compiler.Locus.locusVf());
        p.prepareBit(penlarge)
        ;
// initialisation 
        int auxL30 = 0, enlarge = 0, shiftenlarge = 0;
        for (int i = 1; i < penlarge$es.length - 1; i++) {
            auxL30 = penlarge$en[i];
            enlarge = penlarge$es[i];
            resultCA$e[i] = (enlarge | auxL30);
            shiftenlarge = enlarge;
            enlarge = penlarge$s[i];
            resultCA$se[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$ws[i];
            resultCA$sw[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$wn[i];
            resultCA$w[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$n[i];
            resultCA$nw[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            resultCA$ne[i] = (auxL30 | shiftenlarge);
        }
    }

    public static void enlargeEF_1(PrShift p, int[][] penlarge, int[][] resultCA) {
        int[] resultCA$es = resultCA[0], resultCA$s = resultCA[1], resultCA$ws = resultCA[2], resultCA$wn = resultCA[3], resultCA$n = resultCA[4], resultCA$en = resultCA[5], penlarge$e = penlarge[0], penlarge$se = penlarge[1], penlarge$sw = penlarge[2], penlarge$w = penlarge[3], penlarge$nw = penlarge[4], penlarge$ne = penlarge[5];
        p.mirror(penlarge, compiler.Locus.locusVe());
        p.prepareBit(penlarge)
        ;
// initialisation 
        int auxL32 = 0, enlarge = 0, shiftenlarge = 0;
        for (int i = 1; i < penlarge$e.length - 1; i++) {
            auxL32 = penlarge$e[i];
            enlarge = penlarge$se[i];
            resultCA$es[i] = (enlarge | auxL32);
            shiftenlarge = enlarge;
            enlarge = penlarge$sw[i];
            resultCA$s[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$w[i];
            resultCA$ws[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$nw[i];
            resultCA$wn[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            enlarge = penlarge$ne[i];
            resultCA$n[i] = (enlarge | shiftenlarge);
            shiftenlarge = enlarge;
            resultCA$en[i] = (auxL32 | shiftenlarge);
        }
    }
}