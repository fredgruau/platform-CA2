package compiledMacro;

import simulator.PrShift;

public class RedS {
    public static void redorBEV_1(PrShift p, int[][] ppEV, int[] resultCAR) {
        int[] ppEV$h = ppEV[0], ppEV$d = ppEV[1], ppEV$ad = ppEV[2];
        p.propagate4shift(ppEV$h);
        p.propagate4shift(ppEV$d);
        p.propagate4shift(ppEV$ad);
        int auxL04, auxL02, auxL03, tmun00 = 0;
        for (int i = 1; i < ppEV$h.length; i++) {
            auxL02 = ppEV$h[i];
            auxL03 = ppEV$d[i];
            auxL04 = ppEV$ad[i];
            resultCAR[i] = (((tmun00 | auxL02) | auxL03) | auxL04) | (auxL02 >>> 1);
            tmun00 = auxL03 | (auxL04 << 1);
        }
    }

    public static void redandBEV_1(PrShift p, int[][] ppEV, int[] resultCAR) {
        int[] ppEV$h = ppEV[0], ppEV$d = ppEV[1], ppEV$ad = ppEV[2];
        p.propagate4shift(ppEV$h);
        p.propagate4shift(ppEV$d);
        p.propagate4shift(ppEV$ad);
        int auxL06, auxL07, auxL05, tmun01 = 0;
        for (int i = 1; i < ppEV$h.length; i++) {
            auxL05 = ppEV$h[i];
            auxL06 = ppEV$d[i];
            auxL07 = ppEV$ad[i];
            resultCAR[i] = (((tmun01 & auxL05) & auxL06) & auxL07) & (auxL05 >>> 1);
            tmun01 = auxL06 & (auxL07 << 1);
        }
    }

    public static void redorBVE_1(PrShift p, int[] ppVE, int[][] resultCAR) {
        int[] resultCAR$h = resultCAR[0], resultCAR$d = resultCAR[1], resultCAR$ad = resultCAR[2];
        p.propagate4shift(ppVE);
        int auxL08 = 0, auxL09 = 0;
        for (int i = 1; i < ppVE.length; i++) {
            resultCAR$h[i - 1] = auxL09 | (auxL09 << 1);
            auxL09 = ppVE[i];
            resultCAR$d[i - 1] = auxL08 | auxL09;
            resultCAR$ad[i - 1] = auxL08 | (auxL09 >>> 1);
            auxL08 = auxL09;
        }
    }
}