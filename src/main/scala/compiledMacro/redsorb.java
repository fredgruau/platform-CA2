package compiledMacro;

import simulator.PrShift;

public class redsorb {

    public static void ev_1(PrShift p, int[][] ppEV, int[] resultCAR, int[][] lldefVe) {
        int[] lldefVe$e = lldefVe[0], lldefVe$se = lldefVe[1], lldefVe$sw = lldefVe[2], lldefVe$w = lldefVe[3], lldefVe$nw = lldefVe[4], lldefVe$ne = lldefVe[5], ppEV$h = ppEV[0], ppEV$d = ppEV[1], ppEV$ad = ppEV[2];
        p.mirror(ppEV, compiler.Locus.locusE());
        p.prepareBit(ppEV)
        ;
// initialisation 
        int auxL15 = 0, auxL16 = 0, auxL17 = 0, auxL18 = 0, defVe$e = 0, defVe$ne = 0, defVe$nw = 0, defVe$se = 0, defVe$sw = 0, defVe$w = 0, tmun00 = 0, tmun01 = 0;
        for (int i = 1; i < ppEV$h.length - 1; i++) {
            defVe$e = lldefVe$e[i];
            auxL15 = ppEV$h[i];
            defVe$se = lldefVe$se[i];
            auxL16 = ppEV$d[i];
            defVe$sw = lldefVe$sw[i];
            auxL18 = ppEV$ad[i];
            defVe$w = lldefVe$w[i];
            defVe$nw = lldefVe$nw[i];
            defVe$ne = lldefVe$ne[i];
            resultCAR[i] = ((((((defVe$e & auxL15) | (defVe$se & auxL16)) | (defVe$sw & auxL18)) | (defVe$w & (auxL15 >>> 1))) | (defVe$nw & tmun01)) | (defVe$ne & tmun00));
            tmun01 = auxL16;
            tmun00 = (auxL18 << 1);
        }
    }
}