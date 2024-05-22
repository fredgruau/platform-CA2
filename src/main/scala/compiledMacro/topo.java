package compiledMacro;

import simulator.PrShift;

public class topo {

    public static void nbcc_1(PrShift p, int[][] pringAroundV, int[][] resultCA) {
        int[] resultCA$0 = resultCA[0], resultCA$1 = resultCA[1], pringAroundV$e = pringAroundV[0], pringAroundV$se = pringAroundV[1], pringAroundV$sw = pringAroundV[2], pringAroundV$w = pringAroundV[3], pringAroundV$nw = pringAroundV[4], pringAroundV$ne = pringAroundV[5];
        p.mirror(pringAroundV, compiler.Locus.locusVe());
        p.prepareBit(pringAroundV)
        ;
// initialisation 
        int asInt$0 = 0, asInt$1 = 0, asInt$2 = 0, asInt$3 = 0, asInt$4 = 0, asInt$5 = 0, auxL06 = 0, auxL07 = 0, auxL08 = 0, auxL26 = 0, r0 = 0, r1 = 0, ringAroundV = 0, shiftringAroundV = 0;
        for (int i = 1; i < pringAroundV$e.length - 1; i++) {
            auxL26 = pringAroundV$e[i];
            ringAroundV = pringAroundV$se[i];
            asInt$1 = (ringAroundV & ~auxL26);
            shiftringAroundV = ringAroundV;
            ringAroundV = pringAroundV$sw[i];
            asInt$2 = (ringAroundV & ~shiftringAroundV);
            shiftringAroundV = ringAroundV;
            ringAroundV = pringAroundV$w[i];
            asInt$3 = (ringAroundV & ~shiftringAroundV);
            shiftringAroundV = ringAroundV;
            ringAroundV = pringAroundV$nw[i];
            asInt$4 = (ringAroundV & ~shiftringAroundV);
            shiftringAroundV = ringAroundV;
            ringAroundV = pringAroundV$ne[i];
            asInt$5 = (ringAroundV & ~shiftringAroundV);
            shiftringAroundV = ringAroundV;
            asInt$0 = (auxL26 & ~shiftringAroundV);
            r0 = asInt$2;
            r1 = asInt$3;
            auxL07 = (r0 | r1);
            r0 = asInt$4;
            r1 = asInt$5;
            auxL06 = (r0 | r1);
            r0 = asInt$1;
            r1 = asInt$0;
            auxL08 = (r1 | r0);
            resultCA$0[i] = ((auxL08 ^ auxL07) ^ auxL06);
            resultCA$1[i] = ((auxL08 & auxL07) | (auxL06 & (auxL08 | auxL07)));
        }
    }

    public static void brdin_1_1(PrShift p, int[][] pbrd, int[] pis, int[][] resultCA, int[][] lldefVe) {
        int[] lldefVe$e = lldefVe[0], lldefVe$se = lldefVe[1], lldefVe$sw = lldefVe[2], lldefVe$w = lldefVe[3], lldefVe$nw = lldefVe[4], lldefVe$ne = lldefVe[5], resultCA$e = resultCA[0], resultCA$se = resultCA[1], resultCA$sw = resultCA[2], resultCA$w = resultCA[3], resultCA$nw = resultCA[4], resultCA$ne = resultCA[5], pbrd$h = pbrd[0], pbrd$d = pbrd[1], pbrd$ad = pbrd[2];
        p.mirror(pbrd, compiler.Locus.locusE());
        p.mirror(pis, compiler.Locus.locusV());
        p.prepareBit(pbrd);
        p.prepareBit(pis)
        ;
// initialisation 
        int auxL23 = 0, auxL24 = 0, auxL25 = 0, auxL26 = 0, defVe$e = 0, defVe$ne = 0, defVe$nw = 0, defVe$se = 0, defVe$sw = 0, defVe$w = 0, tmun06 = 0, tmun07 = 0;
        for (int i = 1; i < pbrd$h.length - 1; i++) {
            defVe$e = lldefVe$e[i];
            auxL25 = pis[i];
            auxL23 = pbrd$h[i];
            resultCA$e[i] = ((defVe$e & auxL23) | (~defVe$e & auxL25));
            defVe$se = lldefVe$se[i];
            auxL24 = pbrd$d[i];
            resultCA$se[i] = ((defVe$se & auxL24) | (~defVe$se & auxL25));
            defVe$sw = lldefVe$sw[i];
            auxL26 = pbrd$ad[i];
            resultCA$sw[i] = ((defVe$sw & auxL26) | (~defVe$sw & auxL25));
            defVe$w = lldefVe$w[i];
            resultCA$w[i] = ((defVe$w & (auxL23 >>> 1)) | (~defVe$w & auxL25));
            defVe$nw = lldefVe$nw[i];
            resultCA$nw[i] = ((defVe$nw & tmun06) | (~defVe$nw & auxL25));
            tmun06 = auxL24;
            defVe$ne = lldefVe$ne[i];
            resultCA$ne[i] = ((defVe$ne & tmun07) | (~defVe$ne & auxL25));
            tmun07 = (auxL26 << 1);
        }
    }
}