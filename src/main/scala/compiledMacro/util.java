package compiledMacro;

import simulator.PrShift;

public class util {

    public static void randN12_1(PrShift p, int[] prandNeigh, int[][] resultCA) {
        int[] resultCA$e = resultCA[0], resultCA$se = resultCA[1], resultCA$sw = resultCA[2], resultCA$w = resultCA[3], resultCA$nw = resultCA[4], resultCA$ne = resultCA[5];
        p.mirror(prandNeigh, compiler.Locus.locusV());
        p.prepareBit(prandNeigh)
        ;
// initialisation 
        int auxL00$0 = 0, auxL00$1 = 0, auxL00$2 = 0, auxL00$3 = 0, auxL00$4 = 0, auxL00$5 = 0, auxL00$6 = 0, auxL01$0 = 0, auxL01$1 = 0, auxL01$2 = 0, auxL01$3 = 0, auxL01$4 = 0, auxL01$5 = 0, auxL02$0 = 0, auxL02$1 = 0, auxL02$2 = 0, auxL03 = 0, auxL04 = 0, auxL05 = 0, auxL06 = 0, auxL07 = 0, auxL08 = 0, auxL09 = 0, auxL21 = 0, auxL22 = 0, neighborasInt$0 = 0, neighborasInt$1 = 0, neighborasInt$2 = 0, neighborasInt$3 = 0, neighborasInt$4 = 0, neighborasInt$5 = 0, r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0, r6 = 0, tmun04 = 0, tmun05 = 0;
        for (int i = 1; i < prandNeigh.length - 1; i++) {
            neighborasInt$1 = (auxL22 << 1);
            auxL22 = prandNeigh[i];
            neighborasInt$2 = auxL22;
            neighborasInt$3 = (auxL22 >>> 1);
            neighborasInt$4 = (auxL21 >>> 1);
            neighborasInt$5 = tmun04;
            tmun04 = auxL21;
            neighborasInt$0 = tmun05;
            tmun05 = (auxL21 << 1);
            auxL21 = auxL22;
            r0 = neighborasInt$3;
            auxL03 = r0;
            r0 = neighborasInt$1;
            auxL06 = r0;
            auxL05 = ~auxL06;
            r0 = neighborasInt$2;
            auxL04 = r0;
            r0 = neighborasInt$0;
            auxL08 = r0;
            auxL07 = ~auxL08;
            r0 = (auxL07 & auxL05);
            auxL02$0 = ((r0 & (auxL04 & auxL03)) | (auxL08 & auxL06));
            auxL02$1 = ((r0 & (~auxL04 & auxL03)) | (auxL07 & auxL06));
            auxL02$2 = ((r0 & (auxL04 & ~auxL03)) | (auxL08 & auxL05));
            r0 = neighborasInt$4;
            auxL09 = r0;
            r0 = ~auxL09;
            auxL01$0 = (auxL09 & auxL02$0);
            auxL01$1 = (auxL09 & auxL02$1);
            auxL01$2 = (auxL09 & auxL02$2);
            auxL01$3 = (r0 & auxL02$0);
            auxL01$4 = (r0 & auxL02$1);
            auxL01$5 = (r0 & auxL02$2);
            r0 = neighborasInt$5;
            r5 = (r6 = auxL01$5);
            r3 = (r6 = auxL01$4);
            r1 = (r6 = auxL01$3);
            r4 = (r6 = auxL01$2);
            r2 = auxL01$1;
            r6 = auxL01$0;
            auxL00$0 = (auxL01$0 | (r0 & r2));
            auxL00$1 = (auxL01$1 | (r0 & r4));
            auxL00$2 = (auxL01$2 | (r0 & r1));
            auxL00$3 = (auxL01$3 | (r0 & r3));
            auxL00$4 = (auxL01$4 | (r0 & r5));
            auxL00$5 = auxL01$5;
            auxL00$6 = (r0 & r6);
            r0 = auxL00$0;
            resultCA$e[i - 1] = r0;
            r0 = auxL00$1;
            resultCA$se[i - 1] = r0;
            r0 = auxL00$2;
            resultCA$sw[i - 1] = r0;
            r0 = auxL00$3;
            resultCA$w[i - 1] = r0;
            r0 = auxL00$4;
            resultCA$nw[i - 1] = r0;
            r0 = auxL00$5;
            resultCA$ne[i - 1] = r0;
        }
    }

    public static void rand_1(PrShift p, int[] prandNeigh, int[] randBit) {

        p.mirror(prandNeigh, compiler.Locus.locusV());
        p.prepareBit(prandNeigh)
        ;
// initialisation 
        int auxL19 = 0, auxL20 = 0, neighborasInt$0 = 0, neighborasInt$1 = 0, neighborasInt$2 = 0, neighborasInt$3 = 0, neighborasInt$4 = 0, neighborasInt$5 = 0, r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0, r5 = 0, tmun02 = 0, tmun03 = 0;
        for (int i = 1; i < prandNeigh.length - 1; i++) {
            neighborasInt$1 = (auxL20 << 1);
            auxL20 = prandNeigh[i];
            neighborasInt$2 = auxL20;
            neighborasInt$3 = (auxL20 >>> 1);
            neighborasInt$4 = (auxL19 >>> 1);
            neighborasInt$5 = tmun02;
            tmun02 = auxL19;
            neighborasInt$0 = tmun03;
            tmun03 = (auxL19 << 1);
            auxL19 = auxL20;
            r0 = neighborasInt$3;
            r1 = neighborasInt$5;
            r2 = neighborasInt$1;
            r3 = neighborasInt$2;
            r4 = neighborasInt$4;
            r5 = neighborasInt$0;
            randBit[i - 1] = (((((r5 | r2) | r3) ^ r0) ^ r4) ^ r1);
        }
    }

    public static void randE2_1(PrShift p, int[] prand, int[][] resultCA) {
        int[] resultCA$h1 = resultCA[0], resultCA$h2 = resultCA[1], resultCA$d1 = resultCA[2], resultCA$d2 = resultCA[3], resultCA$ad1 = resultCA[4], resultCA$ad2 = resultCA[5];
        p.mirror(prand, compiler.Locus.locusV());
        p.prepareBit(prand)
        ;
// initialisation 
        int auxL13 = 0, auxL39 = 0, auxL40 = 0;
        for (int i = 1; i < prand.length - 1; i++) {
            auxL13 = ((auxL40 << 1) ^ auxL40);
            auxL40 = prand[i];
            resultCA$h1[i - 1] = auxL13;
            resultCA$h2[i - 1] = ~auxL13;
            auxL13 = (auxL39 ^ auxL40);
            resultCA$d1[i - 1] = auxL13;
            resultCA$d2[i - 1] = ~auxL13;
            auxL13 = (auxL39 ^ (auxL40 >>> 1));
            auxL39 = auxL40;
            resultCA$ad1[i - 1] = auxL13;
            resultCA$ad2[i - 1] = ~auxL13;
        }
    }
}