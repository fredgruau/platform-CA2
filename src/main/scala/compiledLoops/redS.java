package compiledLoops;

import simulator.PrShift;

import static simulator.Util.*;

public class redS {

    /**
     * @param p
     * @param is
     * @param existh
     * @param existd
     * @param existad Computes a boolE true on the neighborhood of the blob
     */
    public static void oldorV2E(PrShift p, int[] is, int[] existh, int[] existd, int[] existad) {
        p.propagate4shift(is); //si on le fait la, pas besoin de repropager pour grow
        int isim1 = 0, isi;
        for (int i = 1; i < is.length; i++) {
            isi = is[i];
            existh[i] = isi | isi << 1;
            existd[i - 1] = isi | isim1; //on stoque directement au bon endroit, via un calcul de rayon
            existad[i - 1] = isi >>> 1 | (isim1); //du fait que on stoque a i-1 on applique un >>>1(isi ^ isim1>>1
            isim1 = isi;
        }
    }

    public static void existE2V_1(PrShift p, int[][] pedge, int[] existVR) {
        int[] pedge$h = pedge[0], pedge$d = pedge[1], pedge$ad = pedge[2];
        p.propagate4shift(pedge$h);
        p.propagate4shift(pedge$d);
        p.propagate4shift(pedge$ad); //si on le fait la, pas besoin de repropager pour grow
        int auxL02, auxL03, auxL01, tmun00 = 0;
        for (int i = 1; i < pedge$h.length; i++) {
            auxL01 = pedge$h[i];
            auxL02 = pedge$d[i];
            auxL03 = pedge$ad[i];
            existVR[i - 1] = (((tmun00 | auxL01) | auxL02) | auxL03) | (auxL01 >>> 1);
            tmun00 = auxL02 | (auxL03 << 1);
        }
    }

    // is a boolV, those do not need to finish by V, and are single array
    public static void orV2E(PrShift p, int[] is, int[][] isE) {
        int[] ish = isE[0], isd = isE[1], isad = isE[2];
        p.propagate4shift(is); //si on le fait la, pas besoin de repropager pour grow
        int isim1 = 0, isi;
        for (int i = 1; i < is.length; i++) {
            isi = is[i];
            ish[i] = isi | isi << 1;
            isd[i - 1] = isi | isim1; //on stoque directement au bon endroit, via un calcul de rayon
            isad[i - 1] = isi >>> 1 | (isim1); //du fait que on stoque a i-1 on applique un >>>1(isi ^ isim1>>1
            isim1 = isi;
        }
    }


    public static void orE2V(PrShift p, int[][] isE, int[] is) {
        //p.propagate4shift(ish,isd,isad); //probably not necessary, how do we compute that?
        int[] ish = isE[0], isd = isE[1], isad = isE[2];
        int pedge$h, pedge$d, pedge$ad, tmun0 = 0; //tmun stores the part of the reduce happening at tminusUn
        for (int i = 1; i < is.length - 1; i++) {
            pedge$h = ish[i];
            pedge$d = isd[i];
            pedge$ad = isad[i]; //we store the Edge component because they are reused two times
            is[i] = tmun0 | (pedge$h & defe[i]) | (pedge$h >>> 1 & defw[i]) | pedge$d & defsw[i] | pedge$ad & defse[i];
            tmun0 = pedge$ad << 1 & defne[i + 1] | pedge$d & defnw[i + 1];//sum before, we add 1 to the index of defne, defnw
        }
    }

    public static void oldorE2V(PrShift p, int[] existh, int[] existd, int[] existad,
                                int[] isN, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        //p.propagate4shift(existh,existd,existad); //probably not necessary
        int pedge$h, pedge$d, pedge$ad, tmun0 = 0; //tmun stores the part of the reduce happening at tminusUn
        for (int i = 1; i < isN.length - 1; i++) {
            pedge$h = existh[i];
            pedge$d = existd[i];
            pedge$ad = existad[i]; //we store the Edge component because they are reused two times
            isN[i] = tmun0 | (pedge$h & defe[i]) | (pedge$h >>> 1 & defw[i]) | pedge$d & defsw[i] | pedge$ad & defse[i];
            tmun0 = pedge$ad << 1 & defne[i + 1] | pedge$d & defnw[i + 1];//sum before, we add 1 to the index of defne, defnw
        }
    }

}
