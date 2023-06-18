package compiledLoops;

import simulator.PrShift;

public class BasicMoves {
    /**
     * should go to the west which is left
     */
    public static void fromE(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int isE = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isE;
            isE = (is[i] << 1) & defe[i];//is lies in the east.
        }
    }

    public static void fromW(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int isW = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isW;
            isW = (is[i] >>> 1) & defw[i];//llis >>> 1 & defw[i] ;//|llis |
        }
    }

    public static void fromNw(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int llistm1 = 0, isNw = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isNw;
            isNw = llistm1 & defnw[i];
            llistm1 = is[i];
        }
    }

    public static void fromNe(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int llistm1 = 0, isNe = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isNe;
            isNe = (llistm1 << 1) & defne[i];
            llistm1 = is[i];
        }
    }

    public static void fromSe(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int isSe = 0, llis = 0, defsetm1 = 0;
        for (int i = 1; i < is.length; i++) {
            llis = is[i];
            isSe = llis & defsetm1;
            is[i - 1] = isSe;
            defsetm1 = defse[i];
        }
    }

    public static void fromSw(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int isSw = 0;
        for (int i = 1; i < is.length; i++) {
            isSw = (is[i] >>> 1) & defsw[i - 1];
            is[i - 1] = isSw;
        }
    }

    /**
     * @param p     how to do the communication implementing rotation
     * @param is    current configuration
     * @param defe  wether east neighbor is defined
     * @param defse wether south-east neighbor is defined
     * @param defsw wether south west neighbor is defined
     * @param defw  wether west neighbor is defined
     * @param defnw wether north west neighbor is defined
     * @param defne wether north east neighbor is defined
     */
    public static void grow(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int llistm1 = 0, llis = 0, isNe = 0, isNw = 0, isE = 0, isW = 0, isSe = 0, defsetm1 = 0, isSw = 0, defswtm1 = 0;
        for (int i = 1; i < is.length; i++) {
            llis = is[i];
            isSe = llis & defsetm1;
            isSw = llis >>> 1 & defswtm1;

            is[i - 1] = isNe | isNw | // last
                    isE | isW | llistm1  //now
                    | isSe | isSw //next
            ;
            isE = (llis << 1) & defe[i];
            isW = (llis >>> 1) & defw[i];
            isNe = (llistm1 << 1) & defne[i];
            isNw = llistm1 & defnw[i];
            defswtm1 = defsw[i];
            defsetm1 = defse[i];
            llistm1 = llis;
        }
    }

    /**
     * @param p
     * @param is
     * @param borderh
     * @param borderd
     * @param borderad Computes a boolE true on the border of the blob
     */
    public static void frontierE(PrShift p, int[] is, int[] borderh, int[] borderd, int[] borderad) {
        p.propagate4shift(is); //si on le fait la, pas besoin de repropager pour grow
        int isim1 = 0, isi;
        for (int i = 1; i < is.length; i++) {
            isi = is[i];
            borderh[i] = isi ^ isi << 1;
            borderd[i - 1] = isi ^ isim1;
            borderad[i - 1] = isi >>> 1 ^ (isim1); //du fait que on stoque a i-1 on applique un >>>1(isi ^ isim1>>1
            isim1 = isi;
        }
    }

    /**
     * @param p
     * @param is
     * @param existh
     * @param existd
     * @param existad Computes a boolE true on the neighborhood of the blob
     */
    public static void existE(PrShift p, int[] is, int[] existh, int[] existd, int[] existad) {
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

    /**
     * @param p
     * @param existh
     * @param existd
     * @param existad
     * @param isN     true on the neighborhood
     *                Computes a boolV true on the neighborhood of an Ebool exist (three components)
     */


    public static void existV(PrShift p, int[] existh, int[] existd, int[] existad,
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


    /**
     * @param p     how to do communication
     * @param is    current configuration
     * @param defe  wether east neighbor is defined
     * @param defse wether south-east neighbor is defined
     * @param defsw wether south west neighbor is defined
     * @param defw  wether west neighbor is defined
     * @param defnw wether north west neighbor is defined
     * @param defne wether north east neighbor is defined
     */
    public static void randBit(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        int llistm1 = 0, llis = 0, isNe = 0, isNw = 0, isE = 0, isW = 0, isSe = 0, defsetm1 = 0, isSw = 0, defswtm1 = 0;
        for (int i = 1; i < is.length; i++) {
            llis = is[i];
            isSe = llis & defsetm1;
            isSw = llis >>> 1 & defswtm1;

            is[i - 1] = isNe ^ isNw ^ isE ^
                    (isW | isSe | isSw)
            ;
            isE = (llis << 1) & defe[i];
            isW = (llis >>> 1) & defw[i];
            isNe = (llistm1 << 1) & defne[i];
            isNw = llistm1 & defnw[i];
            defswtm1 = defsw[i];
            defsetm1 = defse[i];
            llistm1 = llis;
        }
    }
    /** Compute Ev field neighbor of a V field*/
    /**
     * @param p   for communication
     * @param is  Vlayer to be set
     * @param h0  horizontal Ev towards left
     * @param h1  horizontal Ev towards right
     * @param d0  diagonal Ev towards left
     * @param d1  diagonal Ev towards right
     * @param ad0 antidiagonal Ev towards left
     * @param ad1 antidiagonal Ev towards right
     */
    public static void vtoEv(PrShift p, int[] is, int[] h0, int[] h1, int[] d0, int[] d1, int[] ad0, int[] ad1) {
        p.propagate4shift(is);
        int isim1 = 0, isi;
        for (int i = 1; i < is.length; i++) {
            isi = is[i];
            h0[i - 1] = isim1;
            h1[i - 1] = isim1 << 1;
            d0[i - 1] = isim1;
            d1[i - 1] = isi;
            ad0[i - 1] = isim1;
            ad1[i - 1] = isi >>> 1;
            isim1 = isi;
        }

    }

    public static void vtoFv(PrShift p, int[] is, int[] dp, int[] db1, int[] db2, int[] up, int[] ub1, int[] ub2) {
        p.propagate4shift(is);
        int isim1 = 0, isi;
        for (int i = 1; i < is.length; i++) {
            isi = is[i];
            dp[i - 1] = isi;
            db1[i - 1] = isim1 << 1;
            db2[i - 1] = isim1;
            up[i - 1] = isim1;
            ub1[i - 1] = isi >>> 1;
            ub2[i - 1] = isi;
            isim1 = isi;
        }

    }

    public static void etoFe(PrShift p, int[] h, int[] d, int[] ad, int[] db, int[] ds1, int[] ds2, int[] ub, int[] us1, int[] us2) {
        p.propagate4shift(h);
        p.propagate4shift(d);
        p.propagate4shift(ad);
        int hi, di, adi, hitm1 = 0;
        for (int i = 1; i < h.length; i++) {
            hi = h[i];
            di = d[i - 1];
            adi = ad[i - 1];
            db[i - 1] = hitm1;
            ds1[i - 1] = di << 1;
            ds2[i - 1] = adi;
            ub[i - 1] = hi >>> 1;
            us1[i - 1] = di;
            us2[i - 1] = adi;
            hitm1 = hi;
        }
    }


    public static void ftoEf(PrShift p, int[] d, int[] u, int[] h1, int[] h2, int[] d1, int[] d2, int[] ad1, int[] ad2) {
        p.propagate4shift(d);
        p.propagate4shift(u);
        int di, ui, uim1 = 0;
        for (int i = 1; i < d.length; i++) {
            di = d[i];
            ui = u[i];
            h1[i] = uim1 << 1;
            h2[i] = di;
            d1[i] = di;
            d2[i] = ui;
            ad1[i] = ui;
            ad2[i] = di >>> 1;
            uim1 = ui;
        }

    }

    public static void etoVe(PrShift p, int[] h, int[] d, int[] ad, int[] e, int[] se, int[] sw, int[] w, int[] nw, int[] ne) {
        p.propagate4shift(h);
        p.propagate4shift(d);
        p.propagate4shift(ad);
        int hi, di, adi, dim1 = 0, adim1 = 0;
        for (int i = 1; i < h.length; i++) {
            hi = h[i];
            di = d[i];
            adi = ad[i];
            e[i] = hi;
            se[i] = di;
            sw[i] = adi;
            w[i] = hi >>> 1;
            nw[i] = dim1;
            ne[i] = adim1 << 1;
            dim1 = di;
            adim1 = adi;

        }
    }

    public static void ftoVf(PrShift p, int[] d, int[] u, int[] se, int[] s, int[] sw, int[] nw, int[] n, int[] ne) {
        p.propagate4shift(d);
        p.propagate4shift(u);
        int di, ui, dim1 = 0, uim1 = 0;
        for (int i = 1; i < d.length; i++) {
            di = d[i];
            ui = u[i];
            se[i] = di;
            s[i] = ui;
            sw[i] = di >>> 1;
            nw[i] = uim1;
            n[i] = dim1;
            ne[i] = uim1 << 1;
            dim1 = di;
            uim1 = ui;
        }

    }

    /**
     * if we compute a field of radius O, we can simplify the code, we do not need to store at i-1 for example
     */
    public static void fromEradius0(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.propagate4shift(is);
        for (int i = 1; i < is.length; i++) {
            int llis = is[i];
            is[i] = (llis << 1) & defe[i];//llis >>> 1 & defw[i] ;//|llis |
        }
    }
}
