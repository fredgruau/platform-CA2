package compiledLoops;

import simulator.PrShift;

public class BasicMoves {
    public static void fromE(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int isE = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isE;
            isE = (is[i] << 1) & defe[i];//llis >>> 1 & defw[i] ;//|llis |
        }
    }

    public static void fromW(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int isW = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isW;
            isW = (is[i] >>> 1) & defw[i];//llis >>> 1 & defw[i] ;//|llis |
        }
    }

    public static void fromNw(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int llistm1 = 0, isNw = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isNw;
            isNw = llistm1 & defnw[i];
            llistm1 = is[i];
        }
    }

    public static void fromNe(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int llistm1 = 0, isNe = 0;
        for (int i = 1; i < is.length; i++) {
            is[i - 1] = isNe;
            isNe = (llistm1 << 1) & defne[i];
            llistm1 = is[i];
        }
    }

    public static void fromSe(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int isSe = 0, llis = 0, defsetm1 = 0;
        for (int i = 1; i < is.length; i++) {
            llis = is[i];
            isSe = llis & defsetm1;
            is[i - 1] = isSe;
            defsetm1 = defse[i];
        }
    }

    public static void fromSw(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int isSw = 0;
        for (int i = 1; i < is.length; i++) {
            isSw = (is[i] >>> 1) & defsw[i - 1];
            is[i - 1] = isSw;
        }
    }

    public static void grow(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        int llistm1 = 0, llis = 0, isNe = 0, isNw = 0, isE = 0, isW = 0, isSe = 0, defsetm1 = 0, isSw = 0, defswtm1 = 0;
        for (int i = 1; i < is.length; i++) {
            llis = is[i];
            isSe = (llis >>> 1) & defsetm1;
            isSw = llis & defswtm1;
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
     * if we compute a field of radius O, we can simplify the code, we do not need to store at i-1 for example
     */
    public static void fromEradius0(PrShift p, int[] is, int[] defe, int[] defse, int[] defsw, int[] defw, int[] defnw, int[] defne) {
        p.prepareShift(is);
        for (int i = 1; i < is.length; i++) {
            int llis = is[i];
            is[i] = (llis << 1) & defe[i];//llis >>> 1 & defw[i] ;//|llis |
        }
    }
}
