package simulator;

import compiler.Locus;

/**
 * an object implementing PrShift can do the prior computation needed on the border
 */
public interface PrShift {

    /**
     * preprocessin bit level communication within the CA memory, so that << and >>> need only a shift instead of a rotation
     *
     * @param h int32 CA memory
     */
    public void prepareBit(int[] h);

    public void prepareBit(int[][] h);

    /** does a miror on the border */
    public void mirror(int[][] h, Locus l);

    public void mirror(int[] h, Locus l);

    /** does a torus on the border */
    public void torusify(int[][] h, Locus l);

    public void torusify(int[] h, Locus l);

}

/**  does a prepocessing on the border for either preparing shift, miroring, torusifying*/
abstract class BrdPreProc {
    public abstract void propagateOand31(int[] h);

    /** prepare for shift*/
    public void propagateOand31(int[][] h){
        for(int i=0; i<h.length; i++){propagateOand31(h[i]);}
    };

    /** does a miror on the border */
    public abstract void mirror(int[] h, Locus l);

    public void mirror(int[][] h, Locus l){
        for(int i=0; i<h.length; i++){mirror(h[i],l);}
    };

    /** does a torus on the border */
    public abstract void torusify(int[] h, Locus l);

    public void torusify(int[][] h, Locus l)
    {        for(int i=0; i<h.length; i++){torusify(h[i],l);}
    };

}



