package simulator;

import compiler.Locus;

/**
 * an object implementing PrShift can do the prior computation needed on the border
 */
public abstract class PrShift {
    /**
     * preprocessin bit level communication within the CA memory, so that << and >>> need only a shift instead of a rotation
     * will also propose miroring and torusifying
     *  we decided to use an abstract class rather than an interface, so that we can write those processing
     *  for 2D arrays, by doing it on each component
     * @param h int32 CA memory
     *  instances of this class are passed to the CA main loop, in order for the CA to be able to do a callback.
     */

    public abstract void prepareBit(int[] h);
    /** prepare for shift IntV or BoolE, BoolF*/
    public void prepareBit(int[][] h){
        for(int i=0; i<h.length; i++){prepareBit(h[i]);}
    };

    /** does a miror on all the bit plane, we plan to abandon passing the locus */
    public void mirror(int[][] h){for(int i=0; i<h.length; i++){mirror(h[i]);}   };
    /** does a miror on the border */


    public abstract void mirror(int[] h);


    public void border(int[] h){ mirror(h);prepareBit(h);}
    public void border(int[][] h){for(int i=0; i<h.length; i++){border(h[i]);}   };


    public abstract boolean isMirrorSafe(int[] h);
//todo ecrire une version fast de isMirror pour ensuite pouvoir faire des tests systematique.
    /** does a torus on the border */
    public abstract void torusify(int[] h);
    public void torusify(int[][] h) { for(int i=0; i<h.length; i++){torusify(h[i]);}  };
}




