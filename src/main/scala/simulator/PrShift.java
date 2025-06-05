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
    public void prepareBit(int[] h,Locus l){
       if(l==Locus.locusV()) prepareBit(h);
    };
    public abstract void prepareBit(int[] h);

    public void prepareBit(int[][] h){
        for(int i=0; i<h.length; i++){prepareBit(h[i]);}
    };
    /** prepare for shift*/
    public void prepareBit(int[][] h, Locus l){
        for(int i=0; i<h.length; i++){prepareBit(h[i],l);}
    };
    public abstract void mirror(int[] h);
    /** does a miror on the border */
    public  void mirror(int[] h, Locus l){
        if(l==Locus.locusV()) mirror(h);
    };
    /** does a miror on all the bit plane*/
    public void mirror(int[][] h, Locus l){for(int i=0; i<h.length; i++){mirror(h[i],l);}   };
    public void mirror(int[][] h){for(int i=0; i<h.length; i++){mirror(h[i]);}   };

    public void border(int[][] h, Locus l){for(int i=0; i<h.length; i++){border(h[i],l);}   };
    public void border(int[][] h){for(int i=0; i<h.length; i++){border(h[i]);}   };
    public void border(int[] h, Locus l){mirror(h,l); prepareBit(h,l);}
    public void border(int[] h){mirror(h); prepareBit(h);}

    public abstract boolean isMirrorSafe(int[] h);
//todo ecrire une version fast de isMirror pour ensuite pouvoir faire des tests systematique.
    /** does a torus on the border */
    public abstract void torusify(int[] h, Locus l);
    public void torusify(int[][] h, Locus l) { for(int i=0; i<h.length; i++){torusify(h[i],l);}  };



}




