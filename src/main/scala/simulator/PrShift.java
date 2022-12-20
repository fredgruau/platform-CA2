package simulator;

public interface PrShift {
    /**
     * propagates bits on the CA memory, so that << and >>> need not do a rotation.
     *
     * @param h int32 CA memory
     */
    public void propagate4shift(int[] h);
};



