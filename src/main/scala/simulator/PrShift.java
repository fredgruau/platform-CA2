package simulator;
/**
 * ann object implementing PrShift can do the computation needed for horizontal communication
 */
public interface PrShift {

    /**
     * bit level communication within the CA memory, so that << and >>> need only a shift instead of a rotation
     *
     * @param h int32 CA memory
     */
    public void prepareBit(int[] h);

    public void mirror(int[] h);
}



