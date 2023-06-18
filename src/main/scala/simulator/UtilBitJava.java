package simulator;

import java.util.HashMap;

/**
 * static functions used for bit manipulation
 */
public class UtilBitJava {
    /** mask(i) is true for the index of the bits that should be set through propagation from the right */
    public final static HashMap<Integer, Integer> mask = new HashMap<>();

    static {
        mask.put(new Integer(6), new Integer(0x01010101));
        mask.put(new Integer(8), new Integer(1 | 1 << 10 | 1 << 20));  //0x00100801)  0b00000000000100000000010000000001
        mask.put(new Integer(14), new Integer(0x00010001));
        mask.put(new Integer(32), new Integer(0x00000001));
    }

    final static int maskRight = (1 << 31) - 1;  // 0|1111111111111111111111111111111
    final static int maskLeft = maskRight << 1;    // 1111111111111111111111111111111|0

    /**
     * @param h  int32 memory
     * @param i1 index of the int giving its bit 1
     * @param i2 index of the other int giving its bit 30, we can have i1==i2 when nbColCA=30
     */
    public static void propagateBit1and30(int[] h, int i1, int i2) {
        int bitLeft = h[i1] & 2;
        int bitRight = h[i2] & (1 << 30);
        h[i2] = h[i2] & maskRight | bitLeft << 30;
        h[i1] = h[i1] & maskLeft | bitRight >>> 30;
    }

    final static int bitMask8 = 0x01010101;
    final static int maskRight8 = ~bitMask8;
    final static int maskLeft8 = ~(bitMask8 << 7);
    final static int maskRor8 = bitMask8 << 1;
    final static int maskRol8 = bitMask8 << 6;

    /**
     * nbColCA=6, each line of 6 bits from 1 to 6 has two empty bit slots: bit 0 and bit7
     * which are filled before the loop, in a toroidal way, using bit 6 and bit 1
     * this holds for the four lines stored in one int32
     * @param h CAmemory encoded in int32 bits
     * @param i index of cell where propagation takes place
     */
    public static void propagateBit6and1(int[] h, int i) {
        int bitLeft = h[i] & maskRol8;
        int bitRight = h[i] & maskRor8;
        h[i] = h[i] & maskRight8 | bitLeft >>> 6;
        h[i] = h[i] & maskLeft8 | bitRight << 6;
    }

    /**
     * progagates in a generic way when supplied the appropriate mask
     *
     * @param v           integer containing multiple lines
     * @param nbCol       number of colomns in the CA
     * @param bitMaskx(i) is true for the index of the bits that should be set through propagation from the right
     * @return
     */
    public static int propagateBitxand1(int v, int nbCol, int bitMaskx) {
        int bitLeft = v & bitMaskx << nbCol;
        int bitRight = v & bitMaskx << 1;
        v = v & ~bitMaskx | bitLeft >>> nbCol;
        v = v & ~(bitMaskx << nbCol + 1) | bitRight << nbCol;
        return v;
    }

    final static int bitMask16 = 0x00010001;
    final static int maskRight16 = ~bitMask16;
    final static int maskLeft16 = ~(bitMask16 << 15);
    final static int maskRor16 = bitMask16 << 1;
    final static int maskRol16 = bitMask16 << 14;

    /**
     * nbColCA=14, each line of 14 bits from 1 to 14 has two empty bit slots: bit 0 and bit 14
     * which are filled before the loop, in a toroidal way, using bit 13 and bit 1
     * this holds for the two lines stored in one int32
     *
     * @param h CAmemory encoded in int32 bits
     * @param i index of cell where propagation takes place
     */
    public static void propagateBit14and1(int[] h, int i) {
        int bitLeft = h[i] & maskRol16;
        int bitRight = h[i] & maskRor16;
        h[i] = h[i] & maskRight16 | bitLeft >>> 14;
        h[i] = h[i] & maskLeft16 | bitRight << 14;
    }


}
