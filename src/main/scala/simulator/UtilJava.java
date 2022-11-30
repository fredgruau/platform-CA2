package simulator;

//static functions
public class UtilJava {

/*

    public static void prepareShift(int nbBlock, int blockSize, int[] h) {
        if (nbBlock > 0) {
            int blockSizeInterleaved = blockSize + 1;
            int nbInt32total = nbBlock * blockSizeInterleaved; //we have to take the interleaved space into account

            // int blockSize=(h.length-1)/nbBlock  -1 ;//remove the -1
            int nbInnerLoop = nbBlock;
            for (int i = 0; i < nbInnerLoop; i++)
                for (int j = i * blockSizeInterleaved; j < (i + 1) * blockSizeInterleaved; j++)
                    propagateBit1and30(h, 1 + j, (1 + j + blockSizeInterleaved) % nbInt32total);

        } else {
            int nbColCA = blockSize; //nbColCA = 6 or 14


            //we now adjust the very last integer. bits start at h[2]
            int nbInt32=(h.length-3);
            if(nbInt32>1)
            {  int shift=nbInt32/2;
                h[1] = (Utility.ror(h[h.length - 2] >>>1,shift,30 )<<1 ) >>> nbColCA;//>>> (nbColCA + 1)+(2);
                h[h.length - 1] = (Utility.rol(h[2]>>>1,shift,30) <<1 ) << nbColCA ;//<< (nbColCA + 1)+(2);// blockSize is nbColCA
            }
            else{
               h[1] = h[2]>>> nbColCA;//(Utility.ror(h[2] >>>1,0,30 )<<1 ) >>> nbColCA;
              // h[3] = h[2]<< nbColCA;
            }


            for (int i = 1; i < h.length; i++)  propagateBit1and30(h, i, i);
        }
        //we need to do inner rotation in h[1] and [h.length-1]

    }

    public static void prepareShiftOld(int nbBlock, int blockSize, int[] h) {
        if (nbBlock > 0) {
            int blockSizeInterleaved = blockSize + 1;
            int nbInt32total = nbBlock * blockSizeInterleaved; //we have to take the interleaved space into account

            // int blockSize=(h.length-1)/nbBlock  -1 ;//remove the -1
            int nbInnerLoop = nbBlock;
            for (int i = 0; i < nbInnerLoop; i++)
                for (int j = i * blockSizeInterleaved; j < (i + 1) * blockSizeInterleaved; j++)
                    propagateBit1and30(h, 1 + j, (1 + j + blockSizeInterleaved) % nbInt32total);

        } else {
            int nbColCA = blockSize; //nbColCA = 6 or 14
            if(nbColCA==6){ //we start by computing  the very first h[1] and very last  h[h.length - 2] integer. normal bits start at h[2]
               int nbLignes=4*(h.length-3);
               int shift=nbLignes/2;
                h[h.length - 1] = ror6(h[2],shift) ;// blockSize is nbColCA
                h[1] = rol6(h[h.length - 2], shift) ;
                for (int i = 1; i < h.length; i++)  propagateBit6and1(h, i);
            }


        }
        //we need to do inner rotation in h[1] and [h.length-1]

    }
*/

    final static int maskRight = (1 << 31) - 1;  // 0|1111111111111111111111111111111
    final static int maskLeft = maskRight << 1;    // 1111111111111111111111111111111|0

    public static void propagateBit1and30(int[] h, int i1, int i2) { //we can have i1==i2
        int bitLeft = h[i1] & 2;
        int bitRight = h[i2] & (1 << 30);
        h[i2] = h[i2] & maskRight | bitLeft << 30;
        h[i1] = h[i1] & maskLeft | bitRight >>> 30;
    }

    final static int bitMask8 = 0x01010101;
    final static int maskRight8 = ~bitMask8;
    final static int maskLeft8 = ~(0x01010101 << 7);
    final static int maskRor8 = bitMask8 << 1;
    final static int maskRol8 = bitMask8 << 6;

    public static void propagateBit6and1(int[] h, int i) {
        int bitLeft = h[i] & maskRol8;
        int bitRight = h[i] & maskRor8;
        h[i] = h[i] & maskRight8 | bitLeft >>> 6;
        h[i] = h[i] & maskLeft8 | bitRight << 6;
    }
/*
   public static int ror6(int v, int shift){ //careful, we  rotate on  6 bits, not 16
            for(int j=0; j<shift; j++)
               v=(v& maskRor16)<<6 | (v&(~maskRol16))>>>1;
            return v;
        }
    public static int rol6(int v, int shift){
            for(int j=0; j<shift; j++)
                v=(v& maskRol16)>>>6 | (v&(~maskRor16))<<1;
            return v;
        }*/

    final static int bitMask16 = 0x00010001;
    final static int maskRight16 = ~bitMask16;
    final static int maskLeft16 = ~(bitMask16 << 15);
    final static int maskRor16 = bitMask16 << 1;
    final static int maskRol16 = bitMask16 << 14;


    public static void propagateBit14and1(int[] h, int i) {
        int bitLeft = h[i] & maskRol16;
        int bitRight = h[i] & maskRor16;
        h[i] = h[i] & maskRight16 | bitLeft >>> 14;
        h[i] = h[i] & maskLeft16 | bitRight << 14;
    }

}
