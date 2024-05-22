package compiledCA;

import compiledMacro.*;
import compiler.Locus;
import scala.collection.immutable.List;
import simulator.CAloops;
import simulator.CAloops2;
import simulator.PrShift;

import java.util.ArrayList;
import java.util.HashMap;

import static simulator.Util.*;

public final class MvCA implements CAloops2 {
    public static void _fun2(PrShift p, int[][] auxC01, int[][] mvBTwoadjblob, int[][] mvBMeete) {
        int[] mvBMeete$h = mvBMeete[0], mvBMeete$d = mvBMeete[1], mvBMeete$ad = mvBMeete[2], auxC01$e = auxC01[0], auxC01$se = auxC01[1], auxC01$sw = auxC01[2], auxC01$w = auxC01[3], auxC01$nw = auxC01[4], auxC01$ne = auxC01[5], mvBTwoadjblob$h = mvBTwoadjblob[0], mvBTwoadjblob$d = mvBTwoadjblob[1], mvBTwoadjblob$ad = mvBTwoadjblob[2];
        p.mirror(auxC01, compiler.Locus.locusVe());
        p.mirror(mvBTwoadjblob, compiler.Locus.locusE());
        p.prepareBit(auxC01);
        p.prepareBit(mvBTwoadjblob)
        ;
// initialisation 
        int tmun08 = 0, tmun09 = 0, tmun10 = 0, tmun11 = 0, tmun12 = 0, tmun13 = 0;
        for (int i = 1; i < auxC01$e.length - 1; i++) {
            mvBMeete$h[i - 1] = (~tmun09 & tmun08);
            tmun09 = ((auxC01$w[i] << 1) | auxC01$e[i]);
            tmun08 = mvBTwoadjblob$h[i];
            mvBMeete$d[i - 1] = (~(tmun11 | auxC01$nw[i]) & tmun10);
            tmun11 = auxC01$se[i];
            tmun10 = mvBTwoadjblob$d[i];
            mvBMeete$ad[i - 1] = (~(tmun13 | (auxC01$ne[i] >>> 1)) & tmun12);
            tmun13 = auxC01$sw[i];
            tmun12 = mvBTwoadjblob$ad[i];
        }
    }

    public static void _fun3(PrShift p, int[][] mvBNbcc, int[] mvBMeeteside, int[] mvBMeet) {
        int[] mvBNbcc$0 = mvBNbcc[0], mvBNbcc$1 = mvBNbcc[1];
        p.mirror(mvBNbcc, compiler.Locus.locusV());
        p.mirror(mvBMeeteside, compiler.Locus.locusV());
        p.prepareBit(mvBNbcc);
        p.prepareBit(mvBMeeteside)
        ;
// initialisation 
        int r0 = 0, r1 = 0, r2 = 0, r3 = 0, r4 = 0;
        for (int i = 1; i < mvBNbcc$0.length - 1; i++) {
            r0 = ~mvBNbcc$0[i];
            r1 = mvBNbcc$1[i];
            r3 = ((r4 = (r2 = r1)) & mvBNbcc$1[i]);
            r3 = (r3 | ((~r4 & (r2 | r0)) & mvBNbcc$0[i]));
            mvBMeet[i] = (r3 | mvBMeeteside[i]);
        }
    }

    public static void _fun0(PrShift p, int[][] mvBrdin, int[][] defVe, int[] auxC00R) {
        int[] mvBrdin$e = mvBrdin[0], mvBrdin$se = mvBrdin[1], mvBrdin$sw = mvBrdin[2], mvBrdin$w = mvBrdin[3], mvBrdin$nw = mvBrdin[4], mvBrdin$ne = mvBrdin[5], defVe$e = defVe[0], defVe$se = defVe[1], defVe$sw = defVe[2], defVe$w = defVe[3], defVe$nw = defVe[4], defVe$ne = defVe[5];
        p.mirror(mvBrdin, compiler.Locus.locusVe());
        p.mirror(defVe, compiler.Locus.locusVe());
        p.prepareBit(mvBrdin);
        p.prepareBit(defVe)
        ;
// initialisation 
        int auxC00 = 0, auxL29 = 0, pdefVe = 0;
        for (int i = 1; i < mvBrdin$e.length - 1; i++) {
            pdefVe = defVe$e[i];
            auxC00 = (pdefVe & mvBrdin$e[i]);
            pdefVe = defVe$se[i];
            auxC00 = (auxC00 | (pdefVe & mvBrdin$se[i]));
            pdefVe = defVe$sw[i];
            auxC00 = (auxC00 | (pdefVe & mvBrdin$sw[i]));
            pdefVe = defVe$w[i];
            auxC00 = (auxC00 | (pdefVe & mvBrdin$w[i]));
            pdefVe = defVe$nw[i];
            auxC00 = (auxC00 | (pdefVe & mvBrdin$nw[i]));
            pdefVe = defVe$ne[i];
            auxC00R[i] = (auxC00 | (pdefVe & mvBrdin$ne[i]));
        }
    }

    public static void _fun1(PrShift p, int[][] auxC03, int[][] defEf, int[] mv, int[][] mvDoubleton) {
        int[] mvDoubleton$h = mvDoubleton[0], mvDoubleton$d = mvDoubleton[1], mvDoubleton$ad = mvDoubleton[2], auxC03$h = auxC03[0], auxC03$d = auxC03[1], auxC03$ad = auxC03[2], defEf$h1 = defEf[0], defEf$h2 = defEf[1], defEf$d1 = defEf[2], defEf$d2 = defEf[3], defEf$ad1 = defEf[4], defEf$ad2 = defEf[5];
        p.mirror(auxC03, compiler.Locus.locusE());
        p.mirror(defEf, compiler.Locus.locusEf());
        p.mirror(mv, compiler.Locus.locusV());
        p.prepareBit(auxC03);
        p.prepareBit(defEf);
        p.prepareBit(mv)
        ;
// initialisation 
        int auxL30 = 0, auxL31 = 0, auxL32 = 0, auxO02 = 0, pdefEf = 0, tmun14 = 0, tmun15 = 0, tmun16 = 0, tmun17 = 0, tmun18 = 0, tmun19 = 0, tmun20 = 0, tmun21 = 0, tmun22 = 0, tmun23 = 0, tmun24 = 0, tmun25 = 0, tmun26 = 0, tmun27 = 0, tmun28 = 0, tmun29 = 0, tmun30 = 0;
        for (int i = 1; i < auxC03$h.length - 1; i++) {
            pdefEf = defEf$h2[i];
            auxL32 = mv[i];
            auxO02 = ((tmun15 & auxL32) | tmun14);
            tmun15 = pdefEf;
            pdefEf = defEf$h1[i];
            mvDoubleton$h[i - 1] = (tmun19 & ~(auxO02 | ((tmun18 & tmun17) | tmun16)));
            tmun19 = auxC03$h[i];
            tmun17 = (auxL31 << 1);
            tmun18 = pdefEf;
            pdefEf = defEf$d1[i];
            auxO02 = ((tmun22 & tmun21) | tmun20);
            tmun21 = (auxL32 << 1);
            tmun22 = pdefEf;
            pdefEf = defEf$d2[i];
            mvDoubleton$d[i - 1] = (tmun25 & ~(auxO02 | ((tmun24 & (auxL32 >>> 1)) | tmun23)));
            tmun24 = pdefEf;
            tmun25 = auxC03$d[i];
            pdefEf = defEf$ad1[i];
            auxO02 = ((tmun27 & auxL32) | tmun26);
            tmun27 = pdefEf;
            pdefEf = defEf$ad2[i];
            mvDoubleton$ad[i - 1] = (tmun30 & ~(auxO02 | ((tmun29 & (auxL31 >>> 1)) | tmun28)));
            tmun30 = auxC03$ad[i];
            tmun29 = pdefEf;
            auxL31 = auxL32;
        }
    }

    public static void _fun6(PrShift p, int[] mv, int[][] defVe, int[] mvSingleton) {
        int[] defVe$e = defVe[0], defVe$se = defVe[1], defVe$sw = defVe[2], defVe$w = defVe[3], defVe$nw = defVe[4], defVe$ne = defVe[5];
        p.mirror(mv, compiler.Locus.locusV());
        p.mirror(defVe, compiler.Locus.locusVe());
        p.prepareBit(mv);
        p.prepareBit(defVe)
        ;
// initialisation 
        int auxL33 = 0, auxL34 = 0, auxL35 = 0, auxO04 = 0, pdefVe = 0, pmv = 0, tmun31 = 0, tmun32 = 0, tmun33 = 0, tmun34 = 0, tmun35 = 0, tmun36 = 0, tmun37 = 0, tmun38 = 0, tmun39 = 0, tmun40 = 0, tmun41 = 0, tmun42 = 0, tmun43 = 0, tmun44 = 0, tmun45 = 0, tmun46 = 0;
        for (int i = 1; i < mv.length - 1; i++) {
            pmv = mv[i];
            pdefVe = defVe$e[i];
            auxL35 = ~pmv;
            auxO04 = ((tmun33 & tmun32) | tmun31);
            tmun33 = pdefVe;
            tmun32 = (auxL35 << 1);
            pdefVe = defVe$se[i];
            auxO04 = (auxO04 & ((tmun35 & auxL35) | tmun34));
            tmun35 = pdefVe;
            pdefVe = defVe$sw[i];
            auxO04 = (auxO04 & ((tmun37 & (auxL35 >>> 1)) | tmun36));
            tmun37 = pdefVe;
            pdefVe = defVe$w[i];
            auxO04 = (auxO04 & ((tmun39 & (auxL34 >>> 1)) | tmun38));
            tmun39 = pdefVe;
            pdefVe = defVe$nw[i];
            auxO04 = (auxO04 & ((tmun42 & tmun41) | tmun40));
            tmun41 = auxL34;
            tmun42 = pdefVe;
            pdefVe = defVe$ne[i];
            mvSingleton[i - 1] = ((auxO04 & ((tmun46 & tmun45) | tmun44)) & tmun43);
            tmun46 = pdefVe;
            tmun45 = (auxL34 << 1);
            tmun43 = pmv;
            auxL34 = auxL35;
        }
    }

    public static void _fun7(PrShift p, int[][] mvBrdin, int[] mvBMeet, int[] mvInvade, int[] mv, int[][] defVe, int[] llmv) {
        int[] mvBrdin$e = mvBrdin[0], mvBrdin$se = mvBrdin[1], mvBrdin$sw = mvBrdin[2], mvBrdin$w = mvBrdin[3], mvBrdin$nw = mvBrdin[4], mvBrdin$ne = mvBrdin[5], defVe$e = defVe[0], defVe$se = defVe[1], defVe$sw = defVe[2], defVe$w = defVe[3], defVe$nw = defVe[4], defVe$ne = defVe[5];
        p.mirror(mvBrdin, compiler.Locus.locusVe());
        p.mirror(mvBMeet, compiler.Locus.locusV());
        p.mirror(mvInvade, compiler.Locus.locusV());
        p.mirror(mv, compiler.Locus.locusV());
        p.mirror(defVe, compiler.Locus.locusVe());
        p.prepareBit(mvBrdin);
        p.prepareBit(mvBMeet);
        p.prepareBit(mvInvade);
        p.prepareBit(mv);
        p.prepareBit(defVe)
        ;
// initialisation 
        int auxL37 = 0, mvBrdv = 0, pdefVe = 0;
        for (int i = 1; i < mvBrdin$e.length - 1; i++) {
            pdefVe = defVe$e[i];
            mvBrdv = (pdefVe & mvBrdin$e[i]);
            pdefVe = defVe$se[i];
            mvBrdv = (mvBrdv | (pdefVe & mvBrdin$se[i]));
            pdefVe = defVe$sw[i];
            mvBrdv = (mvBrdv | (pdefVe & mvBrdin$sw[i]));
            pdefVe = defVe$w[i];
            mvBrdv = (mvBrdv | (pdefVe & mvBrdin$w[i]));
            pdefVe = defVe$nw[i];
            mvBrdv = (mvBrdv | (pdefVe & mvBrdin$nw[i]));
            pdefVe = defVe$ne[i];
            llmv[i] = (mv[i] | (((mvBrdv | (pdefVe & mvBrdin$ne[i])) & ~mvBMeet[i]) & mvInvade[i]));
        }
    }

    public static void _fun4(PrShift p, int[][] mvMPush, int[][] defVe, int[] mvInvadeR) {
        int[] mvMPush$e = mvMPush[0], mvMPush$se = mvMPush[1], mvMPush$sw = mvMPush[2], mvMPush$w = mvMPush[3], mvMPush$nw = mvMPush[4], mvMPush$ne = mvMPush[5], defVe$e = defVe[0], defVe$se = defVe[1], defVe$sw = defVe[2], defVe$w = defVe[3], defVe$nw = defVe[4], defVe$ne = defVe[5];
        p.mirror(mvMPush, compiler.Locus.locusVe());
        p.mirror(defVe, compiler.Locus.locusVe());
        p.prepareBit(mvMPush);
        p.prepareBit(defVe)
        ;
// initialisation 
        int auxL38 = 0, mvInvade = 0, pdefVe = 0, tmun47 = 0, tmun48 = 0, tmun49 = 0, tmun50 = 0, tmun51 = 0, tmun52 = 0, tmun53 = 0, tmun54 = 0, tmun55 = 0, tmun56 = 0, tmun57 = 0, tmun58 = 0, tmun59 = 0, tmun60 = 0, tmun61 = 0, tmun62 = 0, tmun63 = 0, tmun64 = 0;
        for (int i = 1; i < mvMPush$e.length - 1; i++) {
            pdefVe = defVe$e[i];
            mvInvade = ((tmun49 & tmun48) | tmun47);
            tmun49 = pdefVe;
            tmun48 = (mvMPush$w[i] << 1);
            pdefVe = defVe$se[i];
            mvInvade = (mvInvade | ((tmun51 & mvMPush$nw[i]) | tmun50));
            tmun51 = pdefVe;
            pdefVe = defVe$sw[i];
            mvInvade = (mvInvade | ((tmun53 & (mvMPush$ne[i] >>> 1)) | tmun52));
            tmun53 = pdefVe;
            pdefVe = defVe$w[i];
            mvInvade = (mvInvade | ((tmun56 & (tmun55 >>> 1)) | tmun54));
            tmun55 = mvMPush$e[i];
            tmun56 = pdefVe;
            pdefVe = defVe$nw[i];
            mvInvade = (mvInvade | ((tmun60 & tmun58) | tmun57));
            tmun58 = tmun59;
            tmun59 = mvMPush$se[i];
            tmun60 = pdefVe;
            pdefVe = defVe$ne[i];
            mvInvadeR[i - 1] = (mvInvade | ((tmun64 & tmun62) | tmun61));
            tmun62 = (tmun63 << 1);
            tmun63 = mvMPush$sw[i];
            tmun64 = pdefVe;
        }
    }

    public static void _fun5(PrShift p, int[][] mvRaRandside, int[][] mvDoubleton, int[] mvSingleton, int[][] mvRaRanddir, int[][] mvMPush) {
        int[] mvMPush$e = mvMPush[0], mvMPush$se = mvMPush[1], mvMPush$sw = mvMPush[2], mvMPush$w = mvMPush[3], mvMPush$nw = mvMPush[4], mvMPush$ne = mvMPush[5], mvRaRandside$h1 = mvRaRandside[0], mvRaRandside$h2 = mvRaRandside[1], mvRaRandside$d1 = mvRaRandside[2], mvRaRandside$d2 = mvRaRandside[3], mvRaRandside$ad1 = mvRaRandside[4], mvRaRandside$ad2 = mvRaRandside[5], mvDoubleton$h = mvDoubleton[0], mvDoubleton$d = mvDoubleton[1], mvDoubleton$ad = mvDoubleton[2], mvRaRanddir$e = mvRaRanddir[0], mvRaRanddir$se = mvRaRanddir[1], mvRaRanddir$sw = mvRaRanddir[2], mvRaRanddir$w = mvRaRanddir[3], mvRaRanddir$nw = mvRaRanddir[4], mvRaRanddir$ne = mvRaRanddir[5];
        p.mirror(mvRaRandside, compiler.Locus.locusEv());
        p.mirror(mvDoubleton, compiler.Locus.locusE());
        p.mirror(mvSingleton, compiler.Locus.locusV());
        p.mirror(mvRaRanddir, compiler.Locus.locusVe());
        p.prepareBit(mvRaRandside);
        p.prepareBit(mvDoubleton);
        p.prepareBit(mvSingleton);
        p.prepareBit(mvRaRanddir)
        ;
// initialisation 
        int auxL44 = 0, auxL45 = 0, auxL46 = 0, auxL47 = 0, tmun65 = 0, tmun66 = 0;
        for (int i = 1; i < mvRaRandside$h1.length - 1; i++) {
            auxL46 = mvSingleton[i];
            auxL44 = mvDoubleton$d[i];
            mvMPush$e[i] = ((auxL44 & mvRaRandside$d2[i]) | (auxL46 & mvRaRanddir$e[i]));
            auxL45 = mvDoubleton$ad[i];
            mvMPush$se[i] = ((auxL45 & mvRaRandside$ad2[i]) | (auxL46 & mvRaRanddir$se[i]));
            auxL47 = mvDoubleton$h[i];
            mvMPush$sw[i] = (((auxL47 & mvRaRandside$h1[i]) >>> 1) | (auxL46 & mvRaRanddir$sw[i]));
            mvMPush$w[i] = (tmun65 | (auxL46 & mvRaRanddir$w[i]));
            tmun65 = (auxL44 & mvRaRandside$d1[i]);
            mvMPush$nw[i] = (tmun66 | (auxL46 & mvRaRanddir$nw[i]));
            tmun66 = ((auxL45 & mvRaRandside$ad1[i]) << 1);
            mvMPush$ne[i] = ((auxL47 & mvRaRandside$h2[i]) | (auxL46 & mvRaRanddir$ne[i]));
        }
    }

    public int CAmemWidth() {
        return 64;
    }

    @Override
    public ArrayList<String> theLoops(PrShift p, int[][] m) {
        ArrayList<String> bugs = new ArrayList<>();
        int[] auxC00 = m[43], mvRaNext = m[43], mvSingleton = m[30], llmvRa = m[6], llbugV = m[13], mv = m[15], mvBMeeteside = m[44], mvBMeet = m[34], llmv = m[14], mvRa = m[29], mvInvade = m[16];
        int[][] mvBTwoadjblob = new int[][]{m[44], m[45], m[52]}, defVe = new int[][]{m[42], m[41], m[40], m[39], m[38], m[37]}, mvDoubleton = new int[][]{m[31], m[32], m[33]}, mvBNbcc = new int[][]{m[35], m[36]}, lldefVe = new int[][]{m[0], m[1], m[2], m[3], m[4], m[5]}, mvRaRanddir = new int[][]{m[23], m[24], m[25], m[26], m[27], m[28]}, mvBrdin = new int[][]{m[46], m[47], m[48], m[49], m[50], m[51]}, auxC03 = new int[][]{m[55], m[56], m[57]}, auxC01 = new int[][]{m[58], m[59], m[60], m[61], m[62], m[63]}, mvBMeete = new int[][]{m[43], m[53], m[54]}, auxC02 = new int[][]{m[43], m[53], m[54], m[55], m[56], m[57]}, defEf = new int[][]{m[54], m[53], m[52], m[45], m[44], m[43]}, mvMPush = new int[][]{m[17], m[18], m[19], m[20], m[21], m[22]}, lldefEf = new int[][]{m[7], m[8], m[9], m[10], m[11], m[12]}, mvBrd = new int[][]{m[43], m[44], m[45]}, mvRaRandside = new int[][]{m[43], m[44], m[45], m[52], m[53], m[54]};

        copy(lldefVe, defVe);
        copy(llmv, mv);
        redsxorb.ve_1(p, mv, mvBrd);
        topo.brdin_1_1(p, mvBrd, mv, mvBrdin, lldefVe);
        _fun0(p, mvBrdin, defVe, auxC00);
        redsandb.ve_1(p, auxC00, mvBTwoadjblob);
        redT.enlargeEF_1(p, mvBrdin, auxC02);
        redT.enlargeFE_1(p, auxC02, auxC01);
        _fun2(p, auxC01, mvBTwoadjblob, mvBMeete);
        redsorb.ev_1(p, mvBMeete, mvBMeeteside, lldefVe);
        topo.nbcc_1(p, mvBrdin, mvBNbcc);
        _fun3(p, mvBNbcc, mvBMeeteside, mvBMeet);
        show(mvBMeet);
        copy(lldefEf, defEf);
        redsandb.ve_1(p, mv, auxC03);
        _fun1(p, auxC03, defEf, mv, mvDoubleton);
        show(mvDoubleton);
        _fun6(p, mv, defVe, mvSingleton);
        copy(llmvRa, mvRa);
        util.randN12_1(p, mvRa, mvRaRanddir);
        util.randE2_1(p, mvRa, mvRaRandside);
        _fun5(p, mvRaRandside, mvDoubleton, mvSingleton, mvRaRanddir, mvMPush);
        show(mvMPush);
        show(mvSingleton);
        util.rand_1(p, mvRa, mvRaNext);
        memo(mvRaNext, llmvRa);
        show(mvBNbcc);
        _fun4(p, mvMPush, defVe, mvInvade);
        _fun7(p, mvBrdin, mvBMeet, mvInvade, mv, defVe, llmv);
        show(mv);
        show(mvRa);
        show(mvRaRanddir);
        show(mvInvade);
        return bugs;
    }


    @Override
    public HashMap<String, List<Integer>> fieldOffset() {
        HashMap<String, List<Integer>> map = new HashMap<>(); //for layer's initialization and update, as well as displayed fields.
        map.put("mvBTwoadjblob", li(44, 45, 52));
        map.put("mvBNbcc", li(35, 36));
        map.put("llmvRa", li(6));
        map.put("llbugV", li(13));
        map.put("lldefVe", li(0, 1, 2, 3, 4, 5));
        map.put("mvBMeet", li(34));
        map.put("mvRaRanddir", li(23, 24, 25, 26, 27, 28));
        map.put("mvRa", li(29));
        map.put("mvInvade", li(16));
        map.put("mvBMeete", li(43, 53, 54));
        map.put("auxC00", li(43));
        map.put("llmv", li(14));
        map.put("lldefEf", li(7, 8, 9, 10, 11, 12));
        map.put("mvBrd", li(43, 44, 45));
        map.put("mvRaRandside", li(43, 44, 45, 52, 53, 54));
        map.put("mvRaNext", li(43));
        map.put("mvDoubleton", li(31, 32, 33));
        map.put("mv", li(15));
        map.put("mvBMeeteside", li(44));
        map.put("mvBrdin", li(46, 47, 48, 49, 50, 51));
        map.put("auxC03", li(55, 56, 57));
        map.put("auxC01", li(58, 59, 60, 61, 62, 63));
        map.put("auxC02", li(43, 53, 54, 55, 56, 57));
        map.put("mvSingleton", li(30));
        map.put("mvMPush", li(17, 18, 19, 20, 21, 22));
        return (map);
    }

    @Override
    public HashMap<String, Locus> fieldLocus() {
        HashMap<String, Locus> map = new HashMap<>();
        map.put("auxC01", compiler.Locus.locusVe());
        map.put("mvRaNext", compiler.Locus.locusV());
        map.put("mvRa", compiler.Locus.locusV());
        map.put("llmvRa", compiler.Locus.locusV());
        map.put("mvRaRandside", compiler.Locus.locusEv());
        map.put("mvBMeeteside", compiler.Locus.locusV());
        map.put("lldefEf", compiler.Locus.locusEf());
        map.put("mvSingleton", compiler.Locus.locusV());
        map.put("auxC03", compiler.Locus.locusE());
        map.put("mvBTwoadjblob", compiler.Locus.locusE());
        map.put("defEf", compiler.Locus.locusEf());
        map.put("mv", compiler.Locus.locusV());
        map.put("defVe", compiler.Locus.locusVe());
        map.put("mvBMeete", compiler.Locus.locusE());
        map.put("mvRaRanddir", compiler.Locus.locusVe());
        map.put("lldefVe", compiler.Locus.locusVe());
        map.put("mvBrdin", compiler.Locus.locusVe());
        map.put("mvBNbcc", compiler.Locus.locusV());
        map.put("mvBrd", compiler.Locus.locusE());
        map.put("mvBMeet", compiler.Locus.locusV());
        map.put("auxC02", compiler.Locus.locusVf());
        map.put("auxC00", compiler.Locus.locusV());
        map.put("mvDoubleton", compiler.Locus.locusE());
        map.put("mvMPush", compiler.Locus.locusVe());
        map.put("llbugV", compiler.Locus.locusV());
        map.put("llmv", compiler.Locus.locusV());
        map.put("mvInvade", compiler.Locus.locusV());
        return (map);
    }

    @Override
    public HashMap<String, Integer> fieldBitSize() {
        HashMap<String, Integer> map = new HashMap<>();
        map.put("mvBNbcc", 2);
        return (map);
    }

    @Override
    public String displayableLayerHierarchy() {
        return "mv(mvB(mvBNbcc)(mvBMeet))(mvM(mvMPush))(mvDoubleton)(mvSingleton)(mvInvade)(mvRa(mvRaRanddir)).";
    }

    @Override
    public HashMap<String, String> init() {
        HashMap<String, String> map = new HashMap<>();
        map.put("lldefVe", "def");
        map.put("llmvRa", "random");
        map.put("lldefEf", "def");
        map.put("llbugV", "false");
        map.put("llmv", "global");
        return (map);
    }

    @Override
    public int gateCount() {
        return (238);
    }

}
