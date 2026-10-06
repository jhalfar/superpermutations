/* segins_kern.cu - the GPU kernel of segins_gpu.c (option --or3-gpu): the exact gain of a candidate of segment
   insertion, as o3_gain computes it on the host, one thread block per candidate.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   The method.  A candidate is the blocks of the sequence in their new order.  The first block keeps its costs
   (fw).  From each new join on, the dynamic programme runs through the block that follows, one layer per piece,
   until the costs of a piece's cuts are again what they were; the last block needs its first piece only (bw says
   what follows) unless fwd is set.  A layer: mv[j] = min(h, min over the cuts i of the piece before of
   rel[i] + h - overlap(E[i], S[j])) + D[j]; costs are kept relative to their minimum, h standing for h or more.
   As on the host the overlaps of length k = h .. 4 are found with a hash table of the cheapest cut for every
   k-suffix (one table per block, used again for every k through a generation number), and k = 3, 2, 1 with tables
   indexed by the word.

   The cuts of a piece are ALL the cuts of its trail, in the order of the host's table OP; a cut the piece may not
   take (a skip that is not its own) has fw = bw = 255 and never takes part.  A piece with one cut only (a
   segment, a fixed piece) has a slot of its own behind the last cut.  A candidate without blocks (cand[0] = 0)
   asks for the value V of one join (cand[1] -> cand[2]) instead.

   How the block works.
   * The first warp of a block is its driver.  It alone walks the candidate: takes it from the queue, looks joins up
     in the memo, and computes the layers of small pieces itself (32 threads, no barrier for the whole block).  The
     other warps wait at one barrier and are woken only for a layer of a big piece (pool + piece above g.small
     cuts), which all 1024 threads compute.
   * In front of the hash table of a level stands a bitmap in shared memory (one bit per hash value of a word that
     was put): a lookup whose bit is not set cannot be in the table and does not touch global memory.  Two bitmaps
     take turns, so the one of the next level is cleared while the present one is read.  On the words I profiled 93
     percent of the lookups found nothing.
   * The tables for overlaps of 3, 2 and 1 symbols are bit sets (one per cost) of 401 words.
   * A join taken from the memo counts with the length of its chain in "most layers after one join" (the host uses
     that figure for --or3-long), so the figure does not depend on which block computed the chain.
   * A launch ends for all blocks when the first block has spent its budget (the block writes the launch number
     into ctl[2], the others see it before their next layer), so no block waits for a slower one, and a call may
     hold a whole batch of candidates.  Every block writes down where it is and the next launch goes on from there.
     The budget counts cuts of layers plus a fixed part per layer, lookup and candidate.

   Build (CUDA toolkit; needed only for this step, the program loads the driver library at run time):
     nvcc -arch=sm_120 -ptx -o segins_kern.raw.ptx segins_kern.cu
     awk '/^\.visible \.entry or_judge\(/ { e = 1 } e && /^\{/ { print ".maxnreg 56"; e = 0 } { print }' \
         segins_kern.raw.ptx > segins_kern.ptx
   or `bash mkptx.sh`, which does this for both kernels of this directory.  The second step writes one line into
   the PTX file: it limits the kernel to 56 registers per thread, so that a block of 1024 threads fits one
   multiprocessor (65,536 registers) whatever the compiler would use.  The compiler's own option for this
   (-maxrregcount) gives other code and is not what I ran.
   -arch names the card generation: sm_120 is the RTX 50 series, the only one I tested.  -DOG_H=9 (n = 12) builds
   a kernel with h as a constant; it was not faster.

   Where the parts start.  The structure shared with the host and the constants; the hash table (og_put, og_get) and
   the memo (og_memo_get, og_memo_put); og_layer, one layer of the dynamic programme; or_judge, the kernel. */
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
typedef unsigned char u8;
struct OG { /* as OGDev on the host */
    const u32 *oS, *oE;
    const u8 *oSh, *oEh;
    const signed char *oD; /* all cuts: start word, end word (low 32 bits, bits above), cost */
    const u8 *fw, *bw;     /* this round: cost of every cut from the front and from the back, 255: not allowed */
    const u64 *evb;
    const u32 *evm;
    const i64 *fmin, *gmin; /* this round: first cut and number of cuts of every event, minima */
    const int *cand;
    i64 *out; /* candidates: 16 ints each (stretches, first and last event of each); results: 12 words each */
    u64 *ht;
    u8 *scr;
    u32 *gen;
    u32 *ctl;
    int *
        sav; /* per block: hash table, three byte tables, generation, state; ctl[0]: next candidate, ctl[1]: candidates done, ctl[2]: the launch that is over */
    u64 *memo; /* the joins already known (as O3Memo on the host): pairs (key, value), key 0: free */
    i64 N, ncand, htslots, scrsz, maxlay, budget, memomask;
    int h, fwd;
    u64 *stat;
    int small,
        epoch; /* small: a layer of at most that many cuts (pool + event) is the driver's; epoch: number of this launch */
};
#define OG_GMAX 0xFFF00u
#define OG_BAD (-(1LL << 40))
#define OG_SAVW 64
#define OG_BIG (1 << 20)
#ifndef OG_BMBITS
#define OG_BMBITS 17 /* bits of one bitmap */
#endif
#define OG_BMW (1 << (OG_BMBITS - 5))
#define OG_DTW \
    401 /* 3 x 128 words (three symbols, cost 0, 1, 2), 2 x 8 (two symbols, cost 0, 1), 1 (one symbol, cost 0) */
#ifdef OG_H
#define OGH OG_H /* a kernel for one n: h is a constant */
#else
#define OGH g.h
#endif
/* what a step costs in units of the budget (one unit: one cut of a layer computed by the whole block) */
#define OG_WLAYER 64
#define OG_WSMALL 12 /* an cut of a layer computed by the driver alone */
#define OG_WSTEP 256 /* a candidate taken, a memo lookup */

/* Hash of a word: its top `bits` bits after a multiplication. */
__device__ __forceinline__ u64 og_hash(u64 w, int bits) {
    return (w * 0x9E3779B97F4A7C15ULL) >> (64 - bits);
}
/* slot: generation (20 bits), word (40 bits), cost (4 bits); a slot of another generation is free */
__device__ __forceinline__ void og_put(u64 *ht, u64 mask, int bits, u64 gen, u64 w, u32 r) {
    const u64 kg = (gen << 44) | (w << 4);
    u64 i = og_hash(w, bits);
    for (;;) {
        u64 cur = ht[i];
        for (;;) {
            if ((cur >> 4) == (kg >> 4)) {
                if ((cur & 15) > r)
                    atomicMin(&ht[i], kg | r);
                return;
            }
            if ((cur >> 44) == gen)
                break; /* another word of this level: the next slot */
            u64 old = atomicCAS(&ht[i], cur, kg | r);
            if (old == cur)
                return;
            cur = old;
        }
        i = (i + 1) & mask;
    }
}
/* The cost stored for word w in this generation, or -1 if the word is not in the table. */
__device__ __forceinline__ int og_get(const u64 *ht, u64 mask, int bits, u64 gen, u64 w) {
    const u64 kg = ((gen << 44) | (w << 4)) >> 4;
    for (u64 i = og_hash(w, bits);; i = (i + 1) & mask) {
        u64 cur = ht[i];
        if ((cur >> 4) == kg)
            return (int)(cur & 15);
        if ((cur >> 44) != gen)
            return -1;
    }
}
/* the memo of joins already known, shared by the blocks */
__device__ __forceinline__ int og_memo_get(const OG &g, u64 key, i64 *zr, i64 *mc) {
    u64 i = og_hash(key, 40) & (u64)g.memomask;
    for (int p = 0; p < 64; p++, i = (i + 1) & (u64)g.memomask) {
        const u64 k = g.memo[2 * i];
        if (k == key) {
            const u64 v = g.memo[2 * i + 1];
            if (!(v >> 63))
                return 0;
            *zr = (i64)((v >> 32) & 0x7FFFFFFFu);
            *mc = (i64)(v & 0xFFFFFFFFu);
            return 1;
        }
        if (!k)
            return 0;
    }
    return 0;
}
/* Stores what follows a join (zone length zr, cost mc) under its key, unless another block has done so. */
__device__ __forceinline__ void og_memo_put(const OG &g, u64 key, i64 zr, i64 mc) {
    if (mc < 0 || mc > 0xFFFFFFFFLL)
        return;
    const u64 v = (1ULL << 63) | ((u64)zr << 32) | (u64)mc;
    u64 i = og_hash(key, 40) & (u64)g.memomask;
    for (int p = 0; p < 64; p++, i = (i + 1) & (u64)g.memomask) {
        u64 k = g.memo[2 * i];
        if (!k) {
            k = atomicCAS(&g.memo[2 * i], 0ULL, key);
            if (!k) {
                atomicExch(&g.memo[2 * i + 1], v);
                return;
            }
        }
        if (k == key)
            return; /* another block has it (the value is the same) */
    }
}
/* A barrier for the warp (W = 1) or for the whole block (W = 0). */
template <int W> __device__ __forceinline__ void og_sync() {
    if (W)
        __syncwarp();
    else
        __syncthreads();
}
/* Bit i of a bitmap. */
__device__ __forceinline__ int og_bit(const u32 *b, u32 i) {
    return (b[i >> 5] >> (i & 31)) & 1;
}

/* One layer: the m cuts from zb after the pm cuts from pb whose costs are PT (pm = 0: nothing before), by the
   BT threads tid = 0 .. BT-1 (W = 0: the whole block, barriers; W = 1: the 32 threads of the first warp).
   mode 0: their costs relative to the minimum go to NT, *s_neq says whether they differ from fw; mode 1: only the
   minimum of cost + bw.  The minimum is left in *s_min.  The levels use the generations gen0 + 1 .. gen0 + h - 3. */
template <int W>
__device__ __forceinline__ void og_layer(const OG &g, const int tid, const int BT, u64 *ht, const u32 gen0, u8 *MV,
                                         const u8 *PT, const u64 pb, const int pm, const u64 zb, const int m, u8 *NT,
                                         const int mode, u32 *dt, u32 *bm, int *s_min, int *s_neq) {
    const int h = OGH;
    const u8 *FW = g.fw + zb;
    for (int j = tid; j < m; j += BT)
        MV[j] = FW[j] == 255 ? 255 : (u8)(pm ? h : 0);
    for (int q = tid; q < OG_DTW; q += BT)
        dt[q] = 0;
    if (!W)
        for (int q = tid; q < OG_BMW; q += BT)
            bm[q] = 0;
    if (tid == 0) {
        *s_min = OG_BIG;
        *s_neq = 0;
    }
    og_sync<W>();
    if (pm) {
        int bits = 4;
        while ((1 << bits) < 2 * pm)
            bits++;
        const u64 mask = (1ULL << bits) - 1;
        u32 gen = gen0;
        for (int k = h, lv = 0; k >= 4; k--, lv++) {
            gen++;
            const u64 km = (1ULL << (4 * k)) - 1;
            const int sh = 4 * (h - k);
            u32 *bx = bm + (lv & 1) * OG_BMW, *by = bm + ((lv + 1) & 1) * OG_BMW;
            for (int i = tid; i < pm; i += BT) {
                const u32 r = PT[i];
#ifdef OG_UNC /* the word is read whether it is needed or not: its loads do not wait for the cost */
                const u32 e = ((const volatile u32 *)g.oE)[pb + i];
                const u64 eh = ((const volatile u8 *)g.oEh)[pb + i];
                if (r < (u32)k) {
                    const u64 w = (e | (eh << 32)) & km;
#else
                if (r < (u32)k) {
                    const u32 e = g.oE[pb + i];
                    const u64 w = (e | ((u64)g.oEh[pb + i] << 32)) & km;
#endif
                    og_put(ht, mask, bits, gen, w, r);
                    if (!W) {
                        const u32 hb = (u32)og_hash(w, OG_BMBITS);
                        atomicOr(&bx[hb >> 5], 1u << (hb & 31));
                    }
                    if (k == 4 && r < 3) { /* overlaps of 3, 2, 1 symbols: bit sets by cost */
                        atomicOr(&dt[r * 128 + ((e & 4095) >> 5)], 1u << (e & 31));
                        if (r < 2)
                            atomicOr(&dt[384 + r * 8 + ((e & 255) >> 5)], 1u << (e & 31));
                        if (r < 1)
                            atomicOr(&dt[400], 1u << (e & 15));
                    }
                }
            }
            og_sync<W>();
            if (!W && k > 4)
                for (int q = tid; q < OG_BMW; q += BT)
                    by[q] = 0; /* the bitmap of the next level: nobody reads it now */
            for (int j = tid; j < m; j += BT) {
#ifdef OG_UNC
                const int mv = MV[j];
                const u32 sl = ((const volatile u32 *)g.oS)[zb + j];
                const u64 su = ((const volatile u8 *)g.oSh)[zb + j];
                if (mv == 255 || mv <= h - k)
                    continue;
                const u64 w = (sl | (su << 32)) >> sh;
#else
                const int mv = MV[j];
                if (mv == 255 || mv <= h - k)
                    continue;
                const u64 w = (g.oS[zb + j] | ((u64)g.oSh[zb + j] << 32)) >> sh;
#endif
                if (!W) {
                    const u32 hb = (u32)og_hash(w, OG_BMBITS);
                    if (!og_bit(bx, hb))
                        continue;
                }
                const int v = og_get(ht, mask, bits, gen, w);
                if (v >= 0 && v + h - k < mv)
                    MV[j] = (u8)(v + h - k);
            }
            og_sync<W>();
        }
    }
    int lmin = OG_BIG;
    const int s3 = 4 * (h - 3), s2 = 4 * (h - 2), s1 = 4 * (h - 1);
    for (int j = tid; j < m; j += BT) {
        int mv = MV[j];
        if (mv == 255)
            continue;
        if (pm && mv > h - 3) {
            const u64 S = g.oS[zb + j] | ((u64)g.oSh[zb + j] << 32);
            const u32 k3 = (u32)(S >> s3);
            int v = og_bit(dt, k3) ? 0 : og_bit(dt + 128, k3) ? 1 : og_bit(dt + 256, k3) ? 2 : 255;
            if (v + h - 3 < mv)
                mv = v + h - 3;
            if (mv > h - 2) {
                const u32 k2 = (u32)(S >> s2);
                v = og_bit(dt + 384, k2) ? 0 : og_bit(dt + 392, k2) ? 1 : 255;
                if (v + h - 2 < mv)
                    mv = v + h - 2;
                if (mv == h && ((dt[400] >> (u32)(S >> s1)) & 1))
                    mv = h - 1;
            }
            MV[j] = (u8)mv;
        }
        const int t = mv + (mode ? (int)g.bw[zb + j] : (int)g.oD[zb + j]);
        if (t < lmin)
            lmin = t;
    }
    if (lmin < OG_BIG)
        atomicMin(s_min, lmin);
    og_sync<W>();
    if (mode)
        return;
    const int mn = *s_min;
    int neq = 0;
    for (int j = tid; j < m; j += BT) {
        const int mv = MV[j];
        u8 t = 255;
        if (mv != 255) {
            const int x = mv + (int)g.oD[zb + j] - mn;
            t = (u8)(x < h ? x : h);
        }
        NT[j] = t;
        if (t != FW[j])
            neq = 1;
    }
    if (neq)
        *s_neq = 1;
    og_sync<W>();
}

/* state of a block between launches (sav, OG_SAVW ints; only the driver has it): 0 active, 1 candidate, 2 stretch j, 3 in a chain, 4 event z, 5 pe,
   6 where the pool's costs are (0: fw, 1: TA, 2: TB), 7 layers of this chain, 8 zones used, 9 current zone, 10 most layers after a join, 11 layers,
   12 joins, 13..14 tot, 15 the chain began with old costs, 16..33 zones (zx, zl, zh), 34..35 cost of the chain so far, 36 joins from the memo.
   The generation of the hash table is in g.gen. */
extern "C" __global__ void or_judge(OG g) {
    __shared__ u32 dt[OG_DTW];
    __shared__ u32 bm[2 * OG_BMW];
    __shared__ int s_c, s_min, s_neq, s_hit, s_task, s_stop, s_pm, s_m, s_ptk, s_ntk, s_mode;
    __shared__ u32 s_gen;
    __shared__ i64 s_zr, s_mc;
    __shared__ u64 s_pb, s_zb;
    const int tid = threadIdx.x, BT = blockDim.x, drv = tid < 32, h = OGH;
    const u64 B = blockIdx.x;
    u64 *ht = g.ht + B * (u64)g.htslots;
    u8 *MV = g.scr + B * 3 * (u64)g.scrsz, *TA = MV + g.scrsz, *TB = TA + g.scrsz;
    int *sv = g.sav + B * OG_SAVW;
    /* the driver's state (the other warps never look at it) */
    u32 gen = 0;
    i64 work = 0;
    int act = 0, j = 0, inch = 0, ptk = 0, nl = 0, nz = 0, zi = 0, nlmax = 0, nltot = 0, njoin = 0, ccl = 0, nmemo = 0,
        pend = 0;
    i64 c = 0, z = 0, pe = -1, tot = 0, cum = 0, llo = 0;
    u64 lkey = 0;
    int lclean = 0;
    int zn[18];
    u64 lpb = 0, lzb = 0;
    int lpm = 0, lm = 0, lptk = 0, lntk = 0, lmode = 0; /* the layer asked for */
    if (drv) {
        gen = g.gen[B];
        act = sv[0];
        c = sv[1];
        j = sv[2];
        inch = sv[3];
        z = sv[4];
        pe = sv[5];
        ptk = sv[6];
        nl = sv[7];
        nz = sv[8];
        zi = sv[9];
        nlmax = sv[10];
        nltot = sv[11];
        njoin = sv[12];
        tot = (i64)(((u64)(u32)sv[13]) | ((u64)(u32)sv[14] << 32));
        ccl = sv[15];
        cum = (i64)(((u64)(u32)sv[34]) | ((u64)(u32)sv[35] << 32));
        nmemo = sv[36];
        for (int q = 0; q < 18; q++)
            zn[q] = sv[16 + q];
        __syncwarp();
    }
    for (;;) {
        if (drv) {
            int need = 0;
            for (;;) {
                if (pend) { /* the layer asked for is done: its minimum, and whether the costs changed */
                    const int mn = s_min, neq = s_neq;
                    __syncwarp();
                    work += (lm + lpm <= g.small ? (i64)OG_WSMALL * (lm + lpm) : (i64)(lm + lpm)) + OG_WLAYER;
                    gen += h - 3;
                    const int *cd = g.cand + 16 * c;
                    int fin = 0;
                    i64 res = 0;
                    if (pend == 1) { /* the value of a join */
                        if (tid == 0) {
                            g.out[12 * c] = mn < h ? mn : h;
                            atomicAdd(g.ctl + 1, 1u);
                        }
                        act = 0;
                    } else if (pend == 2) { /* the last stretch: bw says what follows */
                        nltot++;
                        if (lclean && g.memomask && tid == 0)
                            og_memo_put(g, lkey, llo, mn);
                        res = g.fmin[g.N - 1] - (tot + mn + g.gmin[llo]);
                        fin = 1;
                    } else { /* a layer of a chain */
                        const i64 hi = cd[8 + j];
                        int end = 0;
                        tot += mn;
                        cum += mn;
                        nl++;
                        zn[12 + zi] = (int)z;
                        if (!neq) {
                            if (ccl && g.memomask && tid == 0)
                                og_memo_put(g, ((u64)(zn[zi] + 1) << 24) | (u64)zn[6 + zi], z, cum);
                            tot += g.fmin[hi] - g.fmin[z];
                            ptk = 0;
                            pe = hi;
                            end = 1;
                        } else {
                            ptk = lntk == 0 ? 1 : 2;
                            pe = z;
                            if (z == hi)
                                end = 1;
                            else if (nl >= g.maxlay)
                                end = 2;
                        }
                        if (end) {
                            if (nl > nlmax)
                                nlmax = nl;
                            nltot += nl;
                            inch = 0;
                            j++;
                            if (end == 2)
                                fin = 2;
                        } else
                            z++;
                    }
                    if (fin) {
                        if (tid == 0) {
                            i64 *o = g.out + 12 * c;
                            o[0] = fin == 2 ? OG_BAD : res;
                            o[1] = (i64)(((u64)(u32)nltot) | ((u64)(u32)nlmax << 32));
                            o[2] = (i64)(((u64)(u32)njoin) | ((u64)(u32)nmemo << 32));
                            for (int q = 0; q < 9; q++)
                                o[3 + q] = (i64)(((u64)(u32)zn[2 * q]) | ((u64)(u32)zn[2 * q + 1] << 32));
                            atomicAdd(g.ctl + 1, 1u);
                        }
                        act = 0;
                    }
                    pend = 0;
                    continue;
                }
                /* is the launch over?  (this block's budget, or another block's) */
                if (tid == 0) {
                    int st = work >= g.budget;
                    if (st)
                        g.ctl[2] = (u32)g.epoch;
                    else
                        st = g.ctl[2] == (u32)g.epoch;
                    s_stop = st;
                }
                __syncwarp();
                const int stop = s_stop;
                __syncwarp();
                if (stop)
                    break;
                int req = 0;
                if (!act) {
                    if (tid == 0)
                        s_c = (int)atomicAdd(g.ctl, 1u);
                    __syncwarp();
                    c = s_c;
                    __syncwarp();
                    if (c >= g.ncand)
                        break;
                    work += OG_WSTEP;
                    act = 1;
                    j = 0;
                    inch = 0;
                    ptk = 0;
                    nl = 0;
                    nz = 0;
                    zi = 0;
                    nlmax = 0;
                    nltot = 0;
                    njoin = 0;
                    pe = -1;
                    tot = 0;
                    z = 0;
                    ccl = 0;
                    cum = 0;
                    nmemo = 0;
                    for (int q = 0; q < 6; q++) {
                        zn[q] = zn[6 + q] = 0;
                        zn[12 + q] = -1;
                    }
                    const int *cd = g.cand + 16 * c;
                    if (cd[0] == 0) { /* V of the join x -> y from the tables, as o3_exactv on the host */
                        const i64 x = cd[1], y = cd[2];
                        lptk = 0;
                        lpb = g.evb[x];
                        lpm = (int)g.evm[x];
                        lzb = g.evb[y];
                        lm = (int)g.evm[y];
                        lntk = 2;
                        lmode = 1;
                        pend = 1;
                        req = 1;
                    } else {
                        if (cd[8] >= cd[1]) {
                            tot = g.fmin[cd[8]];
                            pe = cd[8];
                        }
                        j = 1;
                        continue;
                    }
                } else if (!inch) { /* the next stretch that is not empty */
                    const int *cd = g.cand + 16 * c;
                    const int ns = cd[0];
                    while (j < ns && cd[8 + j] < cd[1 + j])
                        j++;
                    if (j >= ns) { /* done: nothing after the last join */
                        if (tid == 0) {
                            i64 *o = g.out + 12 * c;
                            o[0] = g.fmin[g.N - 1] - tot;
                            o[1] = (i64)(((u64)(u32)nltot) | ((u64)(u32)nlmax << 32));
                            o[2] = (i64)(((u64)(u32)njoin) | ((u64)(u32)nmemo << 32));
                            for (int q = 0; q < 9; q++)
                                o[3 + q] = (i64)(((u64)(u32)zn[2 * q]) | ((u64)(u32)zn[2 * q + 1] << 32));
                            atomicAdd(g.ctl + 1, 1u);
                        }
                        act = 0;
                        continue;
                    }
                    const i64 lo = cd[1 + j];
                    zi = nz < 6 ? nz++ : 5;
                    zn[zi] = (int)pe;
                    zn[6 + zi] = (int)lo;
                    zn[12 + zi] = (int)lo;
                    const int last = !g.fwd && j == ns - 1 && pe >= 0, clean = pe >= 0 && ptk == 0;
                    const u64 key = ((u64)last << 62) | ((u64)(pe + 1) << 24) | (u64)lo;
                    if (clean && g.memomask) {
                        if (tid == 0) {
                            i64 a = 0, b = 0;
                            s_hit = og_memo_get(g, key, &a, &b);
                            s_zr = a;
                            s_mc = b;
                        }
                        __syncwarp();
                        const int hit = s_hit;
                        const i64 zr = s_zr, mc = s_mc;
                        __syncwarp();
                        work += OG_WSTEP;
                        if (hit && last) {
                            nmemo++;
                            if (tid == 0) {
                                i64 *o = g.out + 12 * c;
                                o[0] = g.fmin[g.N - 1] - (tot + mc + g.gmin[lo]);
                                o[1] = (i64)(((u64)(u32)nltot) | ((u64)(u32)nlmax << 32));
                                o[2] = (i64)(((u64)(u32)njoin) | ((u64)(u32)nmemo << 32));
                                for (int q = 0; q < 9; q++)
                                    o[3 + q] = (i64)(((u64)(u32)zn[2 * q]) | ((u64)(u32)zn[2 * q + 1] << 32));
                                atomicAdd(g.ctl + 1, 1u);
                            }
                            act = 0;
                            continue;
                        }
                        if (hit && zr <= cd[8 + j]) {
                            nmemo++;
                            if ((int)(zr - lo) + 1 > nlmax)
                                nlmax = (int)(zr - lo) + 1;
                            zn[12 + zi] = (int)zr;
                            tot += mc + g.fmin[cd[8 + j]] - g.fmin[zr];
                            pe = cd[8 + j];
                            ptk = 0;
                            j++;
                            continue;
                        }
                    }
                    njoin++;
                    if (last) {
                        lptk = ptk;
                        lpb = g.evb[pe];
                        lpm = (int)g.evm[pe];
                        lzb = g.evb[lo];
                        lm = (int)g.evm[lo];
                        lntk = 2;
                        lmode = 1;
                        pend = 2;
                        req = 1;
                        lkey = key;
                        lclean = clean;
                        llo = lo;
                    } else {
                        inch = 1;
                        z = lo;
                        nl = 0;
                        ccl = clean;
                        cum = 0;
                        continue;
                    }
                } else { /* the next layer of the chain: event z after pe */
                    lptk = pe < 0 ? 0 : ptk;
                    lpb = pe >= 0 ? g.evb[pe] : 0;
                    lpm = pe >= 0 ? (int)g.evm[pe] : 0;
                    lzb = g.evb[z];
                    lm = (int)g.evm[z];
                    lntk = ptk == 1 ? 1 : 0;
                    lmode = 0;
                    pend = 3;
                    req = 1;
                }
                if (req) {
                    if (gen + 16 > OG_GMAX) { /* the generations are used up: an empty table (seldom) */
                        for (u64 q = tid; q < (u64)g.htslots; q += 32)
                            ht[q] = 0;
                        gen = 0;
                        __syncwarp();
                    }
                    if (lm + lpm <= g.small) { /* a small layer: the driver alone */
                        const u8 *pt = lptk == 0 ? g.fw + lpb : lptk == 1 ? TA : TB;
                        u8 *nt = lntk == 0 ? TA : lntk == 1 ? TB : MV;
                        og_layer<1>(g, tid, 32, ht, gen, MV, pt, lpb, lpm, lzb, lm, nt, lmode, dt, bm, &s_min, &s_neq);
                        continue;
                    }
                    if (tid == 0) {
                        s_pb = lpb;
                        s_zb = lzb;
                        s_pm = lpm;
                        s_m = lm;
                        s_ptk = lptk;
                        s_ntk = lntk;
                        s_mode = lmode;
                        s_gen = gen;
                    }
                    need = 1;
                    break;
                }
            }
            if (tid == 0)
                s_task = need;
        }
        __syncthreads();
        if (!s_task)
            break;
        { /* a layer of a big event: the whole block */
            const u64 pb = s_pb, zb = s_zb;
            const int pm = s_pm, m = s_m, pk = s_ptk, nk = s_ntk, mode = s_mode;
            const u32 g0 = s_gen;
            const u8 *pt = pk == 0 ? g.fw + pb : pk == 1 ? TA : TB;
            u8 *nt = nk == 0 ? TA : nk == 1 ? TB : MV;
            og_layer<0>(g, tid, BT, ht, g0, MV, pt, pb, pm, zb, m, nt, mode, dt, bm, &s_min, &s_neq);
        }
    }
    if (tid == 0) {
        g.gen[B] = gen;
        sv[0] = act;
        sv[1] = (int)c;
        sv[2] = j;
        sv[3] = inch;
        sv[4] = (int)z;
        sv[5] = (int)pe;
        sv[6] = ptk;
        sv[7] = nl;
        sv[8] = nz;
        sv[9] = zi;
        sv[10] = nlmax;
        sv[11] = nltot;
        sv[12] = njoin;
        sv[13] = (int)(u32)(u64)tot;
        sv[14] = (int)(u32)((u64)tot >> 32);
        sv[15] = ccl;
        sv[34] = (int)(u32)(u64)cum;
        sv[35] = (int)(u32)((u64)cum >> 32);
        sv[36] = nmemo;
        for (int q = 0; q < 18; q++)
            sv[16 + q] = zn[q];
    }
}
