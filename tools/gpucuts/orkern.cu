/* orkern.cu - segment insertion on the card (option --or3-gpu of tsw5g2.c): the exact gain of a candidate,
   as o3_gain on the host, one thread block per candidate.

   A candidate is the stretches of the sequence in their new order.  The first stretch keeps its costs (fw).  From
   each new join on, the dynamic programme runs through the stretch that follows, one layer per event, until the
   costs of an event's openings are again what they were; the last stretch needs its first event only (bw says what
   follows) unless fwd is set.  A layer: mv[j] = min(h, min over the openings i of the event before of
   rel[i] + h - overlap(E[i], S[j])) + D[j]; the costs are kept relative to their minimum, h standing for h or more.
   As on the host the overlaps of length k = h .. 4 are found with a hash table of the cheapest opening for every
   k-suffix (one table per block, reused for every k through a generation number), k = 3, 2, 1 with tables indexed by
   the word (shared memory).  The threads of a block share the openings of a layer; the control flow (which layer
   comes next) is computed by every thread from the same shared values, so all threads meet at the same barriers.

   The openings of an event are ALL the openings of its trail, in the order of the host's OP array; an opening the
   event may not take (a skip that is not its own) has fw = bw = 255 and never takes part.  An event with one opening
   only (a segment, a fixed piece) has a slot of its own behind the last opening.

   A candidate without stretches (cand[0] = 0) asks for the value V of one join (cand[1] -> cand[2]) instead.

   A launch works until every block has spent its budget of opening-layers, then every block writes down where it
   is (its candidate, the layer it has reached, the tables stay in its scratch memory) and the next launch goes on
   from there: no launch runs longer than the host wants, whatever a single candidate costs.

   build: nvcc -arch=sm_120 -ptx -o orkern.ptx orkern.cu */
typedef unsigned long long u64; typedef long long i64; typedef unsigned int u32; typedef unsigned char u8;
struct OG {                                             /* as OGDev on the host */
    const u32 *oS, *oE; const u8 *oSh, *oEh; const signed char *oD;      /* all openings: start word, end word (low 32 bits, bits above), cost */
    const u8 *fw, *bw;                                  /* this round: cost of every opening from the front and from the back, 255: not allowed */
    const u64 *evb; const u32 *evm; const i64 *fmin, *gmin;               /* this round: first opening and number of openings of every event, minima */
    const int *cand; i64 *out;                          /* candidates: 16 ints each (stretches, first and last event of each); results: 12 words each */
    u64 *ht; u8 *scr; u32 *gen; u32 *ctl; int *sav;     /* per block: hash table, three byte tables, generation, state; ctl[0]: next candidate, ctl[1]: candidates done */
    u64 *memo;                                          /* the joins already known (as O3Memo on the host): pairs (key, value), key 0: free */
    i64 N, ncand, htslots, scrsz, maxlay, budget, memomask; int h, fwd;
};
#define OG_GMAX 0xFFFFFu
#define OG_BAD (-(1LL << 40))
#define OG_SAVW 64
#define OG_BIG (1 << 20)

__device__ __forceinline__ u64 og_hash(u64 w, int bits) { return (w * 0x9E3779B97F4A7C15ULL) >> (64 - bits); }
/* slot: generation (20 bits), word (40 bits), cost (4 bits); a slot of another generation is free */
__device__ __forceinline__ void og_put(u64 *ht, u64 mask, int bits, u64 gen, u64 w, u32 r) {
    const u64 kg = (gen << 44) | (w << 4); u64 i = og_hash(w, bits);
    for (;;) {
        u64 cur = ht[i];
        for (;;) {
            if ((cur >> 4) == (kg >> 4)) { if ((cur & 15) > r) atomicMin(&ht[i], kg | r); return; }
            if ((cur >> 44) == gen) break;              /* another word of this level: the next slot */
            u64 old = atomicCAS(&ht[i], cur, kg | r);
            if (old == cur) return;
            cur = old;
        }
        i = (i + 1) & mask;
    }
}
__device__ __forceinline__ int og_get(const u64 *ht, u64 mask, int bits, u64 gen, u64 w) {
    const u64 kg = ((gen << 44) | (w << 4)) >> 4;
    for (u64 i = og_hash(w, bits); ; i = (i + 1) & mask) {
        u64 cur = ht[i];
        if ((cur >> 4) == kg) return (int)(cur & 15);
        if ((cur >> 44) != gen) return -1;
    }
}

/* The memo: what follows a new join x -> y when the stretch that ends with x has its old costs does not depend on
   the candidate.  key: as on the host; value: bit 63 (written), the event where the old costs are back (for a last
   stretch: y), the cost up to there.  A block that finds a key without its value computes the join itself. */
__device__ __forceinline__ int og_memo_get(const OG &g, u64 key, i64 *zr, i64 *mc) {
    u64 i = og_hash(key, 40) & (u64)g.memomask;
    for (int p = 0; p < 64; p++, i = (i + 1) & (u64)g.memomask) {
        const u64 k = g.memo[2 * i];
        if (k == key) { const u64 v = g.memo[2 * i + 1]; if (!(v >> 63)) return 0; *zr = (i64)((v >> 32) & 0x7FFFFFFFu); *mc = (i64)(v & 0xFFFFFFFFu); return 1; }
        if (!k) return 0;
    }
    return 0;
}
__device__ __forceinline__ void og_memo_put(const OG &g, u64 key, i64 zr, i64 mc) {
    if (mc < 0 || mc > 0xFFFFFFFFLL) return;
    const u64 v = (1ULL << 63) | ((u64)zr << 32) | (u64)mc; u64 i = og_hash(key, 40) & (u64)g.memomask;
    for (int p = 0; p < 64; p++, i = (i + 1) & (u64)g.memomask) {
        u64 k = g.memo[2 * i];
        if (!k) { k = atomicCAS(&g.memo[2 * i], 0ULL, key); if (!k) { atomicExch(&g.memo[2 * i + 1], v); return; } }
        if (k == key) return;                           /* another block has it (the value is the same) */
    }
}

/* One layer: the m openings from zb after the pm openings from pb whose costs are PT (pm = 0: nothing before).
   mode 0: their costs relative to the minimum go to NT, conv says whether they equal fw; returns the minimum.
   mode 1: returns the minimum of cost + bw. */
__device__ __forceinline__ int og_layer(const OG &g, const int tid, const int BT, u64 *ht, u32 &gen, u8 *MV, const u8 *PT, const u64 pb, const int pm,
                                        const u64 zb, const int m, u8 *NT, const int mode, int *sd, int *s_min, int *s_neq, int &conv) {
    const int h = g.h; const u8 *FW = g.fw + zb;
    for (int j = tid; j < m; j += BT) MV[j] = FW[j] == 255 ? 255 : (u8)(pm ? h : 0);
    __syncthreads();
    if (tid == 0) { *s_min = OG_BIG; *s_neq = 0; }
    __syncthreads();
    if (pm) {
        int bits = 4; while ((1 << bits) < 2 * pm) bits++;
        const u64 mask = (1ULL << bits) - 1;
        for (int k = h; k >= 4; k--) {
            if (gen >= OG_GMAX) { for (u64 q = tid; q < (u64)g.htslots; q += BT) ht[q] = 0; gen = 0; __syncthreads(); }
            gen++;
            const u64 km = (1ULL << (4 * k)) - 1; const int sh = 4 * (h - k);
            for (int i = tid; i < pm; i += BT) {
                const u32 r = PT[i];
                if (r < (u32)k) { const u64 E = g.oE[pb + i] | ((u64)g.oEh[pb + i] << 32); og_put(ht, mask, bits, gen, E & km, r); }
            }
            __syncthreads();
            for (int j = tid; j < m; j += BT) {
                const int mv = MV[j]; if (mv == 255 || mv <= h - k) continue;
                const u64 S = g.oS[zb + j] | ((u64)g.oSh[zb + j] << 32);
                const int v = og_get(ht, mask, bits, gen, S >> sh);
                if (v >= 0 && v + h - k < mv) MV[j] = (u8)(v + h - k);
            }
            __syncthreads();
        }
        for (int q = tid; q < 16 + 256 + 4096; q += BT) sd[q] = 255;
        __syncthreads();
        for (int i = tid; i < pm; i += BT) {
            const int r = PT[i];
            if (r < 3) { const u32 e = g.oE[pb + i]; atomicMin(&sd[272 + (e & 4095)], r); if (r < 2) atomicMin(&sd[16 + (e & 255)], r); if (r < 1) sd[e & 15] = 0; }
        }
        __syncthreads();
    }
    int lmin = OG_BIG; const int s3 = 4 * (h - 3), s2 = 4 * (h - 2), s1 = 4 * (h - 1);
    for (int j = tid; j < m; j += BT) {
        int mv = MV[j]; if (mv == 255) continue;
        if (pm && mv > h - 3) {
            const u64 S = g.oS[zb + j] | ((u64)g.oSh[zb + j] << 32);
            int v = sd[272 + (int)(S >> s3)]; if (v + h - 3 < mv) mv = v + h - 3;
            if (mv > h - 2) { v = sd[16 + (int)(S >> s2)]; if (v + h - 2 < mv) mv = v + h - 2; if (mv == h && !sd[(int)(S >> s1)]) mv = h - 1; }
            MV[j] = (u8)mv;
        }
        const int t = mv + (mode ? (int)g.bw[zb + j] : (int)g.oD[zb + j]);
        if (t < lmin) lmin = t;
    }
    if (lmin < OG_BIG) atomicMin(s_min, lmin);
    __syncthreads();
    const int mn = *s_min;
    if (mode) return mn;
    int neq = 0;
    for (int j = tid; j < m; j += BT) {
        const int mv = MV[j]; u8 t = 255;
        if (mv != 255) { const int x = mv + (int)g.oD[zb + j] - mn; t = (u8)(x < h ? x : h); }
        NT[j] = t; if (t != FW[j]) neq = 1;
    }
    if (neq) *s_neq = 1;
    __syncthreads();
    conv = !*s_neq;
    return mn;
}

/* state of a block between launches (sav, OG_SAVW ints): 0 active, 1 candidate, 2 stretch j, 3 in a chain, 4 event z, 5 pe, 6 where the pool's costs are
   (0: fw, 1: TA, 2: TB), 7 layers of this chain, 8 zones used, 9 current zone, 10 most layers after a join, 11 layers, 12 joins, 13..14 tot,
   15 the chain began with old costs, 16..33 zones (zx, zl, zh), 34..35 cost of the chain so far, 36 joins from the memo */
extern "C" __global__ void or_judge(OG g) {
    __shared__ int sd[16 + 256 + 4096]; __shared__ int s_c, s_min, s_neq, s_hit; __shared__ i64 s_zr, s_mc;
    const int tid = threadIdx.x, BT = blockDim.x; const u64 B = blockIdx.x;
    u64 *ht = g.ht + B * (u64)g.htslots; u8 *MV = g.scr + B * 3 * (u64)g.scrsz, *TA = MV + g.scrsz, *TB = TA + g.scrsz;
    int *sv = g.sav + B * OG_SAVW;
    u32 gen = g.gen[B]; i64 work = 0;
    int act = sv[0], j = sv[2], inch = sv[3], ptk = sv[6], nl = sv[7], nz = sv[8], zi = sv[9], nlmax = sv[10], nltot = sv[11], njoin = sv[12], ccl = sv[15], nmemo = sv[36];
    i64 c = sv[1], z = sv[4], pe = sv[5], tot = (i64)(((u64)(u32)sv[13]) | ((u64)(u32)sv[14] << 32)), cum = (i64)(((u64)(u32)sv[34]) | ((u64)(u32)sv[35] << 32));
    int zn[18]; for (int q = 0; q < 18; q++) zn[q] = sv[16 + q];
    __syncthreads();                                    /* everybody has read the state before anybody writes it */
    for (;;) {
        if (!act) {
            if (tid == 0) s_c = work >= g.budget ? 0x7FFFFFFF : (int)atomicAdd(g.ctl, 1u);
            __syncthreads();
            c = s_c;
            __syncthreads();
            if (c >= g.ncand) break;
            if (g.cand[16 * c] == 0) {                  /* V of the join x -> y from the tables, as o3_exactv on the host */
                const i64 x = g.cand[16 * c + 1], y = g.cand[16 * c + 2]; int cv;
                const int mn = og_layer(g, tid, BT, ht, gen, MV, g.fw + g.evb[x], g.evb[x], (int)g.evm[x], g.evb[y], (int)g.evm[y], MV, 1, sd, &s_min, &s_neq, cv);
                work += g.evm[x] + g.evm[y];
                if (tid == 0) { g.out[12 * c] = mn < g.h ? mn : g.h; atomicAdd(g.ctl + 1, 1u); }
                __syncthreads();
                continue;
            }
            act = 1; j = 0; inch = 0; ptk = 0; nl = 0; nz = 0; zi = 0; nlmax = 0; nltot = 0; njoin = 0; pe = -1; tot = 0; z = 0; ccl = 0; cum = 0; nmemo = 0;
            for (int q = 0; q < 6; q++) { zn[q] = zn[6 + q] = 0; zn[12 + q] = -1; }
            const int *cd = g.cand + 16 * c;
            if (cd[8] >= cd[1]) { tot = g.fmin[cd[8]]; pe = cd[8]; }
            j = 1;
        }
        const int *cd = g.cand + 16 * c; const int ns = cd[0];
        i64 res = 0; int fin = 0;                       /* fin: 1 the gain is res, 2 given up */
        while (!fin) {
            if (work >= g.budget) break;
            if (!inch) {                                /* the next stretch that is not empty */
                while (j < ns && cd[8 + j] < cd[1 + j]) j++;
                if (j >= ns) { res = g.fmin[g.N - 1] - tot; fin = 1; break; }
                const i64 lo = cd[1 + j];
                zi = nz < 6 ? nz++ : 5; zn[zi] = (int)pe; zn[6 + zi] = (int)lo; zn[12 + zi] = (int)lo;
                const int last = !g.fwd && j == ns - 1 && pe >= 0, clean = pe >= 0 && ptk == 0;
                const u64 key = ((u64)last << 62) | ((u64)(pe + 1) << 24) | (u64)lo;
                if (clean && g.memomask) {
                    if (tid == 0) { i64 a = 0, b = 0; s_hit = og_memo_get(g, key, &a, &b); s_zr = a; s_mc = b; }
                    __syncthreads();
                    const int hit = s_hit; const i64 zr = s_zr, mc = s_mc;
                    __syncthreads();
                    if (hit && last) { nmemo++; res = g.fmin[g.N - 1] - (tot + mc + g.gmin[lo]); fin = 1; break; }
                    if (hit && zr <= cd[8 + j]) { nmemo++; zn[12 + zi] = (int)zr; tot += mc + g.fmin[cd[8 + j]] - g.fmin[zr]; pe = cd[8 + j]; ptk = 0; j++; continue; }
                }
                njoin++;
                if (last) {
                    int cv; const u8 *pt = ptk == 0 ? g.fw + g.evb[pe] : ptk == 1 ? TA : TB;
                    const int pm = (int)g.evm[pe], m = (int)g.evm[lo];
                    const int mn = og_layer(g, tid, BT, ht, gen, MV, pt, g.evb[pe], pm, g.evb[lo], m, MV, 1, sd, &s_min, &s_neq, cv);
                    work += m + pm; nltot++;
                    if (clean && g.memomask && tid == 0) og_memo_put(g, key, lo, mn);
                    res = g.fmin[g.N - 1] - (tot + mn + g.gmin[lo]); fin = 1; break;
                }
                inch = 1; z = lo; nl = 0; ccl = clean; cum = 0;
                continue;
            }
            {
                const i64 hi = cd[8 + j]; int cv = 0;
                const u8 *pt = pe < 0 || ptk == 0 ? (pe < 0 ? g.fw : g.fw + g.evb[pe]) : ptk == 1 ? TA : TB;
                u8 *T = ptk == 1 ? TB : TA;             /* the table that is not the pool's */
                const u64 pb = pe >= 0 ? g.evb[pe] : 0; const int pm = pe >= 0 ? (int)g.evm[pe] : 0, m = (int)g.evm[z];
                const int mn = og_layer(g, tid, BT, ht, gen, MV, pt, pb, pm, g.evb[z], m, T, 0, sd, &s_min, &s_neq, cv);
                work += m + pm; tot += mn; cum += mn; nl++; zn[12 + zi] = (int)z;
                int end = 0;
                if (cv) {
                    if (ccl && g.memomask && tid == 0) og_memo_put(g, ((u64)(zn[zi] + 1) << 24) | (u64)zn[6 + zi], z, cum);
                    tot += g.fmin[hi] - g.fmin[z]; ptk = 0; pe = hi; end = 1;
                }
                else {
                    ptk = T == TA ? 1 : 2; pe = z;
                    if (z == hi) end = 1;
                    else if (nl >= g.maxlay) end = 2;
                }
                if (end) { if (nl > nlmax) nlmax = nl; nltot += nl; inch = 0; j++; if (end == 2) { fin = 2; break; } }
                else z++;
            }
        }
        if (!fin) break;                                /* out of budget inside a candidate */
        if (tid == 0) {
            i64 *o = g.out + 12 * c;
            o[0] = fin == 2 ? OG_BAD : res; o[1] = (i64)(((u64)(u32)nltot) | ((u64)(u32)nlmax << 32)); o[2] = (i64)(((u64)(u32)njoin) | ((u64)(u32)nmemo << 32));
            for (int q = 0; q < 9; q++) o[3 + q] = (i64)(((u64)(u32)zn[2 * q]) | ((u64)(u32)zn[2 * q + 1] << 32));
            atomicAdd(g.ctl + 1, 1u);
        }
        act = 0;
        __syncthreads();
    }
    if (tid == 0) {
        g.gen[B] = gen;
        sv[0] = act; sv[1] = (int)c; sv[2] = j; sv[3] = inch; sv[4] = (int)z; sv[5] = (int)pe; sv[6] = ptk; sv[7] = nl; sv[8] = nz; sv[9] = zi; sv[10] = nlmax; sv[11] = nltot; sv[12] = njoin;
        sv[13] = (int)(u32)(u64)tot; sv[14] = (int)(u32)((u64)tot >> 32); sv[15] = ccl; sv[34] = (int)(u32)(u64)cum; sv[35] = (int)(u32)((u64)cum >> 32); sv[36] = nmemo;
        for (int q = 0; q < 18; q++) sv[16 + q] = zn[q];
    }
}
