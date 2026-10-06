/* kern.cu - GPU kernels of trailsearch_gpu.c (option --gpu).

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   Every search thread has a mirror of its sequence on the card: the nodes, the hash index (the same open-addressing
   table and the same chains as on the host), and the Bloom filter.  The cuts (S, E, cost, flags) are loaded once
   and shared.  The host sends one command buffer per repair round: the patches of the mirror, then the trails to place.
     ts_patch  copies the patches into the mirror (one GPU thread per record) and the rest of the command to the card
     ts_copy   delivers the answers to the host buffer
     ts_probe  best_insertion: one GPU thread per cut, the best (value, cut) of a trail is kept with atomicMin
     ts_relt   related runs: the run ends / starts within one step of a cut of the trails
     ts_batch  all of the above for the jobs of several threads in one launch, with chained repair rounds
   Build (CUDA toolkit; it is needed only for this step, the program loads the driver library at run time):
     Linux or WSL:  nvcc -arch=sm_120 -ptx -o kern.ptx kern.cu
     Windows:       the same line in a shell where the compiler of Visual Studio is set up (vcvars64.bat)
   -arch names the card generation: sm_120 is the RTX 50 series; use the value of your card (sm_89 for RTX 40,
   sm_86 for RTX 30).  I tested sm_120 only.

   Where the parts start.  The types shared with the host and the look-up helpers come first, then one kernel per
   exchange (ts_patch, ts_probe, ts_relt, ts_copy), then, after a comment line of dashes, ts_batch and its helpers. */
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
#define HKEY(word, j, kind) (((u64)(word) << 8) | ((u64)(j) << 4) | (u64)(kind))
#define BFH(key) (((u64)(key) * 0x9E3779B97F4A7C15ULL) >> 32)
/* a dead node has prev = next = -2 */
struct GNode {
    u64 s, e;
    int prev, next;
};
/* as Slot on the host */
struct GSlot {
    u64 key;
    int head, pad;
};
struct GDev { /* as GDev on the host */
    GNode *nd;
    GSlot *tab;
    int *nx, *vl;
    u64 *bf;
    u64 mask, bfmask;
    const u32 *oS, *oE;
    const unsigned char *oSh, *oEh, *oF;
    u32 *stamp;
    int h, pad;
};
__device__ inline u64 hmix(u64 k) {
    k ^= k >> 33;
    k *= 0xFF51AFD7ED558CCDULL;
    k ^= k >> 33;
    k *= 0xC4CEB9FE1A85EC53ULL;
    k ^= k >> 33;
    return k;
}
__device__ inline int dist(u64 e, u64 s, int h) {
    for (int k = h; k >= 1; k--)
        if ((e & ((1ULL << (4 * k)) - 1)) == (s >> (4 * (h - k))))
            return h - k;
    return h;
}
/* 16 pseudo-random bits from (iteration key, cut, node): the same hash as nz16 on the host. */
__device__ inline u64 nz16(u64 itk, u64 o, u64 a) {
    u64 x = (itk ^ o) * 0x9E3779B97F4A7C15ULL;
    x ^= x >> 32;
    x = (x ^ a) * 0xD6E8FEB86659FD93ULL;
    x ^= x >> 32;
    x *= 0xD6E8FEB86659FD93ULL;
    return x >> 48;
}
/* first index entry of a key, -1 if none */
__device__ inline int chain_head(const GDev &d, u64 key) {
    u64 b = BFH(key) & d.bfmask;
    if (!((d.bf[b >> 6] >> (b & 63)) & 1))
        return -1;
    for (u64 i = hmix(key) & d.mask;; i = (i + 1) & d.mask) {
        u64 k = d.tab[i].key;
        if (k == key)
            return d.tab[i].head;
        if (k == ~0ULL)
            return -1;
    }
}
/* The trail of work item g of a launch, from the prefix sums of the items per trail. */
/* pre[q] <= g < pre[q + 1] */
__device__ inline int find_trail(const u64 *pre, int ntr, u64 g) {
    int lo = 0, hi = ntr;
    while (hi - lo > 1) {
        int m = (lo + hi) >> 1;
        if (pre[m] <= g)
            lo = m;
        else
            hi = m;
    }
    return lo;
}

/* cmd: nnode records {id, s, e, prev | next << 32}, nslot records {slot, key, head}, nent words {next | val << 32} for
   the index entries entbase .., nbf records {word, value}, nte records {entry, next | val << 32}; the ncopy words
   after the records are copied to dst (the command of the next kernel, when cmd is host memory) */
extern "C" __global__ void ts_patch(GDev d, const u64 *cmd, int nnode, int nslot, int nent, int nbf, int entbase,
                                    int nte, u64 *dst, int ncopy) {
    int g = blockIdx.x * blockDim.x + threadIdx.x;
    if (g < nnode) {
        const u64 *r = cmd + 4 * (i64)g;
        GNode x;
        x.s = r[1];
        x.e = r[2];
        x.prev = (int)(u32)r[3];
        x.next = (int)(r[3] >> 32);
        d.nd[r[0]] = x;
        return;
    }
    g -= nnode;
    cmd += 4 * (i64)nnode;
    if (g < nslot) {
        const u64 *r = cmd + 3 * (i64)g;
        GSlot x;
        x.key = r[1];
        x.head = (int)r[2];
        x.pad = 0;
        d.tab[r[0]] = x;
        return;
    }
    g -= nslot;
    cmd += 3 * (i64)nslot;
    if (g < nent) {
        u64 r = cmd[g];
        d.nx[entbase + g] = (int)(u32)r;
        d.vl[entbase + g] = (int)(r >> 32);
        return;
    }
    g -= nent;
    cmd += nent;
    if (g < nbf) {
        d.bf[cmd[2 * (i64)g]] = cmd[2 * (i64)g + 1];
        return;
    }
    g -= nbf;
    cmd += 2 * (i64)nbf;
    if (g < nte) {
        u64 r = cmd[2 * (i64)g + 1];
        d.nx[cmd[2 * (i64)g]] = (int)(u32)r;
        d.vl[cmd[2 * (i64)g]] = (int)(r >> 32);
        return;
    }
    g -= nte;
    cmd += 2 * (i64)nte;
    if (g < ncopy)
        dst[g] = cmd[g];
}

/* cmd: pre[0 .. ntr] (first GPU thread of each trail; pre[ntr] = number of cuts), olo[ntr] (first cut),
   ex[ntr] (offset | count << 32 of the cuts that must not be used: skip cuts whose window is skipped already),
   res[ntr] (in: all ones; out: (value << 40) | (cut - olo) of the best candidate), then the excluded cuts.
   value = (delta + 64) << 16 plus the noise bits, as best_insertion on the host. */
extern "C" __global__ void ts_probe(GDev d, u64 *cmd, int ntr, u64 itk, u64 amp) {
    u64 g = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    if (g >= cmd[ntr])
        return;
    int q = find_trail(cmd, ntr, g), h = d.h;
    u64 orel = g - cmd[q], o = cmd[ntr + 1 + q] + orel;
    int F = d.oF[o], D = (F & 7) - 3;
    if (F & 0x80) {
        u64 ex = cmd[2 * ntr + 1 + q];
        const u64 *xl = cmd + (u32)ex;
        for (u32 i = 0; i < (u32)(ex >> 32); i++)
            if (xl[i] == o)
                return;
    }
    u64 S = d.oS[o] | (u64)d.oSh[o] << 32, E = d.oE[o] | (u64)d.oEh[o] << 32;
    u64 best = ~0ULL;
    for (int k = 0; k < 8; k++) {
        int j = k >> 1;
        u64 key = (k & 1) ? HKEY(E & ((1ULL << (4 * (h - j))) - 1), j, 1) : HKEY(S >> (4 * j), j, 0);
        for (int e = chain_head(d, key); e >= 0; e = d.nx[e]) {
            int x = d.vl[e], a, b2;
            if (!(k & 1)) {
                a = x;
                b2 = d.nd[x].next;
            } else {
                b2 = x;
                a = d.nd[x].prev;
            }
            if (a < 0 || b2 < 0)
                continue;
            u64 ea = d.nd[a].e, sb = d.nd[b2].s;
            int dd = dist(ea, S, h) + D + dist(E, sb, h) - dist(ea, sb, h);
            u64 fx = ((u64)(dd + 64) << 16) + (amp ? (nz16(itk, o, (u64)a) * amp) >> 16 : 0);
            u64 p = (fx << 40) | orel;
            if (p < best)
                best = p;
        }
    }
    if (best != ~0ULL) {
        u64 *r = &cmd[3 * ntr + 1 + q];
        if (best < *r)
            atomicMin(r, best);
    }
}

/* cmd: pre[0 .. ntr], olo[ntr], then one word whose low half counts the answers (in: 0), then the answers (ints):
   2 * node + side; side 0: the node ends a run and its end word is within one step of an S; side 1: it starts a run
   and its start word is within one step of an E.  stamp[2 * node + side] == gen marks an answer already given. */
extern "C" __global__ void ts_relt(GDev d, u64 *cmd, int ntr, u32 gen, int cap) {
    u64 g = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    if (g >= cmd[ntr])
        return;
    int q = find_trail(cmd, ntr, g), h = d.h;
    u64 o = cmd[ntr + 1 + q] + (g - cmd[q]);
    u64 S = d.oS[o] | (u64)d.oSh[o] << 32, E = d.oE[o] | (u64)d.oEh[o] << 32;
    int *cnt = (int *)(cmd + 2 * ntr + 1), *out = cnt + 2;
    for (int k = 0; k < 4; k++) {
        int j = k >> 1, side = k & 1;
        u64 key = side ? HKEY(E & ((1ULL << (4 * (h - j))) - 1), j, 1) : HKEY(S >> (4 * j), j, 0);
        for (int e = chain_head(d, key); e >= 0; e = d.nx[e]) {
            int x = d.vl[e];
            GNode nx = d.nd[x];
            if (nx.next == -2)
                continue;
            if (!side) {
                if (nx.next >= 0 && dist(nx.e, d.nd[nx.next].s, h) < 2)
                    continue;
            } else if (nx.prev >= 0 && dist(d.nd[nx.prev].e, nx.s, h) < 2)
                continue;
            u32 *st = &d.stamp[2 * (i64)x + side];
            if (*st == gen || atomicExch(st, gen) == gen)
                continue;
            int i = atomicAdd(cnt, 1);
            if (i < cap)
                out[i] = 2 * x + side;
        }
    }
}

extern "C" __global__ void ts_copy(u64 *dst, const u64 *src, int n) {
    int g = blockIdx.x * blockDim.x + threadIdx.x;
    if (g < n)
        dst[g] = src[g];
}

/* ---------- ts_batch: the pending requests of all search threads of the process in ONE launch.
   On a card that is shared with other processes a launch that finds the card with somebody else waits for a whole
   turn (measured: 10-20 us if the card is ours, 400-900 us if not), so a request must not be three launches, the
   rounds of a repair must not be one request each, and threads must not queue one behind the other.
   A request (job) is the patches of one mirror plus one of: nothing, a related-runs probe, or a chain of repair
   rounds.  In a chain the card does what the host would do between two rounds when nothing but a best insertion is
   needed: it takes the best trail (with the random numbers the host is going to draw), links its node into the
   mirror, and probes again.  The chain stops where the host has to decide: a trail that may be split, an cut that
   skips a window, a trail without a candidate, the last trail.  The host replays the rounds from the log and checks
   every answer as before.
   The index of the mirror (table, entries, filter) is NOT changed by the card: the nodes inserted during the chain
   (at most GJ_RMAX) are kept in a list, and a probe compares its cut with them directly.  That finds the same
   candidates as the index entries the host adds, costs one GPU thread a few stores instead of a dozen table
   insertions, and leaves only two links to take back if the host goes another way.
   When all waiting trails are probed in every round (greedy), a round after the first does not probe again: an
   insertion of x between a and b removes the candidates at the pair (a, b) and adds those at (a, x) and (x, b), and
   nothing else changes (the noise of a candidate depends on its cut and node only).  So the answer of a trail
   stays, unless it was at (a, b) - then the trail is probed again - and the cuts are only compared with the four
   words that end a, start and end x, and start b: no index, no filter.
   An answer is the smallest (value, cut, node) of a trail packed in one word: value << shf | cut << sha |
   node (ts_probe gives value << 40 | cut and leaves the node to the host).
   The grid is one set of thread blocks that stay on the card for the whole launch (the host launches no more blocks
   than fit at once); the phases are separated by a barrier over the grid.  Every wait is bounded: a block that waits
   too long sets the abort word and all threads leave (the host then loads the mirrors again and uses the kernels
   above).  The L1 caches of the card are not coherent inside one launch (PTX manual, ld.ca): what one thread stores,
   a thread on another multiprocessor may still read as it was.  So a thread that has stored something passes a
   memory fence before the barrier, and what is stored during the rounds (links of the nodes, answers, the state of a
   job) is read with volatile loads, which do not use L1; what is fixed after the patches (index, cuts, command)
   is read as usual.
   Job header (GJ_HW words at word hoff of the host buffer, copied to tab): the mirror, the two command buffers, the
   patch counts, the job.  Command (H_NCOPY words after the patch records, copied to the card), ntr = H_NTR:
     TOLO[ntr] first cut, PRE[ntr + 1] first GPU thread of each trail, TEX[ntr] offset | count << 32 of the
     excluded cuts, bit 63: the host decides about this trail (the chain stops when it is taken), then the
     excluded cuts.
   Output from word H_OUT of both buffers: OUT[0] rounds (0 until the job is done), OUT[1] (related runs: number of
   answers, the answers follow), then per round ntr + 2 words: head = status | waiting trails << 8 | taken trail << 20
   (status 0: the card has inserted the trail, 1: the host goes on; taken trail: its place in the list of the host),
   the answers by trail, and node before | node after << 32 of the inserted node.  Behind the log, on the card only:
   the inserted nodes and the list of the host (the waiting trails in its order).  When everything is delivered the
   word H_DONE of the header in the host buffer is set: the host waits for that word, not for the driver. */
enum {
    H_ND,
    H_TAB,
    H_NX,
    H_VL,
    H_BF,
    H_MASK,
    H_BFMASK,
    H_OS,
    H_OE,
    H_OSH,
    H_OEH,
    H_OF,
    H_STAMP,
    H_H,
    H_HC,
    H_DC,
    H_NNODE,
    H_NSLOT,
    H_NENT,
    H_NBF,
    H_ENTBASE,
    H_NTE,
    H_PW,
    H_NCOPY,
    H_KIND,
    H_NTR,
    H_GREEDY,
    H_RMAX,
    H_ITK,
    H_AMP,
    H_SHA,
    H_SHF,
    H_FLAT,
    H_SKPM,
    H_NN,
    H_NDCAP,
    H_RS,
    H_GEN = H_RS + 4,
    H_CAP,
    H_OUT,
    H_DONE,
    H_LO,
    H_TOT,
    H_PL0,
    H_PL1,
    H_FU0,
    H_FU1,
    H_INC,
    H_IAX,
    H_IEA,
    H_ISX,
    H_IEX,
    H_ISB,
    H_RES,
    H_NOVL,
    H_OUTN,
    GJ_HW = 64
};
/* jobs per launch, rounds per job; no chain of the index is that long */
enum { GJ_MAXJ = 16, GJ_RMAX = 24, GJ_WALK = 1 << 18 };
struct GBat {
    const u64 *hc[GJ_MAXJ];
};
typedef volatile u64 *VH; /* a job header: its last fields change between the phases */
struct GDevV {
    volatile GNode *nd;
    GSlot *tab;
    int *nx, *vl;
    u64 *bf;
    u64 mask, bfmask; /* GDev; the links of the nodes change during a launch */
    const u32 *oS, *oE;
    const unsigned char *oSh, *oEh, *oF;
    u32 *stamp;
    int h, pad;
};
/* the nodes inserted in this launch */
struct GOvl {
    u64 s[GJ_MAXJ * GJ_RMAX], e[GJ_MAXJ * GJ_RMAX];
    int id[GJ_MAXJ * GJ_RMAX], prev[GJ_MAXJ * GJ_RMAX], next[GJ_MAXJ * GJ_RMAX];
};
struct GRound {
    u64 lo[GJ_MAXJ], tot[GJ_MAXJ], pl0[GJ_MAXJ], pl1[GJ_MAXJ], fu0[GJ_MAXJ], fu1[GJ_MAXJ], res[GJ_MAXJ], iax[GJ_MAXJ],
        iea[GJ_MAXJ], isx[GJ_MAXJ], iex[GJ_MAXJ], isb[GJ_MAXJ];
    int inc[GJ_MAXJ], novl[GJ_MAXJ];
};
struct GPick { /* what the GPU thread of a job keeps between the rounds */
    int nact, r, skpm, nn, novl, done, kind, ntr, greedy, rmax, sha, vsh, shf;
    u64 s[4], pl0, pl1, out, ndcap;
    volatile u64 *dc;
    const u64 *TOLO;
};
__device__ inline u64 rotl64(u64 x, int k) {
    return (x << k) | (x >> (64 - k));
}
/* First index entry of a key in the mirror of a thread, or -1 (Bloom filter first, then at most GJ_WALK
   probes). */
__device__ inline int chain_head(const GDevV &d, u64 key) {
    u64 b = BFH(key) & d.bfmask;
    if (!((d.bf[b >> 6] >> (b & 63)) & 1))
        return -1;
    for (u64 i = hmix(key) & d.mask, w = 0; w < GJ_WALK; i = (i + 1) & d.mask, w++) {
        u64 k = d.tab[i].key;
        if (k == key)
            return d.tab[i].head;
        if (k == ~0ULL)
            return -1;
    }
    return -1;
}
/* chain_head after the filter */
__device__ inline int slot_head(const GDevV &d, u64 key) {
    for (u64 i = hmix(key) & d.mask, w = 0; w < GJ_WALK; i = (i + 1) & d.mask, w++) {
        u64 k = d.tab[i].key;
        if (k == key)
            return d.tab[i].head;
        if (k == ~0ULL)
            return -1;
    }
    return -1;
}

/* barrier over the grid: every block adds to bar[0] (block 0 adds 2^31 - (nb - 1), so the low bits are zero exactly
   when all have arrived); the last one publishes the tag of the phase in bar[64], the others wait for it */
__device__ inline bool gsync(volatile u32 *bar, u32 nb, int *sh, u32 tag) {
    __syncthreads();
    if (threadIdx.x == 0) {
        u32 add = blockIdx.x == 0 ? 0x80000000u - (nb - 1) : 1u, old = atomicAdd((u32 *)bar, add);
        if (((old + add) & 0x7fffffffu) == 0)
            bar[64] = tag;
        else
            for (u32 spin = 0; bar[64] != tag; spin++)
                if (spin > (1u << 20) || ((spin & 63) == 63 && bar[1])) {
                    bar[1] = 1;
                    break;
                }
        *sh = bar[1] == 0;
    }
    __syncthreads();
    return *sh != 0;
}
/* the work of a job before the first round: patch records, command words, and what the card writes for itself:
   OUT[0], OUT[1] = 0, the log = all ones, the list of the host = 0, 1, 2, ... */
__device__ inline u64 nlog(const u64 *t) {
    return t[H_KIND] == 1 ? t[H_RMAX] * (t[H_NTR] + 2) : 0;
}
/* Number of work items of a job before its first round. */
__device__ inline u64 items1(const u64 *t) {
    return t[H_NNODE] + t[H_NSLOT] + t[H_NENT] + t[H_NBF] + t[H_NTE] + t[H_NCOPY] + 2 + nlog(t) +
           (t[H_KIND] == 1 ? t[H_NTR] : 0);
}
/* as ts_patch */
__device__ __noinline__ void patch_item(const u64 *t, u64 g) {
    GDev d = *(const GDev *)t;
    const u64 *cmd = (const u64 *)t[H_HC];
    u64 *dc = (u64 *)t[H_DC];
    u64 nnode = t[H_NNODE], nslot = t[H_NSLOT], nent = t[H_NENT], nbf = t[H_NBF], nte = t[H_NTE],
        entbase = t[H_ENTBASE], ncopy = t[H_NCOPY];
    if (g < nnode) {
        const u64 *r = cmd + 4 * g;
        GNode x;
        x.s = r[1];
        x.e = r[2];
        u64 l = r[3];
        x.prev = (int)(u32)l;
        x.next = (int)(l >> 32);
        d.nd[r[0]] = x;
        return;
    }
    g -= nnode;
    cmd += 4 * nnode;
    if (g < nslot) {
        const u64 *r = cmd + 3 * g;
        GSlot x;
        x.key = r[1];
        x.head = (int)r[2];
        x.pad = 0;
        d.tab[r[0]] = x;
        return;
    }
    g -= nslot;
    cmd += 3 * nslot;
    if (g < nent) {
        u64 r = cmd[g];
        d.nx[entbase + g] = (int)(u32)r;
        d.vl[entbase + g] = (int)(r >> 32);
        return;
    }
    g -= nent;
    cmd += nent;
    if (g < nbf) {
        d.bf[cmd[2 * g]] = cmd[2 * g + 1];
        return;
    }
    g -= nbf;
    cmd += 2 * nbf;
    if (g < nte) {
        u64 e = cmd[2 * g], r = cmd[2 * g + 1];
        d.nx[e] = (int)(u32)r;
        d.vl[e] = (int)(r >> 32);
        return;
    }
    g -= nte;
    cmd += 2 * nte;
    if (g < ncopy) {
        dc[t[H_PW] + g] = cmd[g];
        return;
    }
    g -= ncopy;
    u64 *out = dc + t[H_OUT], nl = nlog(t);
    if (g < 2)
        out[g] = 0;
    else if (g < 2 + nl)
        out[g] = ~0ULL;
    else
        out[g + t[H_RMAX]] = g - 2 - nl;
}
/* cut g of the trails of job j: related runs (as ts_relt), or the best candidate of the cut: as ts_probe plus
   the nodes inserted in this launch, or (inc, and the trail is not marked in fu) only the candidates at the node
   inserted last */
__device__ inline void probe_item(const u64 *t, u64 g, const GRound &R, const GOvl &ov, int j) {
    GDevV d = *(const GDevV *)t;
    u64 *dc = (u64 *)t[H_DC];
    int ntr = (int)t[H_NTR], h = d.h;
    const u64 *TOLO = dc + t[H_PW], *PRE = TOLO + ntr, *TEX = PRE + ntr + 1;
    int z = find_trail(PRE, ntr, g);
    if ((z < 64 ? R.pl0[j] >> z : R.pl1[j] >> (z - 64)) & 1)
        return;
    u64 orel = g - PRE[z], o = TOLO[z] + orel;
    u64 S = d.oS[o] | (u64)d.oSh[o] << 32, E = d.oE[o] | (u64)d.oEh[o] << 32;
    if (t[H_KIND] == 2) {
        u32 gen = (u32)t[H_GEN];
        int cap = (int)t[H_CAP], any = 0;
        int *cnt = (int *)(dc + t[H_OUT] + 1), *out = cnt + 2;
        for (int k = 0; k < 4; k++) {
            int jj = k >> 1, side = k & 1, w = 0;
            u64 key = side ? HKEY(E & ((1ULL << (4 * (h - jj))) - 1), jj, 1) : HKEY(S >> (4 * jj), jj, 0);
            for (int e = chain_head(d, key); e >= 0 && w < GJ_WALK; e = d.nx[e], w++) {
                int x = d.vl[e], xn = d.nd[x].next, xp = d.nd[x].prev;
                if (xn == -2)
                    continue;
                if (!side) {
                    if (xn >= 0 && dist(d.nd[x].e, d.nd[xn].s, h) < 2)
                        continue;
                } else if (xp >= 0 && dist(d.nd[xp].e, d.nd[x].s, h) < 2)
                    continue;
                u32 *st = &d.stamp[2 * (i64)x + side];
                if (*st == gen || atomicExch(st, gen) == gen)
                    continue;
                int i = atomicAdd(cnt, 1);
                if (i < cap) {
                    out[i] = 2 * x + side;
                    any = 1;
                }
            }
        }
        if (any)
            __threadfence();
        return;
    }
    int F = d.oF[o], D = (F & 7) - 3, sha = (int)t[H_SHA], shf = (int)t[H_SHF];
    u64 itk = t[H_ITK], amp = t[H_AMP];
    if (F & 0x80) {
        u64 ex = TEX[z];
        const u64 *xl = TOLO + (u32)ex;
        for (u32 i = 0; i < ((u32)(ex >> 32) & 0x7fffffffu); i++)
            if (xl[i] == o)
                return;
    }
    u64 best = ~0ULL;
#define CAND(a_, ea_, sb_)                                                                   \
    do {                                                                                     \
        int dd = dist(ea_, S, h) + D + dist(E, sb_, h) - dist(ea_, sb_, h);                  \
        u64 fx = ((u64)(dd + 64) << 16) + (amp ? (nz16(itk, o, (u64)(a_)) * amp) >> 16 : 0), \
            p = fx << shf | orel << sha | (sha ? (u64)(a_) : 0);                             \
        if (p < best)                                                                        \
            best = p;                                                                        \
    } while (0)
    if (R.inc[j] && !((z < 64 ? R.fu0[j] >> z : R.fu1[j] >> (z - 64)) & 1)) {
        u64 ea = R.iea[j], sx = R.isx[j], ex = R.iex[j], sb = R.isb[j];
        int m0 = 0, m1 = 0; /* a, x, b: the pairs (a, x) and (x, b) */
        for (int jj = 0; jj < 4; jj++) {
            u64 lm = (1ULL << (4 * (h - jj))) - 1, sp = S >> (4 * jj), el = E & lm;
            m0 |= (sp == (ea & lm)) | (el == (sx >> (4 * jj)));
            m1 |= (sp == (ex & lm)) | (el == (sb >> (4 * jj)));
        }
        if (m0)
            CAND((u32)R.iax[j], ea, sx);
        if (m1)
            CAND(R.iax[j] >> 32, ex, sb);
    } else {
        u32 fm = 0; /* the eight filter words are asked for before the first one is looked at */
#define PKEY(k_)                                                                  \
    (((k_) & 1) ? HKEY(E & ((1ULL << (4 * (h - ((k_) >> 1)))) - 1), (k_) >> 1, 1) \
                : HKEY(S >> (4 * ((k_) >> 1)), (k_) >> 1, 0))
        for (int k = 0; k < 8; k++) {
            u64 fb = BFH(PKEY(k)) & d.bfmask;
            fm |= (u32)((d.bf[fb >> 6] >> (fb & 63)) & 1) << k;
        }
        for (int k = 0; k < 8; k++) {
            if (!((fm >> k) & 1))
                continue;
            int w = 0;
            for (int e = slot_head(d, PKEY(k)); e >= 0 && w < GJ_WALK; e = d.nx[e], w++) {
                int x = d.vl[e], a, b2;
                if (!(k & 1)) {
                    a = x;
                    b2 = d.nd[x].next;
                } else {
                    b2 = x;
                    a = d.nd[x].prev;
                }
                if (a < 0 || b2 < 0)
                    continue;
                u64 ea = d.nd[a].e, sb = d.nd[b2].s;
                CAND(a, ea, sb);
            }
        }
        for (
            int v = j * GJ_RMAX; v < j * GJ_RMAX + R.novl[j];
            v++) { /* an inserted node x: the pair (x, next) if a prefix of S ends x, the pair (prev, x) if a suffix of E starts x */
            u64 xs = ov.s[v], xe = ov.e[v];
            int m0 = 0, m1 = 0;
            for (int jj = 0; jj < 4; jj++) {
                u64 lm = (1ULL << (4 * (h - jj))) - 1;
                m0 |= (S >> (4 * jj)) == (xe & lm);
                m1 |= (E & lm) == (xs >> (4 * jj));
            }
            if (m0 && ov.next[v] >= 0) {
                u64 sb = d.nd[ov.next[v]].s;
                CAND(ov.id[v], xe, sb);
            }
            if (m1 && ov.prev[v] >= 0) {
                u64 ea = d.nd[ov.prev[v]].e;
                CAND(ov.prev[v], ea, xs);
            }
        }
    }
#undef CAND
    if (best != ~0ULL) {
        u64 *r = dc + R.res[j] + z;
        if (best < *(volatile u64 *)r)
            atomicMin(r, best);
    }
}
/* between two rounds, one GPU thread per job: the end of a job, or the next step of its chain */
__device__ __noinline__ void pick_job(VH t, GPick *ps) {
    if (ps->done)
        return;
    volatile u64 *dc = ps->dc;
    u64 out = ps->out;
    int kind = ps->kind;
    if (kind != 1) {
        u64 n = 2;
        if (kind == 2) {
            int cnt = (int)(u32)dc[out + 1], cap = (int)t[H_CAP];
            n = 2 + ((u64)(cnt < cap ? cnt : cap) + 1) / 2;
        }
        dc[out] = 1;
        t[H_OUTN] = n;
        t[H_TOT] = 0;
        ps->done = 1;
        __threadfence();
        return;
    }
    GDevV d = *(const GDevV *)t;
    int ntr = ps->ntr, nact = ps->nact, r = ps->r, greedy = ps->greedy, rmax = ps->rmax, sha = ps->sha, shf = ps->shf,
        vsh = ps->vsh;
    const u64 *TOLO = ps->TOLO, *PRE = TOLO + ntr, *TEX = PRE + ntr + 1;
    volatile u64 *L = dc + out + 2 + (u64)r * (ntr + 2), *OVL = dc + out + 2 + (u64)rmax * (ntr + 2);
    u64 *ACT = (u64 *)OVL + rmax;
    int stop = 0, pick = 0, z = greedy ? (int)ACT[0] : r;
    u64 bi = L[1 + z];
    if (greedy) { /* the best of all, ties by the random numbers of the host (xoshiro256**, 53 bits each) */
        u64 *s = ps->s, br = 0;
        for (int q = 0; q < nact; q++) {
            int zq = (int)ACT[q];
            u64 x = L[1 + zq], rr = rotl64(s[1] * 5, 7) * 9, tt = s[1] << 17;
            s[2] ^= s[0];
            s[3] ^= s[1];
            s[1] ^= s[2];
            s[0] ^= s[3];
            s[2] ^= tt;
            s[3] = rotl64(s[3], 45);
            rr >>= 11;
            if (x == ~0ULL)
                stop = 1;
            if (!q)
                br = rr;
            else if ((x >> vsh) < (bi >> vsh) || ((x >> vsh) == (bi >> vsh) && rr < br)) {
                br = rr;
                bi = x;
                pick = q;
                z = zq;
            }
        }
    } else if (bi == ~0ULL)
        stop = 1;
    u64 mo = sha ? (1ULL << (shf - sha)) - 1 : 0xFFFFFFFFFFULL, ma = (1ULL << sha) - 1;
    if (!stop && ps->skpm)
        for (int q = 0; q < nact; q++) {
            int zq = greedy ? (int)ACT[q] : r;
            if (d.oF[TOLO[zq] + ((L[1 + zq] >> sha) & mo)] & 0x80) {
                stop = 1;
                break;
            }
        }
    if (!stop &&
        (!sha || (TEX[z] >> 63) || (greedy ? nact == 1 : r + 1 >= ntr) || r + 1 >= rmax || (u64)ps->nn + 1 > ps->ndcap))
        stop = 1;
    int a = (int)(bi & ma), b = stop ? -1 : d.nd[a].next;
    if (b < 0)
        stop = 1;
    L[0] = (u64)stop | (u64)nact << 8 | (u64)pick << 20;
    if (stop) {
        dc[out] = (u64)r + 1;
        t[H_OUTN] = 2 + ((u64)r + 1) * (ntr + 2);
        t[H_TOT] = 0;
        ps->done = 1;
        __threadfence();
        return;
    }
    /* node_insert_after of the host; the index entries of the node stay with the host */
    u64 o = TOLO[z] + ((bi >> sha) & mo), S = d.oS[o] | (u64)d.oSh[o] << 32, E = d.oE[o] | (u64)d.oEh[o] << 32;
    int id = ps->nn++;
    d.nd[id].s = S;
    d.nd[id].e = E;
    d.nd[id].prev = a;
    d.nd[id].next = b;
    d.nd[a].next = id;
    d.nd[b].prev = id;
    L[ntr + 1] = (u64)(u32)a | (u64)(u32)b << 32;
    OVL[ps->novl++] = (u64)id;
    if (d.oF[o] & 0x80)
        ps->skpm = 1;
    if (z < 64)
        ps->pl0 |= 1ULL << z;
    else
        ps->pl1 |= 1ULL << (z - 64);
    ps->r = ++r;
    volatile u64 *L2 = L + ntr + 2;
    if (greedy) { /* the answers stay, except those at the pair (a, b): these trails are probed again */
        u64 fu0 = 0, fu1 = 0;
        ACT[pick] = ACT[nact - 1];
        ps->nact = --nact;
        for (int q = 0; q < nact; q++) {
            int zq = (int)ACT[q];
            u64 x = L[1 + zq];
            if ((int)(x & ma) == a) {
                if (zq < 64)
                    fu0 |= 1ULL << zq;
                else
                    fu1 |= 1ULL << (zq - 64);
            } else
                L2[1 + zq] = x;
        }
        t[H_PL0] = ps->pl0;
        t[H_PL1] = ps->pl1;
        t[H_FU0] = fu0;
        t[H_FU1] = fu1;
        t[H_INC] = 1;
        t[H_IAX] = (u64)(u32)a | (u64)(u32)id << 32;
        t[H_IEA] = d.nd[a].e;
        t[H_ISX] = S;
        t[H_IEX] = E;
        t[H_ISB] = d.nd[b].s;
    } else {
        t[H_LO] = PRE[r];
        t[H_TOT] = PRE[r + 1] - PRE[r];
    }
    t[H_RES] = out + 2 + (u64)r * (ntr + 2) + 1;
    t[H_NOVL] = (u64)ps->novl;
    __threadfence();
}
/* One launch for the jobs of several search threads: each job brings the patches of its mirror and a chain
   of repair rounds; the GPU threads of all blocks share the work of each phase (see the comment above). */
extern "C" __global__ void ts_batch(GBat b, int J, u64 *tab, u32 *bar, u32 base, int hoff) {
    __shared__ int sh;
    __shared__ GRound R;
    __shared__ GOvl ov;
    const u32 nb = gridDim.x, tid = threadIdx.x;
    const u64 G = (u64)nb * blockDim.x, g0 = (u64)blockIdx.x * blockDim.x + tid;
    u32 tag = base;
    VH vt = tab;
    GPick ps;
    for (u64 i = g0; i < (u64)J * GJ_HW; i += G)
        tab[i] = b.hc[i / GJ_HW][hoff + i % GJ_HW];
    __threadfence();
    if (!gsync(bar, nb, &sh, tag++))
        return;
    {
        u64 tot = 0;
        for (int j = 0; j < J; j++)
            tot += items1(tab + j * GJ_HW);
        for (u64 i = g0; i < tot; i += G) {
            u64 r = i;
            int j = 0;
            for (; j + 1 < J; j++) {
                u64 c = items1(tab + j * GJ_HW);
                if (r < c)
                    break;
                r -= c;
            }
            patch_item(tab + j * GJ_HW, r);
        }
    }
    if (g0 < (u64)J) {
        const u64 *t = tab + g0 * GJ_HW;
        ps.kind = (int)t[H_KIND];
        ps.ntr = (int)t[H_NTR];
        ps.greedy = (int)t[H_GREEDY];
        ps.rmax = (int)t[H_RMAX];
        ps.sha = (int)t[H_SHA];
        ps.shf = (int)t[H_SHF];
        ps.vsh = ps.shf + (int)t[H_FLAT];
        ps.nact = ps.greedy ? ps.ntr : 1;
        ps.r = 0;
        ps.skpm = (int)t[H_SKPM];
        ps.nn = (int)t[H_NN];
        ps.novl = 0;
        ps.done = 0;
        ps.pl0 = ps.pl1 = 0;
        ps.out = t[H_OUT];
        ps.ndcap = t[H_NDCAP];
        ps.dc = (volatile u64 *)t[H_DC];
        ps.TOLO = (const u64 *)t[H_DC] + t[H_PW];
        for (int k = 0; k < 4; k++)
            ps.s[k] = t[H_RS + k];
    }
    __threadfence();
    if (!gsync(bar, nb, &sh, tag++))
        return;
    for (int round = 0; round < GJ_RMAX + 2; round++) {
        /* the state of the jobs and the inserted nodes, once per block */
        if (tid < (u32)J) {
            VH t = vt + tid * GJ_HW;
            R.lo[tid] = t[H_LO];
            R.tot[tid] = t[H_TOT];
            R.pl0[tid] = t[H_PL0];
            R.pl1[tid] = t[H_PL1];
            R.res[tid] = t[H_RES];
            R.novl[tid] = (int)t[H_NOVL];
            R.inc[tid] = (int)t[H_INC];
            if (R.inc[tid]) {
                R.fu0[tid] = t[H_FU0];
                R.fu1[tid] = t[H_FU1];
                R.iax[tid] = t[H_IAX];
                R.iea[tid] = t[H_IEA];
                R.isx[tid] = t[H_ISX];
                R.iex[tid] = t[H_IEX];
                R.isb[tid] = t[H_ISB];
            }
        }
        if (round && tid < (u32)J * GJ_RMAX) {
            int j = tid / GJ_RMAX, k = tid % GJ_RMAX;
            VH t = vt + j * GJ_HW;
            if ((u64)k < t[H_NOVL] && t[H_TOT]) {
                GDevV d = *(const GDevV *)t;
                const volatile u64 *dc = (const volatile u64 *)t[H_DC];
                int id = (int)dc[t[H_OUT] + 2 + t[H_RMAX] * (t[H_NTR] + 2) + k];
                ov.id[tid] = id;
                ov.s[tid] = d.nd[id].s;
                ov.e[tid] = d.nd[id].e;
                ov.prev[tid] = d.nd[id].prev;
                ov.next[tid] = d.nd[id].next;
            }
        }
        __syncthreads();
        u64 tot = 0;
        for (int j = 0; j < J; j++)
            tot += R.tot[j];
        if (round && !tot)
            break;
        for (u64 i = g0; i < tot; i += G) {
            u64 r = i;
            int j = 0;
            for (; j + 1 < J; j++) {
                if (r < R.tot[j])
                    break;
                r -= R.tot[j];
            }
            probe_item(tab + j * GJ_HW, R.lo[j] + r, R, ov, j);
        }
        if (!gsync(bar, nb, &sh, tag++))
            return;
        if (g0 < (u64)J)
            pick_job(vt + g0 * GJ_HW, &ps);
        if (!gsync(bar, nb, &sh, tag++))
            return;
    }
    {
        u64 tot = 0;
        for (int j = 0; j < J; j++)
            tot += vt[j * GJ_HW + H_OUTN];
        int any = 0;
        for (u64 i = g0; i < tot; i += G) {
            u64 r = i;
            int j = 0;
            for (; j + 1 < J; j++) {
                u64 c = vt[j * GJ_HW + H_OUTN];
                if (r < c)
                    break;
                r -= c;
            }
            const u64 *t = tab + j * GJ_HW;
            u64 *hc = (u64 *)t[H_HC];
            const volatile u64 *dc = (const volatile u64 *)t[H_DC];
            u64 out = t[H_OUT];
            hc[out + r] = dc[out + r];
            any = 1;
        }
        if (any)
            __threadfence_system();
    }
    if (!gsync(bar, nb, &sh, tag++))
        return;
    if (g0 < (u64)J) {
        ((u64 *)b.hc[g0])[hoff + H_DONE] = 1;
        __threadfence_system();
    }
}
