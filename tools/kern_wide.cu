/* kern_wide.cu - GPU kernels of recut_wide.c (options --gpu --wide).  Experimental, as that file.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   These are the kernels of the first generation of the card code (one exchange per repair round: ts_patch,
   ts_probe or ts_relt, ts_copy), with one addition for the wide model: bits 60.. of a node's e are 1 / 2 if its
   join with its successor is tight (n - 2 / n - 1 letters shared); that join then costs -1 / -2 instead of what the
   h-words say.  The host sends 0 there without --wide.  ts_wide marks a kernel file that knows this.
   trailsearch_gpu.c uses kern.cu, not this file.
   Build:  nvcc -arch=sm_120 -ptx -o kern_wide.ptx kern_wide.cu      (see kern.cu for -arch)

   Where the parts start.  Types and look-up helpers first, then the kernels in this order: ts_patch, ts_probe,
   ts_relt, ts_copy, ts_wide. */
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
            int tf = (int)(ea >> 60);
            int dd = dist(ea, S, h) + D + dist(E, sb, h) - (tf ? -tf : dist(ea, sb, h));
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
                if (nx.next >= 0 && ((nx.e >> 60) || dist(nx.e, d.nd[nx.next].s, h) < 2))
                    continue;
            } else if (nx.prev >= 0 && ((d.nd[nx.prev].e >> 60) || dist(d.nd[nx.prev].e, nx.s, h) < 2))
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
extern "C" __global__ void ts_wide(int *x) {
}
