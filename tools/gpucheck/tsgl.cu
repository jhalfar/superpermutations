/* tsgl.cu - card kernels of trailsearch_gl (trailsearch_fast with --gpuload): the bitmap passes of
   the model load.  Letters on the card are bytes (values 0..15) in a buffer of a few hundred MB that the host fills
   part by part, so the card holds only the n!-bit tables and that buffer.  Ranks are the lexicographic ranks of
   trailsearch.c (rank_lin); a window is a permutation iff its n letters are different.  n <= 13. */
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
typedef unsigned char u8;

/* key = the n letters, 4 bits each, first letter highest */
__device__ __forceinline__ int isperm(u64 key, int n) {
    u32 m = 0;
    for (int j = 0; j < n; j++) m |= 1u << ((key >> (4 * j)) & 15);
    return m == (1u << n) - 1;
}
__device__ __forceinline__ u64 rankof(u64 key, int n) {
    u64 r = 0; u32 used = 0;
    for (int j = 0; j < n; j++) {
        u32 c = (key >> (4 * (n - 1 - j))) & 15;
        r = r * (u64)(n - j) + (c - (u32)__popc(used & ((1u << c) - 1)));
        used |= 1u << c;
    }
    return r;
}
__device__ __forceinline__ void mark(u64 r, u32 *seen, u32 *dup) {
    u32 bit = 1u << (r & 31), old = atomicOr(seen + (r >> 5), bit);
    if (dup && (old & bit)) atomicOr(dup + (r >> 5), bit);
}

/* The word pass of trailsearch_fast (word_pass_k) for the windows [w0, w1) of the word (L letters, nwin = L - n + 1
   windows).  The buffer w holds the letters [gbase, gbase + m); it must hold [w0 - 3, w1 + 3 + n - 1) intersected
   with [0, L).  Every permutation window sets its bit in ws (and in wd if it was set) and is counted (stats[0]);
   the windows that start a run (no permutation window 1..3 before) go to st, those that end one (none 1..3 after)
   to en: consecutive permutation windows >= 4 apart split the word into pieces.  Thread = S windows (S <= 56). */
extern "C" __global__ void wpass(const u8 *__restrict__ w, u64 gbase, u64 L, int n, int S, u64 w0, u64 w1,
                                 u32 *__restrict__ ws, u32 *__restrict__ wd, u64 *__restrict__ stats,
                                 u64 *__restrict__ st, u64 *__restrict__ en, u64 cap) {
    const u64 nwin = L - n + 1;
    u64 g0 = w0 + ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S, g1 = g0 + S;
    if (g0 >= w1) return;
    if (g1 > w1) g1 = w1;
    const u64 lo = g0 >= 3 ? g0 - 3 : 0, hi = g1 + 3 < nwin ? g1 + 3 : nwin;
    const u64 km = (1ULL << (4 * n)) - 1;
    const u8 *x = w - gbase;      /* x[i] = letter i of the word */
    u64 key = 0, fl = 0;          /* fl bit q - lo: window q is a permutation */
    for (int j = 0; j < n - 1; j++) key = key << 4 | (x[lo + j] & 15);
    for (u64 q = lo; q < hi; q++) {
        key = ((key << 4) | (x[q + n - 1] & 15)) & km;
        if (isperm(key, n)) {
            fl |= 1ULL << (q - lo);
            if (q >= g0 && q < g1) mark(rankof(key, n), ws, wd);
        }
    }
    u32 np = 0;
    for (u64 q = g0; q < g1; q++) {
        u64 b = q - lo;
        if (!((fl >> b) & 1)) continue;
        np++;
        u64 before = (b >= 3 ? (fl >> (b - 3)) : fl) & ((1ULL << (b < 3 ? b : 3)) - 1);
        u64 after = (fl >> (b + 1)) & 7;   /* windows at or beyond nwin are not windows; their bits are 0 */
        if (!before) { u64 k = atomicAdd(stats + 1, 1ULL); if (k < cap) st[k] = q; }
        if (!after) { u64 k = atomicAdd(stats + 2, 1ULL); if (k < cap) en[k] = q; }
    }
    atomicAdd(stats, (u64)np);
}

/* Windows of runs of letters: run e starts at byte EB[e] of the buffer w and has EP[e+1] - EP[e] windows (EP:
   prefix sums, NE + 1 entries, Wtot = EP[NE]); no window crosses from one run into the next.  Sets bits (and dup, if
   not 0); counts the permutation windows in stats[0] (if stats is not 0).  Used for the trail windows (the cyclic
   word of a trail written out with its first n - 1 letters again at the end) and for the plan check (the letters of
   each event). */
extern "C" __global__ void segwin(const u8 *__restrict__ w, const u64 *__restrict__ EB, const u64 *__restrict__ EP,
                                  u64 NE, u64 Wtot, int n, int S, u32 *__restrict__ bits, u32 *__restrict__ dup,
                                  u64 *__restrict__ stats) {
    u64 g0 = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S, g1 = g0 + S;
    if (g0 >= Wtot) return;
    if (g1 > Wtot) g1 = Wtot;
    u64 a = 0, b = NE;            /* EP[a] <= g0 < EP[b] */
    while (b - a > 1) { u64 m = (a + b) >> 1; if (EP[m] <= g0) a = m; else b = m; }
    u64 e = a, o = g0 - EP[e], nw = EP[e + 1] - EP[e];
    const u64 km = (1ULL << (4 * n)) - 1;
    const u8 *x = w + EB[e];
    u64 key = 0; int fresh = 1; u32 np = 0;
    for (u64 g = g0; g < g1; g++, o++) {
        while (o >= nw) { e++; o = 0; nw = EP[e + 1] - EP[e]; x = w + EB[e]; fresh = 1; }
        if (fresh) { key = 0; for (int j = 0; j < n; j++) key = key << 4 | (x[o + j] & 15); fresh = 0; }
        else key = ((key << 4) | (x[o + n - 1] & 15)) & km;
        if (isperm(key, n)) { np++; mark(rankof(key, n), bits, dup); }
    }
    if (stats) atomicAdd(stats, (u64)np);
}

/* windows of a block of letters (one byte each): windows 0 .. nwin-1, the block has n-1 more letters (write_word) */
extern "C" __global__ void rawwin(const u8 *__restrict__ w, u64 nwin, int n, int S, u32 *__restrict__ bits) {
    u64 g0 = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S, g1 = g0 + S;
    if (g0 >= nwin) return;
    if (g1 > nwin) g1 = nwin;
    const u64 km = (1ULL << (4 * n)) - 1;
    u64 key = 0;
    for (int j = 0; j < n - 1; j++) key = key << 4 | (w[g0 + j] & 15);
    for (u64 q = g0; q < g1; q++) {
        key = ((key << 4) | (w[q + n - 1] & 15)) & km;
        if (isperm(key, n)) mark(rankof(key, n), bits, 0);
    }
}

extern "C" __global__ void andbits(u32 *__restrict__ a, const u32 *__restrict__ b, u64 nw) {
    for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < nw; i += (u64)gridDim.x * blockDim.x) a[i] &= b[i];
}
extern "C" __global__ void popcnt(const u32 *__restrict__ bits, u64 nw, u64 *__restrict__ out) {
    u64 c = 0;
    for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < nw; i += (u64)gridDim.x * blockDim.x) c += __popc(bits[i]);
    for (int d = 16; d; d >>= 1) c += __shfl_down_sync(0xffffffffu, c, d);
    if ((threadIdx.x & 31) == 0 && c) atomicAdd(out, c);
}
