/* w2pg.cu - card kernels of w2p13g (word2plan for n = 13, tools/pipeline/w2p13.c with the bitmap passes, the index
   and the full lookups on the card).  The base is on the card as in w2p13.c: 4 bits a letter, letter i in byte i/2,
   low nibble first.  Trail t: piece start PS[t], length R = PR[t]; closed (OPEN[t] = 0): cyclic word of R letters,
   R windows; open: the R letters as they are, R - n + 1 windows.  WP[t] = number of windows of the trails before t
   (WP[NP] = all), so a global window number g is (t, o) with WP[t] <= g < WP[t+1], o = g - WP[t]: the order of the
   loops "for t, for o" of w2p13.c.  Keys and ranks as w2p13.c: key = the 13 letters, 4 bits each, first letter
   highest; rank = lexicographic rank (0 .. 13! - 1). */
typedef unsigned long long u64;
typedef long long i64;
typedef unsigned int u32;
typedef unsigned char u8;
#define NN 13
#define KMASK ((1ULL << (4 * NN)) - 1)

__device__ __forceinline__ int Gb(const u8 *__restrict__ a, u64 i) { return (a[i >> 1] >> ((i & 1) << 2)) & 15; }
__device__ __forceinline__ int Tl(const u8 *__restrict__ B, u64 ps, i64 R, int open, i64 o) {
    if (open) return (o < 0 || o >= R) ? 15 : Gb(B, ps + o);
    o %= R; if (o < 0) o += R; return Gb(B, ps + o);
}
__device__ __forceinline__ int isperm(u64 key) {
    u32 m = 0;
#pragma unroll
    for (int j = 0; j < NN; j++) m |= 1u << ((key >> (4 * j)) & 15);
    return m == (1u << NN) - 1;
}
__device__ __forceinline__ u64 rankof(u64 key) {
    u64 r = 0; u32 used = 0;
#pragma unroll
    for (int j = 0; j < NN; j++) {
        u32 c = (key >> (4 * (NN - 1 - j))) & 15;
        r = r * (u64)(NN - j) + (c - (u32)__popc(used & ((1u << c) - 1)));
        used |= 1u << c;
    }
    return r;
}
__device__ __forceinline__ int sampled(u64 key) { return ((key * 0x9E3779B97F4A7C15ULL) >> 58) == 0; }
__device__ __forceinline__ i64 nwin_t(const u64 *PR, const u8 *OPEN, u64 t) { return OPEN[t] ? (i64)PR[t] - NN + 1 : (i64)PR[t]; }
/* the trail of window g: largest t with WP[t] <= g (WP has NP+1 entries, nondecreasing) */
__device__ __forceinline__ u64 find_t(const u64 *WP, u64 NP, u64 g) {
    u64 a = 0, b = NP;            /* WP[a] <= g < WP[b] */
    while (b - a > 1) { u64 m = (a + b) >> 1; if (WP[m] <= g) a = m; else b = m; }
    return a;
}

/* Walk the windows [g0, g1) in order, calling BODY(t, o, key) for every window; the key is rolled letter by letter
   inside a trail and rebuilt at the start of a trail. */
#define WALK(...)                                                                                               \
    {                                                                                                           \
        u64 t = find_t(WP, NP, g0); i64 o = (i64)(g0 - WP[t]), nw = nwin_t(PR, OPEN, t);                       \
        u64 ps = PS[t]; i64 R = (i64)PR[t]; int op = OPEN[t]; u64 key = 0; int fresh = 1;                      \
        for (u64 g = g0; g < g1; g++) {                                                                         \
            while (o >= nw) { t++; o = 0; nw = nwin_t(PR, OPEN, t); ps = PS[t]; R = (i64)PR[t]; op = OPEN[t]; fresh = 1; } \
            if (fresh) { key = 0; for (int j = 0; j < NN; j++) key = key << 4 | (u64)Tl(B, ps, R, op, o + j); fresh = 0; } \
            else key = ((key << 4) | (u64)Tl(B, ps, R, op, o + NN - 1)) & KMASK;                                \
            __VA_ARGS__;                                                                                          \
            o++;                                                                                                \
        }                                                                                                       \
    }

/* mode 0: seen/dup bits of the trail windows and the number of sampled windows of each block (bcount[block]);
   mode 1: the index entries {key, t, o} of the sampled windows, written in window order from E[bbase[block]]. */
extern "C" __global__ void twin(const u8 *__restrict__ B, const u64 *__restrict__ PS, const u64 *__restrict__ PR,
                                const u8 *__restrict__ OPEN, const u64 *__restrict__ WP, u64 NP, u64 Wtot, int S,
                                u32 *__restrict__ seen, u32 *__restrict__ dup, u32 *__restrict__ bcount, int mode,
                                u64 *__restrict__ E, const u64 *__restrict__ bbase, u64 elo, u64 ehi) {
    __shared__ u32 sc[1024];
    u64 g0 = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S, g1 = g0 + S;
    if (g1 > Wtot) g1 = Wtot;
    u32 c = 0;
    if (g0 < g1) {
        if (mode == 0) {
            WALK(if (isperm(key)) {
                u64 r = rankof(key); u32 bit = 1u << (r & 31), old = atomicOr(seen + (r >> 5), bit);
                if (old & bit) atomicOr(dup + (r >> 5), bit);
                if (sampled(key)) c++;
            })
        } else {
            WALK(if (isperm(key) && sampled(key)) c++;)
        }
    }
    if (mode == 0) {
        for (int d = 16; d; d >>= 1) c += __shfl_down_sync(0xffffffffu, c, d);
        if ((threadIdx.x & 31) == 0 && c) atomicAdd(bcount + blockIdx.x, c);
        return;
    }
    /* mode 1: exclusive prefix of the counts in the block, then write */
    sc[threadIdx.x] = c; __syncthreads();
    if (threadIdx.x == 0) { u32 s = 0; for (int i = 0; i < (int)blockDim.x; i++) { u32 v = sc[i]; sc[i] = s; s += v; } }
    __syncthreads();
    u64 k = bbase[blockIdx.x] + sc[threadIdx.x];
    if (g0 < g1 && c) {
        WALK(if (isperm(key) && sampled(key)) {
            if (k >= elo && k < ehi) { u64 *e = E + 2 * (k - elo); e[0] = key; e[1] = (u64)(u32)t | ((u64)(u32)o << 32); }
            k++;
        })
    }
}

/* windows of the base read as one linear word: seen2 / wd (seen twice) */
extern "C" __global__ void bwin(const u8 *__restrict__ B, u64 Blen, int S, u32 *__restrict__ seen, u32 *__restrict__ wd) {
    u64 q0 = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S;
    if (Blen < NN || q0 >= Blen - NN + 1) return;
    u64 q1 = q0 + S, nw = Blen - NN + 1; if (q1 > nw) q1 = nw;
    u64 key = 0;
    for (int j = 0; j < NN - 1; j++) key = key << 4 | (u64)Gb(B, q0 + j);
    for (u64 q = q0; q < q1; q++) {
        key = ((key << 4) | (u64)Gb(B, q + NN - 1)) & KMASK;
        if (!isperm(key)) continue;
        u64 r = rankof(key); u32 bit = 1u << (r & 31), old = atomicOr(seen + (r >> 5), bit);
        if (old & bit) atomicOr(wd + (r >> 5), bit);
    }
}

/* every (t, o) whose window has this key (full_lookup of w2p13.c); up to max stored, count in cnt[0] */
extern "C" __global__ void flook(const u8 *__restrict__ B, const u64 *__restrict__ PS, const u64 *__restrict__ PR,
                                 const u8 *__restrict__ OPEN, const u64 *__restrict__ WP, u64 NP, u64 Wtot, int S,
                                 u64 want, u32 *__restrict__ ct, u32 *__restrict__ co, u32 *__restrict__ cnt, u32 max) {
    u64 g0 = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * S, g1 = g0 + S;
    if (g1 > Wtot) g1 = Wtot;
    if (g0 >= g1) return;
    WALK(if (key == want) { u32 z = atomicAdd(cnt, 1u); if (z < max) { ct[z] = (u32)t; co[z] = (u32)o; } })
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
