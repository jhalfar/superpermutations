/* gpuprep.cu - card kernels of gcheck and gdelcheck (compiled to gpuprep.ptx by build.sh, loaded through the
   CUDA driver library).  n <= 16 symbols; letters in the kernels are symbol values 0..n-1.

   mapsym   bytes -> symbols through a 256-entry table (0xFF = not a letter), counts the bytes that are not letters
   rankmark ranks every window of n letters that is a permutation (lexicographic rank 0 .. n!-1, the same Lehmer
            code as an earlier card ranker of mine) and sets its bit in the bit table of the shard [lo, lo + span); counts the
            permutation windows and the first occurrences (atomicOr returned the bit clear).  With dup != 0 a window
            whose bit was already set also sets its bit (by full rank) in dup: gdelcheck's "seen twice" table.
   delmark  gdelcheck pass 2: the positions in [d0, d1) that no window occurring exactly once forbids are deletable;
            counts them and lists them (up to cap) in out.
   popcnt   number of set bits of a 32-bit word array */
typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned char u8;

extern "C" __global__ void mapsym(const u8 *__restrict__ raw, u64 len, u8 *__restrict__ sym, const u8 *__restrict__ lut,
                                  u64 *__restrict__ bad) {
    __shared__ u8 t[256];
    for (int k = threadIdx.x; k < 256; k += blockDim.x) t[k] = lut[k];
    __syncthreads();
    u32 nb = 0;
    for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < len; i += (u64)gridDim.x * blockDim.x) {
        u8 v = t[raw[i]]; sym[i] = v; nb += v == 0xFF;
    }
    for (int d = 16; d; d >>= 1) nb += __shfl_down_sync(0xffffffffu, nb, d);
    if ((threadIdx.x & 31) == 0 && nb) atomicAdd(bad, (u64)nb);
}

/* windows i = 0 .. nwin-1 start in w; w has n-1 more letters after the last window.  Block = blockDim.x * S windows,
   loaded as a tile of blockDim.x * S + n - 1 letters into shared memory. */
extern "C" __global__ void rankmark(const u8 *__restrict__ w, u64 nwin, int n, u64 lo, u64 span, u32 *__restrict__ bits,
                                    u32 *__restrict__ dup, u64 *__restrict__ stats, int S, const u64 *__restrict__ guard) {
    if (guard && *guard) return;          /* the chunk had bytes that are not letters: the host filters it and calls again */
    extern __shared__ u8 tile[];
    const u64 base = (u64)blockIdx.x * blockDim.x * S;
    const int tl = blockDim.x * S + n - 1;
    for (int k = threadIdx.x; k < tl; k += blockDim.x) { u64 p = base + k; tile[k] = p < nwin + n - 1 ? w[p] : 0; }
    __syncthreads();
    const u32 full = (1u << n) - 1;
    u32 perms = 0, firsts = 0;
    for (int s = 0; s < S; s++) {
        int o = s * blockDim.x + threadIdx.x;
        if (base + o >= nwin) break;
        const u8 *x = tile + o;
        u32 m = 0;
#pragma unroll 16
        for (int k = 0; k < 16; k++) if (k < n) m |= 1u << (x[k] & 31);
        if (m != full) continue;
        perms++;
        u64 r = 0; u32 av = full;
#pragma unroll 15
        for (int k = 0; k < 15; k++) if (k < n - 1) { u32 b = 1u << x[k]; r = r * (u64)(n - k) + (u32)__popc(av & (b - 1)); av &= ~b; }
        u64 q = r - lo;
        if (q < span) {
            u32 bit = 1u << (q & 31), old = atomicOr(bits + (q >> 5), bit);
            if (!(old & bit)) firsts++;
            else if (dup) atomicOr(dup + (r >> 5), 1u << (r & 31));
        }
    }
    for (int d = 16; d; d >>= 1) { perms += __shfl_down_sync(0xffffffffu, perms, d); firsts += __shfl_down_sync(0xffffffffu, firsts, d); }
    if ((threadIdx.x & 31) == 0) { atomicAdd(stats, (u64)perms); atomicAdd(stats + 1, (u64)firsts); }
}

/* gdelcheck pass 2.  The buffer w holds the letters [wbase, wbase + m) of the word (length L, nwin = L - n + 1
   windows).  A window s that is a permutation occurring once (its dup bit clear) forbids the positions
   [s + (w[s-1] == w[s]), s + n - (w[s+n-1] == w[s+n])) (delcheck.c).  Block b decides the positions
   [d0 + b*T, d0 + (b+1)*T) intersected with [d0, d1), T = blockDim.x * S; the caller guarantees that the letters
   [d0 - n, d1 + n) intersected with [0, L) are in the buffer.  Shared memory: T + 2n + 2 letters, T + n intervals. */
extern "C" __global__ void delmark(const u8 *__restrict__ w, u64 wbase, u64 m, u64 L, int n, u64 d0, u64 d1,
                                   const u32 *__restrict__ dup, u64 *__restrict__ cnt, u64 *__restrict__ out, u64 cap, int S) {
    extern __shared__ u8 sh[];
    const int T = blockDim.x * S;
    const u64 q0 = d0 + (u64)blockIdx.x * T;
    if (q0 >= d1) return;
    const u64 q1 = q0 + T < d1 ? q0 + T : d1;
    const long long nwin = (long long)L - n + 1;
    /* letters [q0 - n, q1 + n] -> sh[0 ..], sh[j] = letter at q0 - n + j (0xFE outside the buffer) */
    const int nl = (int)(q1 - q0) + 2 * n + 1;
    u8 *let = sh, *ilo = sh + T + 2 * n + 2, *ihi = ilo + T + n;
    for (int j = threadIdx.x; j < nl; j += blockDim.x) {
        long long p = (long long)q0 - n + j;
        let[j] = (p >= (long long)wbase && p < (long long)(wbase + m)) ? w[p - wbase] : 0xFE;
    }
    __syncthreads();
    /* windows s = q0 - n + 1 + j, j = 0 .. (q1 - q0) + n - 2 */
    const int nwj = (int)(q1 - q0) + n - 1;
    const u32 full = (1u << n) - 1;
    for (int j = threadIdx.x; j < nwj; j += blockDim.x) {
        long long s = (long long)q0 - n + 1 + j;
        u8 a = 0, b = 0;
        if (s >= 0 && s < nwin) {
            const u8 *x = let + j + 1;            /* letter at s */
            u32 mm = 0;
            for (int k = 0; k < n; k++) mm |= 1u << (x[k] & 31);
            if (mm == full) {
                u64 r = 0; u32 av = full;
                for (int k = 0; k < n - 1; k++) { u32 bb = 1u << x[k]; r = r * (u64)(n - k) + (u32)__popc(av & (bb - 1)); av &= ~bb; }
                if (!((dup[r >> 5] >> (r & 31)) & 1)) {
                    a = (s > 0 && x[-1] == x[0]) ? 1 : 0;
                    b = (u8)(n - ((s + n < (long long)L && x[n - 1] == x[n]) ? 1 : 0));
                }
            }
        }
        ilo[j] = a; ihi[j] = b;
    }
    __syncthreads();
    u32 nd = 0;
    for (int i = threadIdx.x; i < (int)(q1 - q0); i += blockDim.x) {
        /* position p = q0 + i; window s = p - d has index j = i + n - 1 - d */
        int cov = 0;
        for (int d = 0; d < n && !cov; d++) { int j = i + n - 1 - d; if (ilo[j] <= d && d < ihi[j]) cov = 1; }
        if (!cov) {
            nd++;
            u64 k = atomicAdd(cnt + 1, 1ULL);
            if (k < cap) out[k] = q0 + i;
        }
    }
    for (int d = 16; d; d >>= 1) nd += __shfl_down_sync(0xffffffffu, nd, d);
    if ((threadIdx.x & 31) == 0 && nd) atomicAdd(cnt, (u64)nd);
}

extern "C" __global__ void popcnt(const u32 *__restrict__ bits, u64 nw, u64 *__restrict__ out) {
    u64 c = 0;
    for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < nw; i += (u64)gridDim.x * blockDim.x) c += __popc(bits[i]);
    for (int d = 16; d; d >>= 1) c += __shfl_down_sync(0xffffffffu, c, d);
    if ((threadIdx.x & 31) == 0 && c) atomicAdd(out, c);
}
