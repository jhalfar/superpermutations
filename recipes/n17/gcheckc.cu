/* gcheckc.cu - opt/n17/gcheck17.cu with a two-level completed set (agent coretab).
   Core of a group: the group is the cyclic order of the n-1 letters other than the satellite S, read from M; its
   rank g is the Lehmer rank of the n-2 letters after M (classify).  Delete the top letter T (the largest letter
   other than S and M) from that sequence: the rest, n-3 letters, ranked by Lehmer, is the core (one of (n-3)!), and
   the position of T (0..n-3) is the child.  g <-> (core, child) is a bijection (core_of; tested on the host for every
   g at small n, coreBp --selftest).  In the Lehmer digits of g, T is the first position whose digit is the largest
   possible (all remaining letters are smaller than T); the other digits are the core's digits.
   Modes (P.mode): 1 = group table as before ((n-2)!/oK bits, bit g/oK for g = oI mod oK), 2 = core table only,
   3 = both (debug).  In modes 2 and 3 the scan records every group (gK = 1); the group table of mode 3 may be
   restricted to the shard oI/oK (only to save card memory; bit g/oK).
   Core table: harvest ORs the child bit of every complete group into an active-core hash (open addressing, key =
   core, one 32-bit mask of n-2 <= 15 child bits), unless the core's bit is already set (a group completed again:
   counted in stats[4], nothing changes).  csweep (after harvest): an active core whose mask is full sets its bit in
   the (n-3)!-bit core table and is dropped; the others go to a list, the table is cleared, and creins puts them back.
   So a core bit is set only after all its n-2 child groups were complete, each only after all its n(n-1) members
   were seen.  A full core table or list raises overflow flag 8 / 16 and the run is not valid. */
/* gcheck17.cu - opt/fastcheck/gcheck.cu for n <= 17 with group shards (agent n17):
     - member masks of n(n-1) <= 272 bits: 9 words (table entries, survivors, residues);
     - group shard gI/gK: only groups g with g mod gK = gI go into the table; their bit is g / gK in a table of
       ceil((n-2)!/gK) bits (gK = 1: every group, bit g, as before).  The scan itself is unchanged: every window is
       still tested and classified, a group outside the shard is simply not recorded;
     - slice descriptors store the letters of B relative to the satellite (c - (c > s)), decoded in expand.
   Original description: */
/* gcheck.cu - v2 on the card: expansion of slice descriptors into letters, the group check of gcore.h, leaf hashes
   of the tree hash, and the route-A ranker.  Compiled to PTX (build_ptx.bat), loaded through the CUDA driver library
   by gcard.h.  Letters are values 0..n-1 (one byte each).

   Group check (same claim as gcore.h: a group's bit is set only when all its n(n-1) members were seen):
     scan:      every thread takes CH consecutive window starts of the segment; a permutation window is classified
                (group G, class t, rotation j), the run of its left rotations is taken in one step, a weight-2 step
                keeping S in the pair stays in the group; the members are OR-ed into a 240-bit mask while the group
                does not change, then into the table entry of the group (open addressing, atomicCAS on the key,
                atomicOr on the mask words).  Windows past the chunk belong to the next thread.
     harvest:   every table entry: all members seen -> its bit in the group table (atomicOr); otherwise it is kept
                for the next segment (survivor), or, if it was not touched during this segment, it goes to the host
                as a residue (merged at the end).
     reinsert:  survivors go back into the cleared table before the next segment's scan.
   A full table never makes a group complete; it raises the overflow flag and the run is reported as failed. */
typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned char u8;
#define EMPTYK 0xFFFFFFFFFFFFFFFFULL

struct GParam {                    /* constants of the run */
    int n, S, M; int pad;
    u64 fact[21];
    u64 gK, gI;                    /* group shard: groups with g mod gK = gI */
    u32 full[9];                   /* full member mask */
    u32 pad2;
    int mode, nc;                  /* coretab: 1 group table, 2 core table, 3 both; nc = n-2 children per core */
    u64 oK, oI;                    /* group table (modes 1, 3): groups g = oI mod oK, bit g / oK */
    u32 cfull; u32 pad3;           /* full child mask (n-2 bits) */
};
__constant__ GParam P;
/* (core, child) of group g: see the header */
__device__ __forceinline__ u64 core_of(u64 g, int *child) {
    const int n = P.n; u64 rem = g, c = 0; int p = n - 3, found = 0;
    for (int k = 1; k <= n - 3; k++) {
        u64 f = P.fact[n - 2 - k], d = rem / f; rem -= d * f;
        if (!found && d == (u64)(n - 2 - k)) { found = 1; p = k - 1; continue; }
        c += d * (found ? f : P.fact[n - 3 - k]);
    }
    *child = p; return c;
}
__device__ __forceinline__ u64 chsh(u64 c) { return (c * 0xC2B2AE3D27D4EB4FULL) >> 24; }

__device__ __forceinline__ u64 classify(const u8 *x, int *tt, int *jj) {
    const int n = P.n, S = P.S, M = P.M;
    int js = 0; while (x[js] != S) js++;
    u8 q[32];
    for (int k = 0; k < n - 1; k++) { int p = js + 1 + k; if (p >= n) p -= n; q[k] = x[p]; q[k + n - 1] = x[p]; }
    int t = 0; while (q[t] != M) t++;
    u32 avail = ((1u << n) - 1) & ~(1u << S) & ~(1u << M);
    u64 r = 0;
    for (int k = 1; k <= n - 3; k++) { int s = q[t + k]; r += (u64)__popc(avail & ((1u << s) - 1)) * P.fact[n - 2 - k]; avail &= ~(1u << s); }
    *tt = t; *jj = js; return r;
}
__device__ __forceinline__ u64 hsh(u64 g) { return (g * 0x9E3779B97F4A7C15ULL) >> 20; }
/* OR mask m into the entry of group g; returns 0 if the table is full along the probe path */
__device__ int tab_or(u64 *keys, u32 *masks, u8 *touched, u64 tmask, u64 g, const u32 *m) {
    u64 h = hsh(g) & tmask;
    for (int probe = 0; probe < 4096; probe++) {
        u64 k = keys[h];
        if (k == EMPTYK) { u64 old = atomicCAS(&keys[h], EMPTYK, g); if (old == EMPTYK || old == g) k = g; else k = old; }
        if (k == g) {
            for (int w = 0; w < 9; w++) if (m[w]) atomicOr(&masks[h * 9 + w], m[w]);
            touched[h] = 1;
            return 1;
        }
        h = (h + 1) & tmask;
    }
    return 0;
}
__device__ __forceinline__ void addbits(u32 *m, int t, int j, u64 cnt, int n) {
    u32 rm;                        /* n <= 17: rm has n bits, off + n <= 272 = 9 words */
    if (cnt >= (u64)n) rm = (1u << n) - 1;
    else { int c = (int)cnt, lo = j - c + 1; rm = lo >= 0 ? ((1u << c) - 1) << lo : (((1u << (j + 1)) - 1) | (((1u << (-lo)) - 1) << (n + lo))); }
    int off = t * n, w = off >> 5, sh = off & 31;
    m[w] |= rm << sh;
    if (sh + n > 32) m[w + 1] |= rm >> (32 - sh);
}
extern "C" __global__ void scan(const u8 *__restrict__ d, u64 nwin, int CH, u64 *keys, u32 *masks, u8 *touched, u64 tmask,
                                u64 *stats, u32 *overflow) {
    const int n = P.n, S = P.S; const u32 FULL = (1u << n) - 1;
    u64 a = ((u64)blockIdx.x * blockDim.x + threadIdx.x) * (u64)CH;
    if (a >= nwin) return;
    u64 b = a + CH < nwin ? a + CH : nwin;
    u64 i = a; int have = 0, t = 0, j = 0; u64 g = 0;
    u64 cg = EMPTYK; u32 cm[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0}; int cin = 0;   /* cin: cg is in the shard */
    u64 pw = 0, runs = 0;
    while (i < b) {
        const u8 *x = d + i;
        if (!have) {
            u32 seen = 0; for (int k = 0; k < n; k++) seen |= 1u << x[k];
            if (seen != FULL) { i++; continue; }
            g = classify(x, &t, &j);
        }
        u64 k = 0; while (i + k + 1 < b && x[k + n] == x[k]) k++;
        u64 cnt = k + 1;
        if (g != cg) {
            if (cg != EMPTYK && cin && !tab_or(keys, masks, touched, tmask, cg, cm)) atomicOr(overflow, 1u);
            cg = g; cin = P.gK == 1 || g % P.gK == P.gI; for (int w = 0; w < 9; w++) cm[w] = 0;
        }
        addbits(cm, t, j, cnt, n);
        pw += cnt; runs++;
        u64 e = i + k;
        if (e + 2 < b && d[e + n] == d[e + 1] && d[e + n + 1] == d[e]) {
            u8 a1 = d[e], a2 = d[e + 1];
            if (a1 == S) { t = t == 0 ? n - 2 : t - 1; j = n - 1; }
            else if (a2 == S) { t = t == n - 2 ? 0 : t + 1; j = n - 2; }
            else g = classify(d + e + 2, &t, &j);
            have = 1;
        } else have = 0;
        i = e + 2;
    }
    if (cg != EMPTYK && cin && !tab_or(keys, masks, touched, tmask, cg, cm)) atomicOr(overflow, 1u);
    atomicAdd(&stats[0], pw); atomicAdd(&stats[1], runs);
}
/* scan2 - the same scan with the block's letters staged in shared memory (agent n17).  In scan, the 32 threads of a
   warp read bytes 256 apart, so every load touches 32 cache lines; here a block of 128 threads first copies its
   32768 + n - 1 letters with consecutive (coalesced) loads into shared memory, with 4 bytes of padding after every
   256 (thread t's letters then start in bank t mod 32), and every thread runs exactly the code of scan on them:
   the same windows [a, b), the same reads (letters a .. b + n - 2), the same table updates.  Requires CH = 256 and
   128 threads per block (as gcard17.h launches it). */
#define SMB (128u * 256u)
__device__ __forceinline__ u32 sidx(u32 p) { return p + ((p >> 8) << 2); }
#define X(p) sm[sidx(p)]
__device__ __forceinline__ u64 classify_s(const u8 *sm, u32 p0, int *tt, int *jj) {
    const int n = P.n, S = P.S, M = P.M;
    int js = 0; while (X(p0 + js) != S) js++;
    u8 q[32];
    for (int k = 0; k < n - 1; k++) { int p = js + 1 + k; if (p >= n) p -= n; q[k] = X(p0 + p); q[k + n - 1] = q[k]; }
    int t = 0; while (q[t] != M) t++;
    u32 avail = ((1u << n) - 1) & ~(1u << S) & ~(1u << M);
    u64 r = 0;
    for (int k = 1; k <= n - 3; k++) { int s = q[t + k]; r += (u64)__popc(avail & ((1u << s) - 1)) * P.fact[n - 2 - k]; avail &= ~(1u << s); }
    *tt = t; *jj = js; return r;
}
extern "C" __global__ void __launch_bounds__(128) scan2(const u8 *__restrict__ d, u64 nwin, int CH, u64 *keys, u32 *masks, u8 *touched, u64 tmask,
                                u64 *stats, u32 *overflow) {
    __shared__ u8 sm[SMB + 64 + ((SMB + 64) >> 8) * 4 + 16];
    const int n = P.n, S = P.S; const u32 FULL = (1u << n) - 1;
    u64 A = (u64)blockIdx.x * SMB;
    if (A >= nwin) return;                                     /* the whole block */
    u64 lim = nwin + n - 1 - A; if (lim > SMB + n - 1) lim = SMB + n - 1;
    for (u32 p = threadIdx.x; p < lim; p += blockDim.x) sm[sidx(p)] = d[A + p];
    __syncthreads();
    u64 a = A + (u64)threadIdx.x * CH;
    u64 b = a + CH < nwin ? a + CH : nwin; if (a > b) b = a;   /* threads past the end do nothing (no return: see below) */
    u64 i = a; int have = 0, t = 0, j = 0; u64 g = 0;
    u64 cg = EMPTYK; u32 cm[9] = {0, 0, 0, 0, 0, 0, 0, 0, 0}; int cin = 0;
    u64 pw = 0, runs = 0;
    while (i < b) {
        u32 r = (u32)(i - A);
        if (!have) {
            u32 seen = 0; for (int k = 0; k < n; k++) seen |= 1u << X(r + k);
            if (seen != FULL) { i++; continue; }
            g = classify_s(sm, r, &t, &j);
        }
        u64 k = 0; while (i + k + 1 < b && X(r + (u32)k + n) == X(r + (u32)k)) k++;
        u64 cnt = k + 1;
        if (g != cg) {
            if (cg != EMPTYK && cin && !tab_or(keys, masks, touched, tmask, cg, cm)) atomicOr(overflow, 1u);
            cg = g; cin = P.gK == 1 || g % P.gK == P.gI; for (int w = 0; w < 9; w++) cm[w] = 0;
        }
        addbits(cm, t, j, cnt, n);
        pw += cnt; runs++;
        u64 e = i + k; u32 re = (u32)(e - A);
        if (e + 2 < b && X(re + n) == X(re + 1) && X(re + n + 1) == X(re)) {
            u8 a1 = X(re), a2 = X(re + 1);
            if (a1 == S) { t = t == 0 ? n - 2 : t - 1; j = n - 1; }
            else if (a2 == S) { t = t == n - 2 ? 0 : t + 1; j = n - 2; }
            else g = classify_s(sm, re + 2, &t, &j);
            have = 1;
        } else have = 0;
        i = e + 2;
    }
    if (cg != EMPTYK && cin && !tab_or(keys, masks, touched, tmask, cg, cm)) atomicOr(overflow, 1u);
    /* one atomic per warp instead of two per thread (same-address atomics serialise) */
    for (int o = 16; o; o >>= 1) { pw += __shfl_down_sync(0xffffffffu, pw, o); runs += __shfl_down_sync(0xffffffffu, runs, o); }
    if ((threadIdx.x & 31) == 0) { atomicAdd(&stats[0], pw); atomicAdd(&stats[1], runs); }
}
#undef X

/* survivors / residues: g, then 8 mask words, then age (in a u64 slot as 10 u32... kept as struct of 5 u64) */
struct Rec { u64 g; u32 m[9]; u32 age; };
/* OR child bit ch into the active entry of core c (coretab); returns 0 if the table is full along the probe path */
__device__ int core_or(u64 *ckeys, u32 *cmasks, u64 ctmask, u64 c, u32 bit, u64 *stats) {
    u64 h = chsh(c) & ctmask;
    for (int probe = 0; probe < 4096; probe++) {
        u64 k = ckeys[h];
        if (k == EMPTYK) { u64 old = atomicCAS(&ckeys[h], EMPTYK, c); if (old == EMPTYK || old == c) k = c; else k = old; }
        if (k == c) { u32 o = atomicOr(&cmasks[h], bit); if (o & bit) atomicAdd(&stats[4], 1ULL); return 1; }
        h = (h + 1) & ctmask;
    }
    return 0;
}
extern "C" __global__ void harvest(u64 *keys, u32 *masks, u8 *touched, u64 cap, unsigned long long *B2,
                                   Rec *surv, u32 *nsurv, u32 survcap, Rec *res, u32 *nres, u32 rescap, u8 *ages, u64 *stats, u32 *overflow,
                                   u64 *ckeys, u32 *cmasks, u64 ctmask, const unsigned long long *CB) {
    u64 ncomp = 0;                                      /* complete groups seen by this thread (stats[2]) */
    for (u64 h = (u64)blockIdx.x * blockDim.x + threadIdx.x; h < cap; h += (u64)gridDim.x * blockDim.x) {
        u64 g = keys[h];
        if (g == EMPTYK) continue;
        u32 m[9]; int full = 1;
        for (int w = 0; w < 9; w++) { m[w] = masks[h * 9 + w]; if (m[w] != P.full[w]) full = 0; }
        if (full) {
            if ((P.mode & 1) && g % P.oK == P.oI) { u64 gl = g / P.oK; atomicOr(&B2[gl >> 6], 1ULL << (gl & 63)); }
            if (P.mode & 2) {
                int ch; u64 c = core_of(g, &ch);
                if (CB[c >> 6] >> (c & 63) & 1) atomicAdd(&stats[5], 1ULL);           /* core already complete: group seen again */
                else if (!core_or(ckeys, cmasks, ctmask, c, 1u << ch, stats)) atomicOr(overflow, 8u);
            }
            ncomp++;
        }
        else if (touched[h] || ages[h] == 0) {          /* seen in this segment (or new): keep */
            u32 s = atomicAdd(nsurv, 1u);
            if (s < survcap) { Rec r; r.g = g; for (int w = 0; w < 9; w++) r.m[w] = m[w]; r.age = 1; surv[s] = r; } else atomicOr(overflow, 2u);
        } else {                                          /* not continued: residue for the host */
            u32 s = atomicAdd(nres, 1u);
            if (s < rescap) { Rec r; r.g = g; for (int w = 0; w < 9; w++) r.m[w] = m[w]; r.age = 0; res[s] = r; } else atomicOr(overflow, 4u);
        }
        keys[h] = EMPTYK; for (int w = 0; w < 9; w++) masks[h * 9 + w] = 0; touched[h] = 0; ages[h] = 0;
    }
    /* one atomic per warp instead of one per complete group (same-address atomics serialise) */
    for (int o = 16; o; o >>= 1) ncomp += __shfl_down_sync(0xffffffffu, ncomp, o);
    if ((threadIdx.x & 31) == 0 && ncomp) atomicAdd(&stats[2], ncomp);
}
extern "C" __global__ void reinsert(const Rec *surv, u32 ns, u64 *keys, u32 *masks, u8 *touched, u8 *ages, u64 tmask, u32 *overflow) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= ns) return;
    Rec r = surv[i];
    if (!tab_or(keys, masks, touched, tmask, r.g, r.m)) { atomicOr(overflow, 1u); return; }
    /* find the slot again to mark it as carried (not touched in the new segment yet) */
    u64 h = hsh(r.g) & tmask; while (keys[h] != r.g) h = (h + 1) & tmask;
    ages[h] = 1; touched[h] = 0;
}
/* coretab: after harvest.  Full active cores set their core bit and are dropped (stats[6]); the others go to the list
   (key, mask); every entry is cleared.  creins puts the list back. */
struct CoreRec { u64 c; u32 m; u32 pad; };
extern "C" __global__ void csweep(u64 *ckeys, u32 *cmasks, u64 ccap, unsigned long long *CB, CoreRec *lst, u32 *nlst, u32 lstcap, u64 *stats, u32 *overflow) {
    u64 ndone = 0;
    for (u64 h = (u64)blockIdx.x * blockDim.x + threadIdx.x; h < ccap; h += (u64)gridDim.x * blockDim.x) {
        u64 c = ckeys[h];
        if (c == EMPTYK) continue;
        u32 m = cmasks[h];
        if (m == P.cfull) { atomicOr(&CB[c >> 6], 1ULL << (c & 63)); ndone++; }
        else { u32 s = atomicAdd(nlst, 1u); if (s < lstcap) { CoreRec r; r.c = c; r.m = m; r.pad = 0; lst[s] = r; } else atomicOr(overflow, 16u); }
        ckeys[h] = EMPTYK; cmasks[h] = 0;
    }
    for (int o = 16; o; o >>= 1) ndone += __shfl_down_sync(0xffffffffu, ndone, o);
    if ((threadIdx.x & 31) == 0 && ndone) atomicAdd(&stats[6], ndone);
}
extern "C" __global__ void creins(const CoreRec *lst, u32 nl, u64 *ckeys, u32 *cmasks, u64 ctmask, u32 *overflow) {
    u32 i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= nl) return;
    CoreRec r = lst[i]; u64 h = chsh(r.c) & ctmask;
    for (int probe = 0; probe < 4096; probe++) {
        u64 old = atomicCAS(&ckeys[h], EMPTYK, r.c);
        if (old == EMPTYK || old == r.c) { atomicOr(&cmasks[h], r.m); return; }
        h = (h + 1) & ctmask;
    }
    atomicOr(overflow, 8u);
}
/* the bits set in B2[0 .. nw) */
extern "C" __global__ void popcnt64(const unsigned long long *B2, u64 nw, u64 *out) {
    u64 c = 0;
    for (u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x; i < nw; i += (u64)gridDim.x * blockDim.x) c += __popcll(B2[i]);
    for (int dd = 16; dd; dd >>= 1) c += __shfl_down_sync(0xffffffffu, c, dd);
    if ((threadIdx.x & 31) == 0) atomicAdd(out, c);
}

/* ------------------------------------------------------------------ expansion of slice descriptors
   A slice (B: n-1 letters, satellite s, v classes) spells B s B (B[t] s rot(B, t+1)) for t < v-1.  A span asks for
   letters from .. from+len-1 of it, written at out[off ..]. */
struct Span { u64 B; u64 off; unsigned short from, len; u8 s, v, pad0, pad1; };
extern "C" __global__ void expand(const Span *__restrict__ sp, u32 nsp, u8 *__restrict__ out) {
    u32 wid = (blockIdx.x * blockDim.x + threadIdx.x) >> 5, lane = threadIdx.x & 31;
    if (wid >= nsp) return;
    Span z = sp[wid];
    const int n1 = P.n - 1;
    for (u32 q = lane; q < z.len; q += 32) {
        int p = z.from + q, c, i;                   /* i: index into B, or -1 for the satellite */
        if (p < n1) i = p;
        else if (p == n1) i = -1;
        else if (p < 2 * n1 + 1) i = p - n1 - 1;
        else {
            int r0 = p - 2 * n1 - 1, t = r0 / (n1 + 2), r = r0 % (n1 + 2);
            if (r == 0) i = t;
            else if (r == 1) i = -1;
            else { int k = t + 1 + r - 2; if (k >= n1) k -= n1; i = k; }
        }
        if (i < 0) c = z.s; else { c = (int)((z.B >> (4 * i)) & 15); c += c >= z.s; }
        out[z.off + q] = (u8)c;
    }
}

/* ------------------------------------------------------------------ SHA-256 of leaves (tree hash)
   leaf i = ASCII letters (alphabet 0-9A-F) of word positions [i*LEAF, (i+1)*LEAF) of the segment; one thread per
   leaf; digest[i] (8 words, big-endian values). */
__constant__ u32 SK[64] = {
0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,
0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,
0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,
0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2};
#define ROR(x,k) __funnelshift_r((x),(x),(k))
__device__ __forceinline__ u32 asc(u32 v) { return v < 10 ? 48 + v : 55 + v; }
__device__ void sha_block(u32 *h, const u32 *w0) {
    u32 w[64];
    for (int i = 0; i < 16; i++) w[i] = w0[i];
    for (int i = 16; i < 64; i++) { u32 s0 = ROR(w[i-15],7)^ROR(w[i-15],18)^(w[i-15]>>3), s1 = ROR(w[i-2],17)^ROR(w[i-2],19)^(w[i-2]>>10); w[i] = w[i-16]+s0+w[i-7]+s1; }
    u32 a=h[0],b=h[1],c=h[2],d=h[3],e=h[4],f=h[5],g=h[6],hh=h[7];
#pragma unroll 8
    for (int i = 0; i < 64; i++) {
        u32 t1 = hh + (ROR(e,6)^ROR(e,11)^ROR(e,25)) + ((e&f)^(~e&g)) + SK[i] + w[i];
        u32 t2 = (ROR(a,2)^ROR(a,13)^ROR(a,22)) + ((a&b)^(a&c)^(b&c));
        hh=g; g=f; f=e; e=d+t1; d=c; c=b; b=a; a=t1+t2;
    }
    h[0]+=a; h[1]+=b; h[2]+=c; h[3]+=d; h[4]+=e; h[5]+=f; h[6]+=g; h[7]+=hh;
}
extern "C" __global__ void leafsha(const u8 *__restrict__ d, u64 len, u32 LEAF, u32 *digest) {
    u64 li = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    u64 a = li * LEAF; if (a >= len) return;
    u64 L = len - a < LEAF ? len - a : LEAF;
    u32 h[8] = {0x6a09e667,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19};
    u32 w[16];
    const u8 *p = d + a;
    u64 nb = L / 64;
    for (u64 bk = 0; bk < nb; bk++) {
        const uint4 *q = (const uint4 *)(p + bk * 64);     /* 64 letters, 16-byte aligned (segments are) */
        for (int k = 0; k < 4; k++) {
            uint4 v = q[k]; u32 x[4] = {v.x, v.y, v.z, v.w};
            for (int m = 0; m < 4; m++) {
                u32 y = x[m];
                w[k * 4 + m] = asc(y & 255) << 24 | asc((y >> 8) & 255) << 16 | asc((y >> 16) & 255) << 8 | asc(y >> 24);
            }
        }
        sha_block(h, w);
    }
    /* tail and padding */
    u32 rem = (u32)(L - nb * 64); u8 buf[128];
    for (u32 k = 0; k < rem; k++) buf[k] = (u8)asc(p[nb * 64 + k]);
    buf[rem] = 0x80; u32 tot = rem + 1 <= 56 ? 64 : 128;
    for (u32 k = rem + 1; k < tot - 8; k++) buf[k] = 0;
    u64 bits = L * 8; for (int k = 0; k < 8; k++) buf[tot - 8 + k] = (u8)(bits >> (56 - 8 * k));
    for (u32 o = 0; o < tot; o += 64) { for (int k = 0; k < 16; k++) w[k] = (u32)buf[o+4*k] << 24 | (u32)buf[o+4*k+1] << 16 | (u32)buf[o+4*k+2] << 8 | buf[o+4*k+3]; sha_block(h, w); }
    for (int k = 0; k < 8; k++) digest[li * 8 + k] = h[k];
}

/* ------------------------------------------------------------------ route A sample: rank and mark a shard */
extern "C" __global__ void rankmark(const u8 *__restrict__ w, u64 nwin, u64 lo, u64 span, u32 *__restrict__ bits, u64 *__restrict__ stats) {
    const int n = P.n; const u32 full = (1u << n) - 1;
    u64 i = (u64)blockIdx.x * blockDim.x + threadIdx.x;
    u32 marked = 0;
    for (; i < nwin; i += (u64)gridDim.x * blockDim.x) {
        const u8 *x = w + i; u32 m = 0;
        for (int k = 0; k < n; k++) m |= 1u << x[k];
        if (m != full) continue;
        u64 r = 0; u32 av = full;
        for (int k = 0; k < n - 1; k++) { u32 bb = 1u << x[k]; r = r * (u64)(n - k) + (u32)__popc(av & (bb - 1)); av &= ~bb; }
        u64 q = r - lo;
        if (q < span) { atomicOr(bits + (q >> 5), 1u << (q & 31)); marked++; }
    }
    if (marked) atomicAdd(&stats[3], (u64)marked);
}
