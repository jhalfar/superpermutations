/* delcheck.c - coverage and single-deletion test of a superpermutation with little memory (OpenMP).

   Same predicate as `literal_check --deletions` of jaypantone/superperm-upper-43-80: a letter can be deleted iff no
   permutation that occurs exactly once is lost.  Two equal permutation windows cannot start less than n positions
   apart, so one deletion destroys at most one occurrence of a permutation; deleting an interior letter of a unique
   window cannot recreate it, deleting its first (last) letter recreates it only if the letter before (after) the
   window is equal.  Hence every unique window starting at s forbids the positions
       [s + (w[s-1] == w[s]),  s + n - (w[s+n-1] == w[s+n])),
   and the deletable positions are the complement of the union of these intervals.

   Memory: 2 bits per permutation (seen, seen twice): 1.56 GB for 13 symbols.  The word is read from disk in blocks
   by every thread, never held in memory.  Pass 1 counts, pass 2 forms the intervals.

   build: gcc -O2 -fopenmp -o delcheck delcheck.c        usage: delcheck word.txt [threads] */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <omp.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif
typedef long long i64;
typedef unsigned long long u64;
#define BLK (1 << 24)

static int n; static u64 fact[16]; static int map[256];
static u64 *seen, *dup;

/* read word letters [from, to) (0-based, as symbols) into buf; returns 0 on failure */
static int read_range(FILE *f, i64 from, i64 to, unsigned char *buf) {
    if (fseek64(f, from, SEEK_SET)) return 0;
    size_t want = (size_t)(to - from), got = fread(buf, 1, want, f);
    if (got != want) return 0;
    for (size_t i = 0; i < want; i++) { int v = map[buf[i]]; if (v < 0) return 0; buf[i] = (unsigned char)v; }
    return 1;
}
static inline u64 rank_of(const unsigned char *p) {
    u64 r = 0; int used = 0;
    for (int k = 0; k < n; k++) { int c = p[k]; r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k]; used |= 1 << c; }
    return r;
}

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: delcheck word.txt [threads]\n"); return 1; }
    int T = argc > 2 ? atoi(argv[2]) : omp_get_max_threads();
    double t0 = omp_get_wtime();
    for (int c = 0; c < 256; c++) map[c] = -1;
    const char *al = "0123456789ABCDEF"; for (int c = 0; c < 16; c++) map[(unsigned char)al[c]] = c;
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
    fseek64(f, 0, SEEK_END); i64 L = ftell64(f);
    /* strip the final newline(s); the alphabet size is the largest symbol of the first block + 1 */
    for (;;) { unsigned char c; if (L == 0) break; fseek64(f, L - 1, SEEK_SET); if (fread(&c, 1, 1, f) != 1) break; if (c == '\n' || c == '\r') L--; else break; }
    { static unsigned char head[1 << 16]; i64 m = L < (1 << 16) ? L : (1 << 16); fseek64(f, 0, SEEK_SET); if (fread(head, 1, (size_t)m, f) != (size_t)m) { fprintf(stderr, "read failed\n"); return 2; }
      int mx = -1; for (i64 i = 0; i < m; i++) { int v = map[head[i]]; if (v > mx) mx = v; } n = mx + 1; }
    fclose(f);
    if (n < 2 || n > 13 || L < n) { fprintf(stderr, "bad word\n"); return 2; }
    fact[0] = 1; for (int i = 1; i < 16; i++) fact[i] = fact[i - 1] * i;
    u64 NF = fact[n], NW = NF / 64 + 1;
    seen = calloc(NW, 8); dup = calloc(NW, 8);
    if (!seen || !dup) { fprintf(stderr, "out of memory\n"); return 2; }
    i64 nwin = L - n + 1, nperm = 0; int bad = 0;
    /* pass 1: occurrence counts (0, 1, 2+) */
    #pragma omp parallel num_threads(T) reduction(+:nperm) reduction(|:bad)
    {
        int tid = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 a = nwin * tid / nt, b = nwin * (tid + 1) / nt;       /* window starts [a, b) */
        unsigned char *buf = malloc(BLK + 64); FILE *g = fopen(argv[1], "rb");
        if (!buf || !g) bad = 1;
        for (i64 p0 = a; p0 < b && !bad; p0 += BLK) {
            i64 p1 = p0 + BLK < b ? p0 + BLK : b;                   /* starts [p0, p1) need letters [p0, p1 + n - 1) */
            if (!read_range(g, p0, p1 + n - 1, buf)) { bad = 1; break; }
            int cnt[16] = {0}, dist = 0;
            for (int k = 0; k < n - 1; k++) if (cnt[buf[k]]++ == 0) dist++;
            for (i64 s = 0; s < p1 - p0; s++) {
                if (cnt[buf[s + n - 1]]++ == 0) dist++;
                if (dist == n) {
                    u64 r = rank_of(buf + s), bit = 1ULL << (r & 63);
                    u64 old = __atomic_fetch_or(&seen[r >> 6], bit, __ATOMIC_RELAXED);
                    if (old & bit) __atomic_fetch_or(&dup[r >> 6], bit, __ATOMIC_RELAXED);
                    nperm++;
                }
                if (--cnt[buf[s]] == 0) dist--;
            }
        }
        if (g) fclose(g);
        free(buf);
    }
    if (bad) { fprintf(stderr, "read failed or bad symbol\n"); return 2; }
    i64 distinct = 0, twice = 0;
    #pragma omp parallel for num_threads(T) reduction(+:distinct,twice)
    for (i64 i = 0; i < (i64)NW; i++) { distinct += __builtin_popcountll(seen[i]); twice += __builtin_popcountll(dup[i]); }
    double t1 = omp_get_wtime();
    /* pass 2: union of the forbidden intervals of the unique windows */
    enum { KEEP = 4096 };
    i64 ndel = 0; i64 *first_del = malloc((size_t)T * KEEP * sizeof(i64)); int *nkeep = calloc((size_t)T, sizeof(int));
    #pragma omp parallel num_threads(T) reduction(+:ndel) reduction(|:bad)
    {
        int tid = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 A = L * tid / nt, B = L * (tid + 1) / nt;               /* positions [A, B) are reported by this thread */
        i64 s0 = A - n > 0 ? A - n : 0, s1 = B < nwin ? B : nwin;   /* window starts that can cover them */
        unsigned char *buf = malloc(BLK + 64); FILE *g = fopen(argv[1], "rb");
        if (!buf || !g) bad = 1;
        i64 covered_end = A;
        for (i64 p0 = s0; p0 < s1 && !bad; p0 += BLK) {
            i64 p1 = p0 + BLK < s1 ? p0 + BLK : s1;                 /* starts [p0, p1) */
            i64 lo = p0 > 0 ? p0 - 1 : 0, hi = p1 + n < L ? p1 + n : L;   /* letters [lo, hi): one before, one after */
            if (!read_range(g, lo, hi, buf)) { bad = 1; break; }
            const unsigned char *w = buf - lo;                      /* w[i] = letter at position i */
            int cnt[16] = {0}, dist = 0;
            for (int k = 0; k < n - 1; k++) if (cnt[w[p0 + k]]++ == 0) dist++;
            for (i64 s = p0; s < p1; s++) {
                if (cnt[w[s + n - 1]]++ == 0) dist++;
                if (dist == n) {
                    u64 r = rank_of(w + s);
                    if (!((dup[r >> 6] >> (r & 63)) & 1)) {
                        i64 first = s + (s > 0 && w[s - 1] == w[s]);
                        i64 stop = s + n - (s + n < L && w[s + n - 1] == w[s + n]);
                        if (first < stop) {
                            while (covered_end < first && covered_end < B) { if (nkeep[tid] < KEEP) first_del[(size_t)tid * KEEP + nkeep[tid]++] = covered_end; ndel++; covered_end++; }
                            if (stop > covered_end) covered_end = stop;
                        }
                    }
                }
                if (--cnt[w[s]] == 0) dist--;
            }
        }
        while (covered_end < B) { if (nkeep[tid] < KEEP) first_del[(size_t)tid * KEEP + nkeep[tid]++] = covered_end; ndel++; covered_end++; }
        if (g) fclose(g);
        free(buf);
    }
    if (bad) { fprintf(stderr, "read failed or bad symbol\n"); return 2; }
    double t2 = omp_get_wtime();
    printf("{\"n\":%d,\"length\":%lld,\"permutation_occurrences\":%lld,\"distinct_permutations\":%lld,\"required_permutations\":%llu,"
           "\"missing_permutations\":%llu,\"extra_occurrences\":%lld,\"permutations_occurring_once\":%lld,\"tested_deletions\":%lld,"
           "\"coverage_preserving_deletions_count\":%lld,\"coverage_preserving_deletions\":[",
           n, L, nperm, distinct, (u64)NF, (u64)(NF - (u64)distinct), nperm - distinct, distinct - twice, L, ndel);
    int printed = 0;
    for (int t = 0; t < T && printed < KEEP; t++) for (int k = 0; k < nkeep[t] && printed < KEEP; k++) printf("%s%lld", printed++ ? "," : "", first_del[(size_t)t * KEEP + k]);
    printf("],\"scan_seconds\":%.1f,\"deletion_seconds\":%.1f,\"threads\":%d}\n", t1 - t0, t2 - t1, T);
    return (u64)distinct == NF ? 0 : 3;
}
