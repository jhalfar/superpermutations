/* Parallel superpermutation verifier (OpenMP): the word is split into T chunks overlapping by n-1 letters; each
   thread slides its window over its chunk and sets the permutation's rank bit in a shared bitset with an atomic OR.
   Then the bitset is popcounted in parallel.  Memory: word + n!/8 bytes (13! -> 778 MB).
   build: gcc -O2 -fopenmp -o verify_par verify_par.c      usage: verify_par word.txt [threads] */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <omp.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif
typedef long long i64;

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: verify_par word.txt [threads]\n"); return 1; }
    int T = argc > 2 ? atoi(argv[2]) : omp_get_max_threads();
    double t0 = omp_get_wtime();
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
    fseek64(f, 0, SEEK_END); i64 sz = ftell64(f); fseek64(f, 0, SEEK_SET);
    unsigned char *W = malloc(sz + 16); i64 got = 0;
    while (got < sz) { size_t r = fread(W + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f); if (!r) break; got += r; }
    fclose(f);
    i64 L = got; while (L > 0 && (W[L - 1] == '\n' || W[L - 1] == '\r')) L--;
    int map[256]; for (int c = 0; c < 256; c++) map[c] = -1;
    const char *al = "0123456789ABCDEF"; for (int c = 0; c < 16; c++) map[(unsigned char)al[c]] = c;
    int mx = -1, bad = 0;
    #pragma omp parallel for num_threads(T) reduction(max:mx) reduction(+:bad)
    for (i64 i = 0; i < L; i++) { int v = map[W[i]]; if (v < 0) bad++; else { W[i] = (unsigned char)v; if (v > mx) mx = v; } }
    if (bad) { fprintf(stderr, "bad symbols: %d\n", bad); return 2; }
    int n = mx + 1; uint64_t fact[16]; fact[0] = 1; for (int i = 1; i < 16; i++) fact[i] = fact[i - 1] * i;
    uint64_t NF = fact[n], NW = NF / 64 + 1;
    uint64_t *seen = calloc(NW, 8);
    double t1 = omp_get_wtime();
    i64 nperm = 0;
    #pragma omp parallel num_threads(T) reduction(+:nperm)
    {
        int tid = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 nwin = L - n + 1, a = nwin * tid / nt, b = nwin * (tid + 1) / nt;   /* windows [a, b) */
        int cnt[16] = {0}, dist = 0;
        for (i64 i = a; i < a + n - 1 && i < L; i++) if (cnt[W[i]]++ == 0) dist++;
        for (i64 p = a; p < b; p++) {
            unsigned char in = W[p + n - 1];
            if (cnt[in]++ == 0) dist++;
            if (dist == n) {
                uint64_t r = 0; int used = 0;
                for (int k = 0; k < n; k++) {
                    int c = W[p + k], less = __builtin_popcount(used & ((1 << c) - 1));
                    r += (uint64_t)(c - less) * fact[n - 1 - k]; used |= 1 << c;
                }
                __atomic_fetch_or(&seen[r >> 6], 1ULL << (r & 63), __ATOMIC_RELAXED);
                nperm++;
            }
            if (--cnt[W[p]] == 0) dist--;
        }
    }
    double t2 = omp_get_wtime();
    i64 distinct = 0;
    #pragma omp parallel for num_threads(T) reduction(+:distinct)
    for (i64 i = 0; i < (i64)NW; i++) distinct += __builtin_popcountll(seen[i]);
    printf("n=%d length %lld permutation windows %lld distinct %lld/%llu missing %llu: %s  (read %.1fs, scan %.1fs, %d threads)\n",
           n, L, nperm, distinct, (unsigned long long)NF, (unsigned long long)(NF - (uint64_t)distinct),
           (uint64_t)distinct == NF ? "VALID" : "INVALID", t1 - t0, t2 - t1, T);
    return (uint64_t)distinct == NF ? 0 : 3;
}
