/* verify.c - check that a word contains every permutation of its alphabet (0-9, A-F) as a contiguous factor.
   Streams the file and keeps one bit per permutation rank (n!/8 bytes: 5 MB for n = 11, 778 MB for n = 13).
   build: cc -O2 -o verify verify.c          usage: verify word.txt */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef long long i64;

int main(int argc, char **argv) {
    if (argc < 2) { fprintf(stderr, "usage: verify word.txt\n"); return 1; }
    FILE *f = fopen(argv[1], "rb"); if (!f) { perror(argv[1]); return 1; }
    int map[256]; for (int c = 0; c < 256; c++) map[c] = -1;
    const char *al = "0123456789ABCDEF"; for (int c = 0; c < 16; c++) map[(unsigned char)al[c]] = c;
    unsigned char *buf = malloc(1 << 24); size_t got = fread(buf, 1, 1 << 24, f);
    int mx = -1; for (size_t i = 0; i < got; i++) { int v = map[buf[i]]; if (v > mx) mx = v; }
    int n = mx + 1; uint64_t fact[16]; fact[0] = 1; for (int i = 1; i < 16; i++) fact[i] = fact[i - 1] * i;
    uint64_t NF = fact[n]; uint8_t *seen = calloc(NF / 8 + 1, 1);
    rewind(f);
    unsigned char ring[16]; int cnt[16] = {0}, dist = 0; i64 L = 0, nperm = 0, distinct = 0;
    while ((got = fread(buf, 1, 1 << 24, f)) > 0) {
        for (size_t i = 0; i < got; i++) {
            int v = map[buf[i]];
            if (v < 0) { if (buf[i] == '\n' || buf[i] == '\r') continue; fprintf(stderr, "bad symbol at %lld\n", L); return 2; }
            if (L >= n) { int leave = ring[L % n]; if (--cnt[leave] == 0) dist--; }
            ring[L % n] = (unsigned char)v; if (cnt[v]++ == 0) dist++;
            L++;
            if (L >= n && dist == n) {
                uint64_t r = 0; int used = 0;
                for (int k = 0; k < n; k++) {
                    int c = ring[(L - n + k) % n], less = __builtin_popcount(used & ((1 << c) - 1));
                    r += (uint64_t)(c - less) * fact[n - 1 - k]; used |= 1 << c;
                }
                nperm++;
                if (!(seen[r >> 3] & (1 << (r & 7)))) { seen[r >> 3] |= (uint8_t)(1 << (r & 7)); distinct++; }
            }
        }
    }
    printf("n=%d length %lld permutation windows %lld distinct %lld/%llu missing %llu: %s\n", n, L, nperm, distinct,
           (unsigned long long)NF, (unsigned long long)(NF - (uint64_t)distinct), (uint64_t)distinct == NF ? "VALID" : "INVALID");
    return (uint64_t)distinct == NF ? 0 : 3;
}
