/* neighbours.c: for every pair of words on n symbols (n <= 8), the largest number of common steps over all
   renamings of the symbols and both reading directions.
   A step of a word is an ordered pair (permutation, next permutation) in the order of first occurrences.
   usage: neighbours N WORDS.txt [SAMPLE]     WORDS.txt: one word per line over the symbols 1..N
   output: i j steps_i steps_j common direction renaming      (i < j, lines of the file counted from 1)
   For speed a renaming is first tried on SAMPLE steps spread over the word (default 300) and counted in full
   only if at least 3 of them are common; two unrelated words share no step at all in practice. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <omp.h>

#define MAXW 128
#define HB 17
#define HS (1u << HB)
static int N, nw, ne[MAXW];
static uint32_t *ep[MAXW], *eq[MAXW];      /* steps of each word, as packed permutations */
static uint32_t *hk[MAXW], *hv[MAXW];      /* hash: permutation -> next permutation */

static inline uint32_t hsh(uint32_t x) { return (x * 2654435761u) >> (32 - HB); }
static inline uint32_t nxt(int w, uint32_t p) {
    uint32_t h = hsh(p);
    while (hk[w][h] && hk[w][h] != p) h = (h + 1) & (HS - 1);
    return hk[w][h] ? hv[w][h] : 0;
}
static inline uint32_t ren(uint32_t p, const int *pi) {
    uint32_t r = 0;
    for (int i = 0; i < N; i++) r |= (uint32_t)pi[(p >> (4 * i)) & 15] << (4 * i);
    return r;
}
static inline uint32_t rev(uint32_t p) {
    uint32_t r = 0;
    for (int i = 0; i < N; i++) r |= ((p >> (4 * i)) & 15) << (4 * (N - 1 - i));
    return r;
}
static void load(int w, const char *s) {
    int L = (int)strlen(s), cnt = 0;
    static uint8_t *seen;
    uint32_t last = 0;
    hk[w] = calloc(HS, 4); hv[w] = calloc(HS, 4);
    ep[w] = malloc(4 * 41000); eq[w] = malloc(4 * 41000);
    for (int i = 0; i + N <= L; i++) {
        uint32_t p = 0, m = 0;
        for (int j = 0; j < N; j++) { int c = s[i + j] - '0'; m |= 1u << c; p |= (uint32_t)c << (4 * j); }
        if (__builtin_popcount(m) != N) continue;
        uint32_t h = hsh(p);
        while (hk[w][h] && hk[w][h] != p) h = (h + 1) & (HS - 1);
        if (hk[w][h]) continue;                      /* seen before */
        hk[w][h] = p;
        if (last) { ep[w][cnt] = last; eq[w][cnt] = p; cnt++; }
        last = p;
    }
    for (int e = 0; e < cnt; e++) {
        uint32_t h = hsh(ep[w][e]);
        while (hk[w][h] != ep[w][e]) h = (h + 1) & (HS - 1);
        hv[w][h] = eq[w][e];
    }
    ne[w] = cnt;
    (void)seen;
}
int main(int argc, char **argv) {
    N = atoi(argv[1]);
    int sample = argc > 3 ? atoi(argv[3]) : 300;
    FILE *f = fopen(argv[2], "r");
    static char buf[200000];
    while (nw < MAXW * 4 && fgets(buf, sizeof buf, f)) {
        buf[strcspn(buf, "\r\n")] = 0;
        if (!buf[0]) continue;
        if (nw >= MAXW) { fprintf(stderr, "too many words\n"); return 1; }
        load(nw++, buf);
    }
    int np = 1; for (int i = 2; i <= N; i++) np *= i;
    int (*perm)[9] = malloc(sizeof(int[9]) * np);
    { int a[9], c = 0; for (int i = 1; i <= N; i++) a[i] = i;      /* all renamings, by Heap's method */
      int st[9] = {0}; memcpy(perm[c++], a, sizeof a);
      for (int i = 1; i < N;) { if (st[i] < i) { int x = (i % 2 == 0) ? 1 : st[i] + 1, y = i + 1, t = a[x]; a[x] = a[y]; a[y] = t;
            memcpy(perm[c++], a, sizeof a); st[i]++; i = 1; } else { st[i] = 0; i++; } } }
    #pragma omp parallel for schedule(dynamic, 1) collapse(1)
    for (int i = 0; i < nw; i++) for (int j = i + 1; j < nw; j++) {
        int best = -1, bd = 0, bp = 0, step = ne[j] / sample ? ne[j] / sample : 1;
        for (int d = 0; d < 2; d++) for (int k = 0; k < np; k++) {
            const int *pi = perm[k];
            int hit = 0;
            for (int e = 0; e < ne[j] && hit < 3; e += step) {
                uint32_t p = ren(ep[j][e], pi), q = ren(eq[j][e], pi);
                if (d) { uint32_t t = rev(q); q = rev(p); p = t; }
                hit += nxt(i, p) == q;
            }
            if (hit < 3) continue;
            int c = 0;
            for (int e = 0; e < ne[j]; e++) {
                uint32_t p = ren(ep[j][e], pi), q = ren(eq[j][e], pi);
                if (d) { uint32_t t = rev(q); q = rev(p); p = t; }
                c += nxt(i, p) == q;
            }
            if (c > best) { best = c; bd = d; bp = k; }
        }
        #pragma omp critical
        { printf("%d %d %d %d %d %s ", i + 1, j + 1, ne[i], ne[j], best < 0 ? 0 : best, bd ? "reversed" : "forward");
          for (int s = 1; s <= N; s++) printf("%d", perm[bp][s]); printf("\n"); fflush(stdout); }
    }
    return 0;
}
