/* cuts12.c - list every cut of every closed trail of a base word.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

   Build:  gcc -O2 -o cuts12 cuts12.c
   Use:    cuts12 BASE.txt TABLE.tsv OUT.bin [NOLD]

   BASE.txt   a base word in which every closed trail is one piece: the trail written once, followed by its first
              h = n - 3 letters (the base words of gen12.py, geng.py and gen13.py)
   TABLE.tsv  the table of the generator: one line per trail with kind, slices, R, offset of the piece
   OUT.bin    the file of cuts, read by c12.py and hop12.c
   NOLD       the letters below NOLD are renamed, in the order in which they first appear, in the second code of
              every cut (default 7; the scripts here do not read that code)

   A cut.  The word leaves the trail after the permutation window E and enters it again at the window S.  S is the
   window after E, or the one after that when the window between them holds a permutation that occurs twice in the
   trails and is dropped ("skip").  G is the number of letters from E to S, 2 or 3, and D = 3 - G is the cost of the
   cut.  A cut is described completely by the word w of the n - G letters from the start of S to the end of E
   around the trail (at n = 12: 9 letters for G = 3, 10 for G = 2): the piece cut there starts with the first h
   letters of w and ends with the last h letters of w.  Steps of weight 1 are not cut.  A skip whose G would be
   above 3 is left out and counted in the last message.

   Output, binary, little-endian:
     header     int32 n, int32 number of trails, int64 number of cuts
     per trail  int32 R, number of windows, number of cuts, index of its kind (kinds are numbered in the order in
                which they first appear in the table)
     per cut    uint64 w (4 bits per letter, first letter highest), uint64 w with the letters below NOLD renamed,
                uint8 D, uint8 skip (1: the cut drops a repeated permutation), uint16 trail: 20 bytes
   The cuts of a trail are consecutive, in the order of its windows.
   Messages (to stderr): the windows, the distinct permutations (all n! must occur), how many occur twice and more
   often; the cuts by D and by skip; the kinds with their numbers.

   Limits: trail numbers are 16 bits (at most 65,535 trails) and there is one byte of memory per permutation, so
   this is a program for n <= 12.
   Memory and time at n = 12 (7,200 trails, 40,272,960 cuts; the output has 0.8 GB): 2.75 GB and 150 s (measured). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* value of a letter 0-9, A-F; -1 for anything else */
static int val(int c) {
    if (c >= '0' && c <= '9')
        return c - '0';
    if (c >= 'A' && c <= 'F')
        return c - 'A' + 10;
    return -1;
}

int main(int argc, char **argv) {
    if (argc < 4) {
        fprintf(stderr, "usage: cuts12 BASE TABLE OUT [NOLD]\n");
        return 1;
    }
    int NOLD = argc > 4 ? atoi(argv[4]) : 7;
    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror(argv[1]);
        return 1;
    }
    fseek(f, 0, SEEK_END);
    long long L = ftell(f);
    fseek(f, 0, SEEK_SET);
    unsigned char *w = malloc(L + 16);
    if (fread(w, 1, L, f) != (size_t)L)
        return 1;
    fclose(f);
    while (L > 0 && val(w[L - 1]) < 0)
        L--;
    int n = 0;
    for (long long i = 0; i < L; i++) {
        int v = val(w[i]);
        if (v < 0) {
            fprintf(stderr, "bad symbol at %lld\n", i);
            return 1;
        }
        w[i] = (unsigned char)v;
        if (v + 1 > n)
            n = v + 1;
    }
    int h = n - 3;
    /* the table: offset, R and kind of every trail */
    f = fopen(argv[2], "r");
    if (!f) {
        perror(argv[2]);
        return 1;
    }
    int cap = 1 << 20, NT = 0;
    long long *off = malloc(8 * cap);
    int *R = malloc(4 * cap), *kind = malloc(4 * cap);
    char kinds[256][64];
    int nk = 0;
    char kb[64];
    int sl, r;
    long long o;
    while (fscanf(f, "%63s %d %d %lld", kb, &sl, &r, &o) == 4) {
        int k = 0;
        while (k < nk && strcmp(kinds[k], kb))
            k++;
        if (k == nk)
            strcpy(kinds[nk++], kb);
        off[NT] = o;
        R[NT] = r;
        kind[NT] = k;
        NT++;
    }
    fclose(f);
    uint64_t fact[20];
    fact[0] = 1;
    for (int i = 1; i < 20; i++)
        fact[i] = fact[i - 1] * i;
    uint64_t NF = fact[n];
    unsigned char *cnt = calloc(NF, 1);
    /* pass 1: windows of every trail, count of every permutation.  A window is found with a sliding count of the
       distinct letters among n consecutive ones; a permutation is counted under its rank. */
    int **wpos = malloc(sizeof(int *) * NT);
    int *nw = malloc(4 * NT);
    long long totw = 0;
    for (int t = 0; t < NT; t++) {
        const unsigned char *s = w + off[t];
        int Rt = R[t];
        if (off[t] + Rt + h > L) {
            fprintf(stderr, "trail %d runs over the end\n", t);
            return 1;
        }
        for (int i = 0; i < h; i++)
            if (s[Rt + i] != s[i]) {
                fprintf(stderr, "trail %d is not closed\n", t);
                return 1;
            }
        int *pos = malloc(4 * (Rt / 1 + 1));
        int m = 0;
        int c[16];
        memset(c, 0, sizeof(c));
        int distinct = 0;
        for (int i = 0; i < n; i++) {
            if (c[s[i % Rt]]++ == 0)
                distinct++;
        }
        for (int p = 0; p < Rt; p++) {
            if (distinct == n) {
                pos[m++] = p;
                unsigned mask = 0;
                uint64_t rk = 0;
                for (int i = 0; i < n; i++) {
                    int a = s[(p + i) % Rt];
                    int less = __builtin_popcount(mask & ((1u << a) - 1));
                    rk += (uint64_t)(a - less) * fact[n - 1 - i];
                    mask |= 1u << a;
                }
                if (cnt[rk] < 255)
                    cnt[rk]++;
            }
            if (--c[s[p]] == 0)
                distinct--;
            if (c[s[(p + n) % Rt]]++ == 0)
                distinct++;
        }
        wpos[t] = realloc(pos, 4 * (m + 1));
        nw[t] = m;
        totw += m;
    }
    uint64_t dist = 0, dup = 0, more = 0;
    for (uint64_t i = 0; i < NF; i++) {
        if (cnt[i])
            dist++;
        if (cnt[i] == 2)
            dup++;
        if (cnt[i] > 2)
            more++;
    }
    fprintf(stderr, "n=%d trails %d windows %lld distinct permutations %llu of %llu, twice %llu, more often %llu\n", n,
            NT, totw, (unsigned long long)dist, (unsigned long long)NF, (unsigned long long)dup,
            (unsigned long long)more);
    /* pass 2: cuts.  For the step from window i to window i + 1 the plain cut (pass 0) and, if window i + 1 holds
       a repeated permutation, the cut that drops it (pass 1). */
    FILE *g = fopen(argv[3], "wb");
    if (!g) {
        perror(argv[3]);
        return 1;
    }
    int32_t hd[2] = {n, NT};
    int64_t nc = 0;
    fwrite(hd, 4, 2, g);
    fwrite(&nc, 8, 1, g);
    int32_t *th = calloc(4 * (size_t)NT, 4);
    fwrite(th, 4, 4 * (size_t)NT, g);
    long long ncut = 0, nskip = 0, hist[8] = {0}, badG = 0;
    for (int t = 0; t < NT; t++) {
        const unsigned char *s = w + off[t];
        int Rt = R[t];
        int m = nw[t];
        const int *pos = wpos[t];
        int tc = 0;
        for (int i = 0; i < m; i++) {
            int p = pos[i], q = pos[(i + 1) % m];
            int g1 = (q - p + Rt) % Rt;
            if (g1 == 0)
                g1 = Rt;
            int isdup = 0, g2 = 0;
            { /* is window i+1 a duplicated permutation?  then the cut that drops it */
                unsigned mask = 0;
                uint64_t rk = 0;
                for (int a_ = 0; a_ < n; a_++) {
                    int a = s[(q + a_) % Rt];
                    int less = __builtin_popcount(mask & ((1u << a) - 1));
                    rk += (uint64_t)(a - less) * fact[n - 1 - a_];
                    mask |= 1u << a;
                }
                if (cnt[rk] >= 2 && m >= 3) {
                    isdup = 1;
                    int q2 = pos[(i + 2) % m];
                    g2 = (q2 - q + Rt) % Rt;
                    if (g2 == 0)
                        g2 = Rt;
                }
            }
            for (int pass = 0; pass < 2; pass++) {
                int G = pass == 0 ? g1 : g1 + g2;
                if (pass == 1 && !isdup)
                    break;
                if (G < 2)
                    continue;
                if (G > 3) {
                    if (pass == 0) {
                        fprintf(stderr, "gap %d inside trail %d\n", G, t);
                        return 1;
                    }
                    badG++;
                    continue;
                }
                int len = n - G;
                uint64_t code = 0, can = 0;
                int map[16], nx = 0;
                for (int a = 0; a < 16; a++)
                    map[a] = -1;
                for (int a_ = 0; a_ < len; a_++) {
                    int a = s[(p + G + a_) % Rt];
                    code = (code << 4) | (uint64_t)a;
                    int b = a;
                    if (a < NOLD) {
                        if (map[a] < 0)
                            map[a] = nx++;
                        b = map[a];
                    }
                    can = (can << 4) | (uint64_t)b;
                }
                uint8_t D = (uint8_t)(3 - G), sk = (uint8_t)pass;
                uint16_t tt = (uint16_t)t;
                fwrite(&code, 8, 1, g);
                fwrite(&can, 8, 1, g);
                fwrite(&D, 1, 1, g);
                fwrite(&sk, 1, 1, g);
                fwrite(&tt, 2, 1, g);
                ncut++;
                tc++;
                nskip += pass;
                hist[D + 2 * pass]++;
            }
        }
        th[4 * t] = Rt;
        th[4 * t + 1] = m;
        th[4 * t + 2] = tc;
        th[4 * t + 3] = kind[t];
    }
    nc = ncut;
    fseek(g, 8, SEEK_SET);
    fwrite(&nc, 8, 1, g);
    fwrite(th, 4, 4 * (size_t)NT, g);
    fclose(g);
    fprintf(
        stderr,
        "cuts %lld (plain D=0 %lld, D=1 %lld; skip D=0 %lld, D=1 %lld; skip cuts with a gap over 3 left out: %lld)\n",
        ncut, hist[0], hist[1], hist[2], hist[3], badG);
    for (int k = 0; k < nk; k++)
        fprintf(stderr, "kind %d %s\n", k, kinds[k]);
    return 0;
}
