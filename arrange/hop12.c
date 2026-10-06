/* hop12.c - the block programme over the cuts of the big trails of a base word (file of cuts12.c).

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.

   Build:  gcc -O2 -o hop12 hop12.c
   Use:    hop12 CUTS.bin FIRSTCUT SRC.i16 SNK.i16 SRC2.i16 SNK2.i16 HOPS [KMIN] > log
           hop12 CUTS.bin FIRSTCUT SRC.i16 SNK.i16 SRC2.i16 SNK2.i16 ROUNDS KMIN --pot MU [SC] > log

   CUTS.bin   the file of cuts
   FIRSTCUT   the number of the first cut that takes part: the cuts from there to the end of the file are the cuts
              of the big trails (prep_hop.py prints the number)
   SRC, SNK, SRC2, SNK2   one 16-bit number per cut from FIRSTCUT on (prep_hop.py writes them): the cost of
              entering a block at the cut, of leaving it there, and the same for a block at the start and at the end
              of the word
   HOPS       the largest block length k
   KMIN       overlaps below KMIN letters are charged as overlap KMIN - 1 (default 5).  This lowers W, so every
              number printed stays a lower bound of the true value.

   Units.  W(c, d) = 2 (h - largest overlap, at most h, of the end of the piece cut at c with the start of the piece
   cut at d) + D_c + D_d, in half letters; this program works with 2 W.

   The block programme.  A block is a sequence of k cuts of big trails; consecutive cuts lie in different trails.
       v_1(c) = SRC(c),    v_{k+1}(d) = min over cuts c of another trail of v_k(c) + 2 W(c, d),
       B_k = min over d of v_k(d) + SNK(d)
   B_k is twice the smallest W-sum of the k + 1 joins of a block of k big cuts between two cuts outside.  A second
   chain starts from SRC2 (a block at the start of the word, Bs_k), and both are also closed with SNK2 (a block at
   the end, Be_k).  A trail may come back later in a block; a real word writes it once, so the minimum here is over
   a larger set and is a lower bound.
   One step v_k -> v_{k+1} goes through the overlaps KMIN .. h.  For up to 6 letters there is a table over all
   strings of that length; for longer overlaps the cuts sorted by the end of their word are merged with the cuts
   sorted by the start.  For every string the best value and the best value of another trail are kept, so that the
   own trail can be excluded.
   Output: one line per k with B_k, Bs_k, Be_k, the smallest v_k and the smallest and largest v_{k+1} - v_k.

   --pot MU [SC]: a potential.  The program looks for phi <= 0 on the cuts with
       phi(d) <= phi(c) + SC * 2 W(c, d) - MU    for all cuts c, d of different trails,
   by repeating phi <- min(phi, (one step from phi) - MU), at most ROUNDS times.  At a fixed point every join
   between big trails is worth at least MU / SC after the correction by phi, and the program prints
       FIXED POINT: mu = MU / SC per join; every block of k cuts: SC * B_k >= MU (k - 1) + a + b
   with a = min (SC * SRC - phi) and b = min (SC * SNK + phi), and writes phi to hop_phi.i16.  If phi falls below
   -25000 it prints DIVERGES: there is a cycle of joins with mean below MU / SC.

   Everything is exact integer arithmetic in 16-bit values (30000 stands for infinity).
   Memory: about 39 bytes per cut.  At n = 12 with the 37,594,368 big cuts of the piece set: 1.47 GB;
   318 s for the block lengths 1 to 19, 139 s for the potential 7 / 2 (a fixed point after 8 rounds). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define INF 30000
typedef struct __attribute__((packed)) {
    uint64_t w, c;
    uint8_t D, sk;
    uint16_t t;
} Rec;
static uint64_t *W;
static uint8_t *Dc;
static uint16_t *Tr;
static int64_t N;
static int h;
/* code of the last h letters of the word of cut i: what the piece cut there ends with */
static inline uint64_t exitc(int64_t i) {
    return W[i] & ((1ULL << (4 * h)) - 1);
}
/* code of the first h letters of the word of cut i: what the piece cut there starts with */
static inline uint64_t entryc(int64_t i) {
    return W[i] >> (4 * Dc[i]);
}

/* the cuts in sorted order.  kind 0: by the start code; kind 1: by the last k letters of the end code */
static void radix_sort(uint32_t *idx, int kind, int k) {
    uint32_t *tmp = malloc(4 * (size_t)N);
    int bits = kind == 0 ? 4 * h : 4 * k;
    for (int64_t i = 0; i < N; i++)
        idx[i] = (uint32_t)i;
    for (int sh = 0; sh < bits; sh += 12) {
        static int64_t cnt[4097];
        memset(cnt, 0, sizeof(cnt));
        for (int64_t i = 0; i < N; i++) {
            uint64_t key = kind == 0 ? entryc(idx[i]) : (exitc(idx[i]) & ((1ULL << (4 * k)) - 1));
            cnt[((key >> sh) & 4095) + 1]++;
        }
        for (int d = 0; d < 4096; d++)
            cnt[d + 1] += cnt[d];
        for (int64_t i = 0; i < N; i++) {
            uint64_t key = kind == 0 ? entryc(idx[i]) : (exitc(idx[i]) & ((1ULL << (4 * k)) - 1));
            tmp[cnt[(key >> sh) & 4095]++] = idx[i];
        }
        memcpy(idx, tmp, 4 * (size_t)N);
    }
    free(tmp);
}
static uint32_t *ordS, *ordE[16];
static int KMIN = 5;
static int SC = 1;
static int16_t *T1, *T2;
static uint16_t *TT;

/* one step of the programme: vn(d) = min over cuts c of another trail of v(c) + SC * 2 W(c, d).  First the value
   that any pair reaches (overlap charged as KMIN - 1), then the overlaps KMIN .. h.  m1 / m2 and T1 / T2 hold the
   best value and the best value of a second trail. */
static void hop(const int16_t *v, int16_t *vn) {
    for (int64_t i = 0; i < N; i++)
        vn[i] = INF;
    /* floor: any pair */
    {
        int m1 = INF, m2 = INF;
        int t1 = -1;
        for (int64_t i = 0; i < N; i++) {
            int x = v[i] + 2 * SC * Dc[i];
            if (x < m1) {
                if (Tr[i] != t1)
                    m2 = m1;
                m1 = x;
                t1 = Tr[i];
            } else if (x < m2 && Tr[i] != t1)
                m2 = x;
        }
        int add = SC * 4 * (h - (KMIN - 1));
        for (int64_t i = 0; i < N; i++) {
            int x = (Tr[i] == t1 ? m2 : m1) + add + 2 * SC * Dc[i];
            if (x < vn[i])
                vn[i] = (int16_t)(x > INF ? INF : x);
        }
    }
    for (int k = KMIN; k <= h; k++) {
        int add = SC * 4 * (h - k);
        if (4 * k <= 24) { /* dense table over the strings of k letters */
            size_t sz = (size_t)1 << (4 * k);
            uint64_t mask = sz - 1;
            for (size_t i = 0; i < sz; i++) {
                T1[i] = INF;
                T2[i] = INF;
                TT[i] = 65535;
            }
            for (int64_t i = 0; i < N; i++) {
                size_t s = exitc(i) & mask;
                int x = v[i] + 2 * SC * Dc[i];
                if (x >= INF)
                    continue;
                if (x < T1[s]) {
                    if (TT[s] != Tr[i])
                        T2[s] = T1[s];
                    T1[s] = (int16_t)x;
                    TT[s] = Tr[i];
                } else if (x < T2[s] && TT[s] != Tr[i])
                    T2[s] = (int16_t)x;
            }
            int sh = 4 * (h - k);
            for (int64_t i = 0; i < N; i++) {
                size_t s = entryc(i) >> sh;
                int x = (TT[s] == Tr[i] ? T2[s] : T1[s]);
                if (x >= INF)
                    continue;
                x += add + 2 * SC * Dc[i];
                if (x < vn[i])
                    vn[i] = (int16_t)x;
            }
        } else { /* merge of the sources sorted by suffix with the targets sorted by entry */
            const uint32_t *oe = ordE[k];
            uint64_t mask = (1ULL << (4 * k)) - 1;
            int sh = 4 * (h - k);
            int64_t a = 0, b = 0;
            while (a < N && b < N) {
                uint64_t s = exitc(oe[a]) & mask;
                uint64_t tkey = entryc(ordS[b]) >> sh;
                if (tkey < s) {
                    b++;
                    continue;
                }
                int64_t a2 = a;
                int m1 = INF, m2 = INF, t1 = -1;
                while (a2 < N && (exitc(oe[a2]) & mask) == s) {
                    int64_t i = oe[a2];
                    int x = v[i] + 2 * SC * Dc[i];
                    if (x < m1) {
                        if (Tr[i] != t1)
                            m2 = m1;
                        m1 = x;
                        t1 = Tr[i];
                    } else if (x < m2 && Tr[i] != t1)
                        m2 = x;
                    a2++;
                }
                if (tkey == s && m1 < INF) {
                    while (b < N && (entryc(ordS[b]) >> sh) == s) {
                        int64_t i = ordS[b];
                        int x = (Tr[i] == t1 ? m2 : m1);
                        if (x < INF) {
                            x += add + 2 * SC * Dc[i];
                            if (x < vn[i])
                                vn[i] = (int16_t)x;
                        }
                        b++;
                    }
                }
                a = a2;
            }
        }
    }
}
/* read N 16-bit numbers from a file */
static int16_t *rdi16(const char *p) {
    FILE *f = fopen(p, "rb");
    if (!f) {
        perror(p);
        exit(1);
    }
    int16_t *a = malloc(2 * (size_t)N);
    if (fread(a, 2, N, f) != (size_t)N) {
        fprintf(stderr, "short %s\n", p);
        exit(1);
    }
    fclose(f);
    return a;
}

int main(int argc, char **argv) {
    if (argc < 8) {
        fprintf(stderr, "usage\n");
        return 1;
    }
    FILE *f = fopen(argv[1], "rb");
    if (!f) {
        perror(argv[1]);
        return 1;
    }
    int32_t hd[2];
    int64_t nc;
    if (fread(hd, 4, 2, f) != 2 || fread(&nc, 8, 1, f) != 1)
        return 1;
    int n = hd[0], NT = hd[1];
    h = n - 3;
    fseek(f, 16 + 16LL * NT, SEEK_SET);
    int64_t first = atoll(argv[2]);
    N = nc - first;
    int hops = atoi(argv[7]);
    if (argc > 8)
        KMIN = atoi(argv[8]);
    W = malloc(8 * (size_t)N);
    Dc = malloc(N);
    Tr = malloc(2 * (size_t)N);
    fseek(f, 16 + 16LL * NT + (long long)sizeof(Rec) * first, SEEK_SET);
    {
        size_t CH = 1 << 20;
        Rec *buf = malloc(sizeof(Rec) * CH);
        int64_t i = 0;
        while (i < N) {
            size_t g = fread(buf, sizeof(Rec), (N - i) < (int64_t)CH ? (size_t)(N - i) : CH, f);
            if (!g) {
                fprintf(stderr, "short read\n");
                return 1;
            }
            for (size_t j = 0; j < g; j++) {
                W[i + j] = buf[j].w;
                Dc[i + j] = buf[j].D;
                Tr[i + j] = buf[j].t;
            }
            i += g;
        }
        free(buf);
    }
    fclose(f);
    int16_t *src = rdi16(argv[3]), *snk = rdi16(argv[4]), *src2 = rdi16(argv[5]), *snk2 = rdi16(argv[6]);
    clock_t c0 = clock();
    ordS = malloc(4 * (size_t)N);
    radix_sort(ordS, 0, 0);
    for (int k = KMIN; k <= h; k++)
        if (4 * k > 24) {
            ordE[k] = malloc(4 * (size_t)N);
            radix_sort(ordE[k], 1, k);
        }
    {
        size_t sz = (size_t)1 << 24;
        T1 = malloc(2 * sz);
        T2 = malloc(2 * sz);
        TT = malloc(2 * sz);
    }
    fprintf(stderr, "cuts %lld, sorted (%.0fs)\n", (long long)N, (double)(clock() - c0) / CLOCKS_PER_SEC);
    if (argc > 10 && !strcmp(argv[9], "--pot")) {
        /* potential: phi <= 0 with phi(d) <= phi(c) + SC * 2 W(c,d) - MU for all cuts c, d of different trails */
        int MU = atoi(argv[10]);
        SC = argc > 11 ? atoi(argv[11]) : 1;
        int16_t *phi = calloc(N, 2), *vn = malloc(2 * (size_t)N);
        for (int it = 1; it <= hops; it++) {
            hop(phi, vn);
            int64_t ch = 0;
            int mn = 0;
            for (int64_t i = 0; i < N; i++) {
                int x = vn[i] - MU;
                if (x < phi[i]) {
                    phi[i] = (int16_t)x;
                    ch++;
                }
                if (phi[i] < mn)
                    mn = phi[i];
            }
            printf("iteration %d: changed %lld, min phi %d (%.0fs)\n", it, (long long)ch, mn,
                   (double)(clock() - c0) / CLOCKS_PER_SEC);
            fflush(stdout);
            if (!ch) {
                int a = 4 * INF, b = 4 * INF;
                for (int64_t i = 0; i < N; i++) {
                    int x = SC * src[i] - phi[i];
                    if (x < a)
                        a = x;
                    x = SC * snk[i] + phi[i];
                    if (x < b)
                        b = x;
                }
                printf("FIXED POINT: mu = %d / %d per join; every block of k cuts: %d * B_k >= %d (k - 1) + %d + %d\n",
                       MU, SC, SC, MU, a, b);
                FILE *g = fopen("hop_phi.i16", "wb");
                fwrite(phi, 2, N, g);
                fclose(g);
                return 0;
            }
            if (mn < -25000) {
                printf("DIVERGES (a cycle with mean below mu)\n");
                return 0;
            }
        }
        printf("no fixed point within %d iterations\n", hops);
        return 0;
    }
    int16_t *v = src, *vs = src2, *vn = malloc(2 * (size_t)N), *vsn = malloc(2 * (size_t)N);
    printf(
        "# k  B_k (block between two inner cuts)  Bs_k (block at the start)  Be_k (block at the end)  min v_k  [v_k - v_{k-1}: min max]\n");
    for (int k = 1; k <= hops; k++) {
        int B = 4 * INF, Bs = 4 * INF, Be = 4 * INF, mv = INF;
        for (int64_t i = 0; i < N; i++) {
            int x = v[i] + snk[i];
            if (x < B)
                B = x;
            x = vs[i] + snk[i];
            if (x < Bs)
                Bs = x;
            x = v[i] + snk2[i];
            if (x < Be)
                Be = x;
            if (v[i] < mv)
                mv = v[i];
        }
        printf("%d %d %d %d %d", k, B, Bs, Be, mv);
        if (k < hops) {
            hop(v, vn);
            hop(vs, vsn);
            int dmin = INF, dmax = -INF;
            for (int64_t i = 0; i < N; i++) {
                int d = vn[i] - v[i];
                if (d < dmin)
                    dmin = d;
                if (d > dmax)
                    dmax = d;
            }
            printf(" %d %d", dmin, dmax);
            int16_t *t_ = v;
            v = vn;
            vn = t_;
            t_ = vs;
            vs = vsn;
            vsn = t_;
        }
        printf("\n");
        fflush(stdout);
        if (k % 10 == 0)
            fprintf(stderr, "hop %d (%.0fs)\n", k, (double)(clock() - c0) / CLOCKS_PER_SEC);
    }
    return 0;
}
