/* letter.c - moves at the level of letters on a superpermutation, independent of the trails.  A tool for
   certificates and for looking at words, not a search: on my words it finds nothing.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   The word is read as a walk through the permutation graph: the windows of n letters that are permutations, in
   order, with the step (number of letters) between consecutive ones.  For two permutations u, v the cheapest way
   to have v follow u is the maximal overlap, d(u,v) = n - overlap, and d obeys the triangle inequality, so every
   question "is there a shorter string that covers these permutations" is an asymmetric travelling-salesman path
   on permutations with weights d.  Tables: one byte per permutation (number of occurrences, perfect ranking) and
   four bytes per permutation (index of its first occurrence); windows are packed into 64 bits, 4 bits a letter.

   modes (first argument, then the word):
     stats WORD                 step weights, pieces, 1-cycle arcs, where the extra occurrences sit
     diff  A B                  B as a re-ordering of stretches of A (breakpoints, step weights at the cuts)
     del   WORD                 exhaustive: delete any substring (any length) and keep coverage
     win   WORD --what joins|dups|gap3|sweep --R r [--nodes N] [--out F]
                                exact re-synthesis of windows (branch and bound): around every join / extra occurrence
                                / weight-3 step with r windows on each side, or "sweep": windows of 2r letters every r
                                letters (covers every window of up to r+1 letters); improvements are applied and written
     reloc WORD [--dm D]        single permutations at expensive places and their cheapest other place
     ex    WORD [--delta D] [--store G] [-v]
                                census of 2-exchanges with gain >= -D; crossing pairs (double bridge) with a net gain
     x3    WORD [--gmin G] [--d1 a --d2 b]
                                all 3-exchanges (move a stretch of any length elsewhere) with gain >= G
     lk    WORD [--wmin w --k K --d0 a --din b] [--out F]
                                sequential exchanges of up to K cuts from every edge of weight >= w
     chain WORD [--joinw J | --base BASE | --events FILE] [--closable C] [--dups] [--D d] [--out F]
                                exact dynamic programme: every unit re-cut anywhere (also inside a 1-cycle), order kept,
                                junctions with maximal overlap
     selftest WORD              the bound of win against a search without it
     ctx   WORD pos [r]         letters and steps around a position
   Every word written is checked here (all permutations present) and should be checked again with delcheck.

   n = 12 fits the same code (32-bit window indices: 2.1 GB index, 0.5 GB counts); n = 13 does not: the index
   (13! entries of 5 bytes) is 31 GB, only the modes that need the counts alone (del, win: 2 bits a permutation)
   carry over, the look-up modes would need batched look-ups (sort the queries by rank, answer them in one pass).

   What it showed (n = 11, the 43,930,623 word): no substring of any length can be deleted, no window of up to 49
   letters can be replaced by a shorter one, and no exchange of 2 or 3 parts or chain of up to 7 cuts makes one
   shorter word.  The exchanges with a gain only make loops that are detached from the word.  The mode chain with
   the trails as units is the fixed-order pass of recut_wide.c in another form: it takes 43,930,628 to 43,930,624.
   Time, n = 11, 2 threads: load 7 seconds, del 14, win sweep up to 25 letters 50 to 60, up to 49 letters 210,
   ex 25, x3 1.5, lk with 7 cuts 4, chain 60; 0.45 to 0.7 GB.

   Where the parts start.  Parts begin with a comment line of dashes or of equal signs, in this order: packing,
   ranking and distance; reading and writing a word; the tables of the word; then the modes: stats, diff, del, the
   neighbours and pieces that the exchanges use, the word as stretches of its windows, ex, x3, reloc, lk, chain,
   win.  main is at the end.

   Build:  gcc -O2 -mpopcnt -fopenmp -o letter letter.c -lm */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <omp.h>

typedef long long i64;
typedef unsigned long long u64;
typedef unsigned int u32;
typedef unsigned char u8;
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

static const char *AL = "0123456789ABCDEF";
static int n;                 /* symbols */
static u64 fact[17], LOW[17]; /* LOW[k]: the low 4k bits */
static u8 *W;
static i64 L;    /* the word as symbols 0..n-1 */
static u8 *CNT;  /* occurrences of every permutation (saturates at 255) */
static u32 *IDX; /* rank -> index (into P) of the first occurrence */
static u32 *P;
static i64 M;  /* starts of the permutation windows; node M is the virtual end/start node V */
static u8 *NU; /* NU[i] = 1: window i is a permutation that occurs more than once */
typedef struct {
    u64 r;
    u32 i;
} Dup;
static Dup *DUP;
static i64 NDUP; /* all occurrences of the non-unique permutations, sorted by rank, index */
static int THREADS = 2;

static double wall(void) {
    return omp_get_wtime();
}

/* ---------- packing, ranking, distance */
static inline u64 pk_at(const u8 *w) {
    u64 v = 0;
    for (int k = 0; k < n; k++)
        v = (v << 4) | w[k];
    return v;
}
static inline u64 pk(i64 i) {
    return pk_at(W + P[i]);
}
/* Rank (0 .. n! - 1) of a window packed 4 bits per letter, first letter highest. */
static inline u64 rank_pk(u64 v) {
    u64 r = 0;
    unsigned used = 0;
    for (int k = 0; k < n; k++) {
        int c = (int)((v >> (4 * (n - 1 - k))) & 15);
        r += (u64)(c - __builtin_popcount(used & ((1u << c) - 1))) * fact[n - 1 - k];
        used |= 1u << c;
    }
    return r;
}
/* letters to append to a so that the string ends with b */
static inline int dist_pk(u64 a, u64 b) {
    for (int k = n - 1; k >= 1; k--)
        if ((a & LOW[k]) == (b >> (4 * (n - k))))
            return n - k;
    return n;
}
static inline int is_perm_pk(u64 v) {
    unsigned m = 0;
    for (int k = 0; k < n; k++)
        m |= 1u << ((v >> (4 * k)) & 15);
    return m == (1u << n) - 1;
}
static void pk_str(u64 v, char *s) {
    for (int k = 0; k < n; k++)
        s[k] = AL[(v >> (4 * (n - 1 - k))) & 15];
    s[n] = 0;
}

/* ---------- word in / out */
static u8 *load_word(const char *path, i64 *len) {
    FILE *f = fopen(path, "rb");
    if (!f)
        DIE("cannot open %s", path);
#if defined(_WIN32)
    _fseeki64(f, 0, SEEK_END);
    i64 sz = _ftelli64(f);
    _fseeki64(f, 0, SEEK_SET);
#else
    fseeko(f, 0, SEEK_END);
    i64 sz = ftello(f);
    fseeko(f, 0, SEEK_SET);
#endif
    u8 *w = malloc(sz + 64);
    if (!w)
        DIE("out of memory");
    i64 got = 0;
    while (got < sz) {
        size_t r = fread(w + got, 1, (size_t)((sz - got) > (1 << 30) ? (1 << 30) : (sz - got)), f);
        if (!r)
            break;
        got += r;
    }
    fclose(f);
    while (got > 0 && (w[got - 1] == '\n' || w[got - 1] == '\r'))
        got--;
    int map[256];
    for (int c = 0; c < 256; c++)
        map[c] = -1;
    for (int c = 0; c < 16; c++)
        map[(u8)AL[c]] = c;
    for (i64 i = 0; i < got; i++) {
        int v = map[w[i]];
        if (v < 0)
            DIE("bad symbol in %s", path);
        w[i] = (u8)v;
    }
    *len = got;
    return w;
}
/* Writes a word (numbers 0 .. n - 1) as text, one line. */
static void save_word(const char *path, const u8 *w, i64 len) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    char *buf = malloc(1 << 20);
    for (i64 a = 0; a < len; a += 1 << 20) {
        i64 b = len - a < (1 << 20) ? len - a : (1 << 20);
        for (i64 k = 0; k < b; k++)
            buf[k] = AL[w[a + k]];
        fwrite(buf, 1, (size_t)b, f);
    }
    fputc('\n', f);
    fclose(f);
    free(buf);
}
/* Finds n from the first letters and fills the tables that depend on it. */
static void init_n(void) {
    int mx = 0;
    for (i64 i = 0; i < L && i < (1 << 16); i++)
        if (W[i] > mx)
            mx = W[i];
    n = mx + 1;
    if (n < 4 || n > 13)
        DIE("n = %d not supported", n);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    LOW[0] = 0;
    for (int k = 1; k < 17; k++)
        LOW[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
}

/* ---------- tables of the word */
static int dup_cmp(const void *a, const void *b) {
    const Dup *x = a, *y = b;
    return x->r < y->r ? -1 : x->r > y->r ? 1 : x->i < y->i ? -1 : x->i > y->i;
}
/* First entry of DUP (sorted by permutation) that is not below r. */
static i64 dup_find(u64 r) {
    i64 lo = 0, hi = NDUP;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (DUP[m].r < r)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
static i64 missing;
/* Builds the tables of the word in W: positions of its permutation windows, occurrences per permutation,
   index of the first occurrence, the list of duplicates; sets `missing`. */
static void build(void) {
    if (fact[n] > 0xFFFFFFF0ULL || L > 0xFFFFFFF0LL)
        DIE("this build keeps 32-bit indices (n <= 12); see the comment at the top of letter.c for n = 13");
    free(P);
    free(NU);
    free(DUP);
    if (!CNT) {
        CNT = malloc(fact[n]);
        IDX = malloc(fact[n] * 4);
        if (!CNT || !IDX)
            DIE("out of memory");
    }
    memset(CNT, 0, fact[n]);
    memset(IDX, 0xFF, fact[n] * 4);
    i64 cap = L - n + 2;
    P = malloc((size_t)cap * 4);
    if (!P)
        DIE("out of memory");
    M = 0;
    int c[16] = {0}, dc = 0;
    for (int k = 0; k < n - 1 && k < L; k++)
        if (c[W[k]]++ == 0)
            dc++;
    for (i64 s = 0; s + n <= L; s++) {
        if (c[W[s + n - 1]]++ == 0)
            dc++;
        if (dc == n) {
            u64 r = rank_pk(pk_at(W + s));
            if (CNT[r] == 0)
                IDX[r] = (u32)M;
            if (CNT[r] < 255)
                CNT[r]++;
            P[M++] = (u32)s;
        }
        if (--c[W[s]] == 0)
            dc--;
    }
    P = realloc(P, (size_t)(M + 2) * 4);
    P[M] = (u32)L;
    P[M + 1] = (u32)L;
    NU = calloc((size_t)M + 2, 1);
    NDUP = 0;
    i64 dcap = 1 << 16;
    DUP = malloc((size_t)dcap * sizeof(Dup));
    for (i64 i = 0; i < M; i++) {
        u64 r = rank_pk(pk(i));
        if (CNT[r] >= 2) {
            NU[i] = 1;
            if (NDUP == dcap) {
                dcap *= 2;
                DUP = realloc(DUP, (size_t)dcap * sizeof(Dup));
            }
            DUP[NDUP].r = r;
            DUP[NDUP].i = (u32)i;
            NDUP++;
        }
    }
    qsort(DUP, (size_t)NDUP, sizeof(Dup), dup_cmp);
    missing = 0;
    for (u64 r = 0; r < fact[n]; r++)
        if (!CNT[r])
            missing++;
}
/* indices of all occurrences of the permutation with packed form v; returns their number (at most 8 are written) */
static inline int occ(u64 v, u32 *out) {
    u64 r = rank_pk(v);
    int c = CNT[r];
    if (c == 0)
        return 0;
    if (c == 1) {
        out[0] = IDX[r];
        return 1;
    }
    i64 k = dup_find(r);
    int m = 0;
    while (k < NDUP && DUP[k].r == r && m < 8)
        out[m++] = DUP[k++].i;
    return m;
}
/* weight of the edge into window i */
static inline int step(i64 i) {
    return i <= 0 || i >= M ? 0 : (int)(P[i] - P[i - 1]);
}

/* ================================================================== stats */
static void mode_stats(void) {
    printf("n=%d length=%lld windows=%lld distinct=%llu missing=%lld extra=%lld head=%u tail=%lld\n", n, L, M,
           fact[n] - missing, missing, M - (i64)(fact[n] - missing), P[0], L - (P[M - 1] + n));
    i64 hs[20] = {0};
    for (i64 i = 1; i < M; i++) {
        int w = step(i);
        hs[w > 19 ? 19 : w]++;
    }
    printf("step weights:");
    i64 waste = 0;
    for (int w = 1; w < 20; w++)
        if (hs[w]) {
            printf(" %d:%lld", w, hs[w]);
            waste += hs[w] * (w - 1);
        }
    printf("\n");
    printf("non-permutation windows %lld + extra occurrences %lld = %lld letters above n!+n-1\n", waste,
           M - (i64)fact[n], waste + M - (i64)fact[n]);
    /* arcs (maximal chains of weight-1 steps) */
    i64 arcs = 1, ah[16] = {0};
    int len = 1;
    for (i64 i = 1; i < M; i++) {
        if (step(i) == 1)
            len++;
        else {
            ah[len > 15 ? 15 : len]++;
            len = 1;
            arcs++;
        }
    }
    ah[len > 15 ? 15 : len]++;
    printf("1-cycle arcs %lld (1-cycles %llu, surplus %lld); arc lengths:", arcs, fact[n - 1], arcs - (i64)fact[n - 1]);
    for (int k = 1; k < 16; k++)
        if (ah[k])
            printf(" %d:%lld", k, ah[k]);
    printf("\n");
    /* pieces: maximal stretches without a step >= 4 */
    i64 np = 1, jc = 0;
    for (i64 i = 1; i < M; i++)
        if (step(i) >= 4) {
            np++;
            jc += step(i);
        }
    printf(
        "pieces %lld, letters in the joins %lld; last window to first window: %d letters (a rotation of the word gains if this is below the heaviest step)\n",
        np, jc, dist_pk(pk(M - 1), pk(0)));
    /* extra occurrences */
    i64 cls[4][4] = {{0}}, nnu = 0, runs = 0, rh[12] = {0}, R0 = 0, Rpos = 0, dj[6] = {0}, ww[12][12] = {{0}};
    i64 *lastj = malloc((size_t)(M + 1) * 8);
    i64 lj = -(1LL << 40);
    for (i64 i = 0; i < M; i++) {
        if (step(i) >= 4)
            lj = i;
        lastj[i] = lj;
    } /* last join at or before i (edge into lj) */
    i64 nj = 1LL << 40;
    u8 *typ = malloc((size_t)M + 1);
    for (i64 i = M - 1; i >= 0; i--) {
        if (NU[i]) {
            int wi = step(i), wo = step(i + 1);
            nnu++;
            int t = (wi >= 4 || wo >= 4 || i == 0 || i == M - 1) ? 3
                    : (wi == 3 || wo == 3)                       ? 2
                    : (wi == 2 || wo == 2)                       ? 1
                                                                 : 0;
            typ[i] = (u8)t;
            ww[wi > 11 ? 11 : wi][wo > 11 ? 11 : wo]++;
            int R = (i > 0 && i < M - 1) ? wi + wo - dist_pk(pk(i - 1), pk(i + 1)) : wi + wo;
            if (R > 0)
                Rpos++;
            else
                R0++;
            i64 dn = nj - i, dp = i - lastj[i] + 1;
            i64 dd = dn < dp ? dn : dp; /* windows to the nearest join */
            dj[dd <= 0 ? 0 : dd <= 1 ? 1 : dd <= 11 ? 2 : dd <= 121 ? 3 : dd <= 1331 ? 4 : 5]++;
        }
        if (step(i) >= 4)
            nj = i;
    }
    for (i64 i = 0; i < M;) {
        if (!NU[i]) {
            i++;
            continue;
        }
        i64 j = i;
        while (j < M && NU[j])
            j++;
        runs++;
        rh[j - i > 11 ? 11 : j - i]++;
        i = j;
    }
    printf("non-unique windows %lld in %lld runs; run lengths:", nnu, runs);
    for (int k = 1; k < 12; k++)
        if (rh[k])
            printf(" %d%s:%lld", k, k == 11 ? "+" : "", rh[k]);
    printf("\n");
    printf("  (step in, step out) of the non-unique windows:");
    for (int a = 0; a < 12; a++)
        for (int b = 0; b < 12; b++)
            if (ww[a][b])
                printf(" (%d,%d):%lld", a, b, ww[a][b]);
    printf("\n");
    printf(
        "  windows to the nearest join (step>=4): at the join %lld, 2..11 %lld, 12..121 %lld, 122..1331 %lld, farther %lld\n",
        dj[0] + dj[1], dj[2], dj[3], dj[4], dj[5]);
    printf("  single removal (drop the window, join its neighbours): saves nothing for %lld, saves letters for %lld\n",
           R0, Rpos);
    /* pairs: type of both copies, same piece or not */
    const char *tn[4] = {"inside-arc(1,1)", "at-gap2", "at-gap3", "at-join"};
    i64 same = 0, multi = 0, pairs = 0;
    for (i64 k = 0; k < NDUP;) {
        i64 e = k;
        while (e < NDUP && DUP[e].r == DUP[k].r)
            e++;
        if (e - k == 2) {
            pairs++;
            int a = typ[DUP[k].i], b = typ[DUP[k + 1].i];
            cls[a < b ? a : b][a < b ? b : a]++;
            if (lastj[DUP[k].i] == lastj[DUP[k + 1].i])
                same++;
        } else
            multi++;
        k = e;
    }
    printf("  permutations occurring twice %lld (both copies in the same piece: %lld), more than twice %lld\n", pairs,
           same, multi);
    for (int a = 0; a < 4; a++)
        for (int b = a; b < 4; b++)
            if (cls[a][b])
                printf("    %s + %s: %lld\n", tn[a], tn[b], cls[a][b]);
    free(lastj);
    free(typ);
}

/* ================================================================== diff: B as stretches of A */
static void mode_diff(const char *pb) {
    i64 LB;
    u8 *B = load_word(pb, &LB);
    /* windows of B */
    i64 mb = 0, bp = 0, fresh = 0, prev = -2, hs[2][20] = {{0}};
    int c[16] = {0}, dc = 0;
    i64 lastpos = -1;
    u64 lastv = 0;
    u8 *cut = calloc((size_t)M + 2, 1); /* cut[i] = 1: A's edge i -> i+1 is not used by B */
    u8 *used = calloc((size_t)M + 2, 1);
    for (int k = 0; k < n - 1; k++)
        if (c[B[k]]++ == 0)
            dc++;
    for (i64 s = 0; s + n <= LB; s++) {
        if (c[B[s + n - 1]]++ == 0)
            dc++;
        if (dc == n) {
            u64 v = pk_at(B + s);
            u32 o[8];
            int m = occ(v, o);
            i64 here = -1;
            for (int k = 0; k < m; k++)
                if ((i64)o[k] == prev + 1)
                    here = o[k];
            if (here < 0 && m) {
                for (int k = 0; k < m; k++)
                    if (!used[o[k]]) {
                        here = o[k];
                        break;
                    }
                if (here < 0)
                    here = o[0];
            }
            if (m == 0)
                fresh++;
            if (mb) {
                int wB = (int)(s - lastpos);
                if (here != prev + 1 || prev < 0) {
                    bp++;
                    hs[1][wB > 19 ? 19 : wB]++;
                }
            }
            if (here >= 0)
                used[here] = 1;
            prev = here;
            lastpos = s;
            lastv = v;
            mb++;
        }
        if (--c[B[s]] == 0)
            dc--;
    }
    (void)lastv;
    /* edges of A that B does not use: recompute by walking B again */
    memset(cut, 1, (size_t)M + 1);
    prev = -2;
    memset(c, 0, sizeof c);
    dc = 0;
    memset(used, 0, (size_t)M + 1);
    for (int k = 0; k < n - 1; k++)
        if (c[B[k]]++ == 0)
            dc++;
    for (i64 s = 0; s + n <= LB; s++) {
        if (c[B[s + n - 1]]++ == 0)
            dc++;
        if (dc == n) {
            u64 v = pk_at(B + s);
            u32 o[8];
            int m = occ(v, o);
            i64 here = -1;
            for (int k = 0; k < m; k++)
                if ((i64)o[k] == prev + 1)
                    here = o[k];
            if (here < 0 && m) {
                for (int k = 0; k < m; k++)
                    if (!used[o[k]]) {
                        here = o[k];
                        break;
                    }
                if (here < 0)
                    here = o[0];
            }
            if (here >= 0 && here == prev + 1)
                cut[prev] = 0;
            if (here >= 0)
                used[here] = 1;
            prev = here;
        }
        if (--c[B[s]] == 0)
            dc--;
    }
    i64 ncut = 0, unused = 0;
    for (i64 i = 0; i + 1 < M; i++)
        if (cut[i]) {
            ncut++;
            int w = step(i + 1);
            hs[0][w > 19 ? 19 : w]++;
        }
    for (i64 i = 0; i < M; i++)
        if (!used[i])
            unused++;
    printf("A: %lld letters, %lld windows;  B: %lld letters, %lld windows (%lld not in A)\n", L, M, LB, mb, fresh);
    printf("B is %lld stretches of A; edges of A not used by B: %lld; windows of A not used by B: %lld\n", bp + 1, ncut,
           unused);
    printf("weights of A's edges that are cut:");
    for (int w = 1; w < 20; w++)
        if (hs[0][w])
            printf(" %d:%lld", w, hs[0][w]);
    printf("\n");
    printf("weights of B's new edges:         ");
    for (int w = 1; w < 20; w++)
        if (hs[1][w])
            printf(" %d:%lld", w, hs[1][w]);
    printf("\n");
    i64 first = -1, last = -1;
    for (i64 i = 0; i + 1 < M; i++)
        if (cut[i]) {
            if (first < 0)
                first = i;
            last = i;
        }
    printf("cut edges span indices %lld .. %lld of A (%lld windows)\n", first, last, last - first);
    free(cut);
    free(used);
    free(B);
}

/* ================================================================== del: every substring deletion that keeps coverage */
static void mode_del(void) {
    /* U[s] = number of windows with start < s that are permutations occurring once */
    u32 *U = malloc((size_t)(L + 2) * 4);
    i64 q = 0, acc = 0;
    for (i64 s = 0; s <= L; s++) {
        U[s] = (u32)acc;
        if (q < M && (i64)P[q] == s) {
            if (!NU[q])
                acc++;
            q++;
        }
    }
    i64 NW = L - n + 1;
    i64 tested[64] = {0}, good[64] = {0};
    i64 maxl = 0, nfound = 0;
#pragma omp parallel for num_threads(THREADS) schedule(dynamic, 65536) reduction(+ : nfound) reduction(max : maxl)
    for (i64 a = 0; a < L; a++) {
        for (i64 l = 1; a + l <= L; l++) {
            i64 lo = a - n + 1 > 0 ? a - n + 1 : 0,
                hi = a + l - 1 < NW - 1 ? a + l - 1 : NW - 1; /* window starts that are lost */
            if (hi < lo)
                break;
            if ((i64)U[hi + 1] - (i64)U[lo] > n - 1)
                break;
            /* exact test: every permutation whose occurrences all start in [lo, hi] must be among the new windows */
            u8 buf[64];
            int bl = 0; /* the letters around the cut: n-1 before, n-1 after */
            i64 b0 = a - (n - 1) > 0 ? a - (n - 1) : 0;
            for (i64 k = b0; k < a; k++)
                buf[bl++] = W[k];
            for (i64 k = a + l; k < a + l + n - 1 && k < L; k++)
                buf[bl++] = W[k];
            u64 nw[32];
            int nn = 0;
            for (int k = 0; k + n <= bl; k++) {
                u64 v = pk_at(buf + k);
                if (is_perm_pk(v))
                    nw[nn++] = v;
            }
            /* lost windows: locate the first window index >= lo by binary search */
            i64 x = 0, y = M;
            while (x < y) {
                i64 m = (x + y) >> 1;
                if ((i64)P[m] < lo)
                    x = m + 1;
                else
                    y = m;
            }
            int ok = 1;
            i64 e = x;
            while (e < M && (i64)P[e] <= hi)
                e++;
            for (i64 i = x; i < e && ok; i++) {
                u64 v = pk(i);
                int in = 0;
                for (int k = 0; k < nn; k++)
                    if (nw[k] == v)
                        in = 1;
                if (in)
                    continue;
                if (!NU[i]) {
                    ok = 0;
                    break;
                }
                int inside = 0;
                for (i64 j = x; j < e; j++)
                    if (pk(j) == v)
                        inside++;
                if (inside >= CNT[rank_pk(v)])
                    ok = 0;
            }
            int lb = l < 63 ? (int)l : 63;
#pragma omp atomic
            tested[lb]++;
            if (ok) {
#pragma omp atomic
                good[lb]++;
                nfound++;
#pragma omp critical
                if (nfound <= 20)
                    printf("DELETABLE: %lld letters at %lld\n", l, a);
            }
            if (l > maxl)
                maxl = l;
        }
    }
    printf("substring deletions: candidates that passed the count filter and were tested exactly, by length:\n ");
    for (int l = 1; l < 64; l++)
        if (tested[l])
            printf(" %d:%lld(%lld ok)", l, tested[l], good[l]);
    printf("\n");
    printf("longest substring that passed the filter: %lld; coverage-preserving deletions found: %lld\n", maxl, nfound);
    free(U);
}

/* ================================================================== neighbours in the permutation graph */
#define DMAXN 9
static u8 *ARR[DMAXN + 1];
static int NARR[DMAXN + 1]; /* all arrangements of d elements */
static void init_arr(void) {
    for (int d = 1; d <= DMAXN; d++) {
        NARR[d] = (int)fact[d];
        ARR[d] = malloc((size_t)NARR[d] * d);
        int a[16];
        for (int k = 0; k < d; k++)
            a[k] = k;
        for (int t = 0; t < NARR[d]; t++) { /* lexicographic successor */
            for (int k = 0; k < d; k++)
                ARR[d][(size_t)t * d + k] = (u8)a[k];
            int i = d - 2;
            while (i >= 0 && a[i] > a[i + 1])
                i--;
            if (i < 0)
                break;
            int j = d - 1;
            while (a[j] < a[i])
                j--;
            int x = a[i];
            a[i] = a[j];
            a[j] = x;
            for (int l = i + 1, r = d - 1; l < r; l++, r--) {
                x = a[l];
                a[l] = a[r];
                a[r] = x;
            }
        }
    }
}
/* t-th permutation at exact distance d after v: v[d..] followed by an arrangement of v[0..d-1] */
static inline u64 succ_at(u64 v, int d, int t) {
    u64 s = (v & LOW[n - d]) << (4 * d);
    const u8 *a = ARR[d] + (size_t)t * d;
    for (int j = 0; j < d; j++)
        s |= ((v >> (4 * (n - 1 - a[j]))) & 15) << (4 * (d - 1 - j));
    return s;
}
/* t-th permutation at exact distance d before v: an arrangement of v[n-d..] followed by v[0..n-d-1] */
static inline u64 pred_at(u64 v, int d, int t) {
    u64 s = v >> (4 * d);
    const u8 *a = ARR[d] + (size_t)t * d;
    for (int j = 0; j < d; j++)
        s |= ((v >> (4 * (d - 1 - a[j]))) & 15) << (4 * (n - 1 - j));
    return s;
}

/* ---------- pieces (maximal stretches without a step >= JOINW) */
static int JOINW = 4;
static u32 *JN;
static i64 NJ; /* JN: indices i with step(i) >= JOINW, increasing */
static void build_joins(void) {
    free(JN);
    NJ = 0;
    for (i64 i = 1; i < M; i++)
        if (step(i) >= JOINW)
            NJ++;
    JN = malloc((size_t)(NJ + 2) * 4);
    NJ = 0;
    for (i64 i = 1; i < M; i++)
        if (step(i) >= JOINW)
            JN[NJ++] = (u32)i;
}
/* The piece that holds letter i (binary search in the joins JN). */
static inline i64 piece_of(i64 i) {
    i64 lo = 0, hi = NJ;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if ((i64)JN[m] <= i)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
static inline i64 piece_first(i64 p) {
    return p == 0 ? 0 : JN[p - 1];
}
static inline i64 piece_last(i64 p) {
    return p == NJ ? M - 1 : (i64)JN[p] - 1;
}

/* ================================================================== the sequence as stretches of the original windows */
/* Nodes are the original window indices 0..M-1 and V = M (virtual node between the end and the start of the word,
   at distance 0 from and to everything): the word is a cyclic tour.  A move cuts some edges and re-orders the
   stretches; SEQ lists the stretches in the current order. */
typedef struct {
    u32 lo, hi;
    i64 base;
} Iv;
static Iv *SEQ;
static int NSEQ, SEQCAP;
static int *BYLO;
static int bylo_cmp(const void *a, const void *b) {
    u32 x = SEQ[*(const int *)a].lo, y = SEQ[*(const int *)b].lo;
    return x < y ? -1 : x > y;
}
/* Sorts the stretches of the current rearrangement by their first window. */
static void seq_index(void) {
    BYLO = realloc(BYLO, (size_t)NSEQ * sizeof(int));
    i64 b = 0;
    for (int k = 0; k < NSEQ; k++) {
        BYLO[k] = k;
        SEQ[k].base = b;
        b += (i64)SEQ[k].hi - SEQ[k].lo + 1;
    }
    qsort(BYLO, (size_t)NSEQ, sizeof(int), bylo_cmp);
}
static void seq_init(void) {
    SEQCAP = 1024;
    SEQ = realloc(SEQ, SEQCAP * sizeof(Iv));
    NSEQ = 1;
    SEQ[0].lo = 0;
    SEQ[0].hi = (u32)M;
    seq_index();
}
/* The stretch of the current rearrangement that holds window i. */
static inline int seq_find(i64 i) {
    int lo = 0, hi = NSEQ - 1;
    while (lo < hi) {
        int m = (lo + hi + 1) >> 1;
        if ((i64)SEQ[BYLO[m]].lo <= i)
            lo = m;
        else
            hi = m - 1;
    }
    return BYLO[lo];
}
static inline i64 seq_pos(i64 i) {
    int k = seq_find(i);
    return SEQ[k].base + (i - SEQ[k].lo);
}
static inline i64 seq_next(i64 i) {
    int k = seq_find(i);
    if (i < (i64)SEQ[k].hi)
        return i + 1;
    return SEQ[k + 1 == NSEQ ? 0 : k + 1].lo;
}
/* distance between nodes */
static inline int nd(i64 a, i64 b) {
    return a == M || b == M ? 0 : dist_pk(pk(a), pk(b));
}

/* best re-ordering of the stretches made by cutting the edges after the nodes cut[0..K-1] (K <= KMAX).
   returns the gain (letters saved, >= 0); ord[] = the stretches in the new cyclic order, as indices into the cuts
   sorted by position: stretch j runs from next(cut_j) to cut_{j+1}; ord[0] = 0. */
#define KMAX 17
typedef struct {
    i64 cut[KMAX], head[KMAX], tail[KMAX];
    int K, ord[KMAX], gain;
} Move;
/* The best order of the stretches, as described above KMAX: a dynamic programme over the sets of stretches
   already placed and the last one of them. */
static int eval_cuts(Move *m, unsigned short *dp /* (1<<(K-1))*(K-1) entries */, u8 *par) {
    int K = m->K;
    i64 pos[KMAX];
    int ix[KMAX];
    for (int j = 0; j < K; j++)
        pos[j] = seq_pos(m->cut[j]);
    for (int j = 0; j < K; j++)
        ix[j] = j;
    for (int a = 1; a < K; a++) {
        int x = ix[a];
        int b = a - 1;
        while (b >= 0 && pos[ix[b]] > pos[x]) {
            ix[b + 1] = ix[b];
            b--;
        }
        ix[b + 1] = x;
    }
    i64 c2[KMAX];
    for (int j = 0; j < K; j++)
        c2[j] = m->cut[ix[j]];
    memcpy(m->cut, c2, sizeof(i64) * K);
    for (int j = 0; j + 1 < K; j++)
        if (m->cut[j] == m->cut[j + 1]) {
            m->gain = 0;
            return 0;
        }
    int old = 0, cst[KMAX][KMAX];
    for (int j = 0; j < K; j++) {
        m->head[j] = seq_next(m->cut[j]);
        m->tail[j] = m->cut[(j + 1) % K];
        old += nd(m->cut[j], m->head[j]);
    }
    for (int a = 0; a < K; a++)
        for (int b = 0; b < K; b++)
            cst[a][b] = nd(m->tail[a], m->head[b]);
    if (K <= 2) {
        m->gain = 0;
        m->ord[0] = 0;
        m->ord[1] = 1;
        return 0;
    }
    int F = K - 1, full = (1 << F) - 1; /* stretches 1..K-1 are free, stretch 0 is first */
    for (int s = 1; s <= full; s++)
        for (int l = 0; l < F; l++)
            dp[(size_t)s * F + l] = 60000;
    for (int l = 0; l < F; l++) {
        dp[(size_t)(1 << l) * F + l] = (unsigned short)cst[0][l + 1];
        par[(size_t)(1 << l) * F + l] = 255;
    }
    for (int s = 1; s <= full; s++)
        for (int l = 0; l < F; l++)
            if ((s >> l) & 1) {
                int v = dp[(size_t)s * F + l];
                if (v >= 60000)
                    continue;
                for (int t = 0; t < F; t++)
                    if (!((s >> t) & 1)) {
                        int s2 = s | (1 << t), nv = v + cst[l + 1][t + 1];
                        if (nv < dp[(size_t)s2 * F + t]) {
                            dp[(size_t)s2 * F + t] = (unsigned short)nv;
                            par[(size_t)s2 * F + t] = (u8)l;
                        }
                    }
            }
    int best = 1 << 30, bl = -1;
    for (int l = 0; l < F; l++) {
        int v = dp[(size_t)full * F + l] + cst[l + 1][0];
        if (v < best) {
            best = v;
            bl = l;
        }
    }
    m->gain = old - best;
    int s = full, l = bl, k = K - 1;
    while (l != 255 && k >= 1) {
        m->ord[k--] = l + 1;
        int pl = par[(size_t)s * F + l];
        s &= ~(1 << l);
        l = pl;
    }
    m->ord[0] = 0;
    return m->gain;
}
/* apply: split the stretches at the cuts and re-order them (m must come from eval_cuts on the current sequence) */
static void apply_move(const Move *m) {
    int K = m->K;
    if (NSEQ + 2 * K + 4 > SEQCAP) {
        SEQCAP = 2 * SEQCAP + 2 * K + 4;
        SEQ = realloc(SEQ, (size_t)SEQCAP * sizeof(Iv));
    }
    for (int j = 0; j < K; j++) { /* split after cut[j] */
        int k = seq_find(m->cut[j]);
        if ((i64)SEQ[k].hi == m->cut[j])
            continue;
        memmove(SEQ + k + 2, SEQ + k + 1, (size_t)(NSEQ - k - 1) * sizeof(Iv));
        NSEQ++;
        SEQ[k + 1].lo = (u32)(m->cut[j] + 1);
        SEQ[k + 1].hi = SEQ[k].hi;
        SEQ[k].hi = (u32)m->cut[j];
        seq_index();
    }
    /* stretch j = entries from the one starting with head[j] to the one ending with tail[j] (cyclic) */
    Iv *nw = malloc((size_t)(NSEQ + 1) * sizeof(Iv));
    int nn = 0;
    for (int o = 0; o < K; o++) {
        int j = m->ord[o];
        int k = seq_find(m->head[j]);
        for (;;) {
            nw[nn++] = SEQ[k];
            if ((i64)SEQ[k].hi == m->tail[j])
                break;
            k = k + 1 == NSEQ ? 0 : k + 1;
            if (nn > NSEQ)
                DIE("apply_move: broken stretch");
        }
    }
    if (nn != NSEQ)
        DIE("apply_move: %d entries instead of %d", nn, NSEQ);
    /* rotate so that V is last, merge neighbours that are consecutive */
    int kv = -1;
    for (int k = 0; k < nn; k++)
        if ((i64)nw[k].hi == M)
            kv = k;
    if (kv < 0)
        DIE("apply_move: V is not a stretch end");
    int o = 0;
    for (int k = 0; k < nn; k++) {
        Iv e = nw[(kv + 1 + k) % nn];
        if (o && SEQ[o - 1].hi + 1 == e.lo)
            SEQ[o - 1].hi = e.hi;
        else
            SEQ[o++] = e;
    }
    NSEQ = o;
    free(nw);
    seq_index();
}
/* write the current sequence as a word */
static u8 *materialize(i64 *len) {
    u8 *out = malloc((size_t)L + 4096);
    i64 o = 0;
    i64 prev = -1;
    for (int k = 0; k < NSEQ; k++) {
        i64 lo = SEQ[k].lo, hi = SEQ[k].hi;
        if (hi == M)
            hi = M - 1;
        if (lo > hi)
            continue; /* drop V */
        i64 a = P[lo], b = (i64)P[hi] + n;
        int ov = prev < 0 ? 0 : n - dist_pk(pk(prev), pk(lo));
        if (o + (b - a) - ov > L + 4000)
            DIE("materialize: the word grew");
        memcpy(out + o, W + a + ov, (size_t)(b - a - ov));
        o += b - a - ov;
        prev = hi;
    }
    *len = o;
    return out;
}

/* ================================================================== census of 2-exchanges */
/* Cutting the edges a -> a+1 and z -> z+1 and adding a -> z+1 and z -> a+1 changes the length by -G and turns the
   stretch between the cuts into a closed loop (or merges a loop).  G >= -DELTA implies that one of the new edges
   is at most floor(DELTA/2) longer than the edge it replaces at the same tail, so the search from every edge
   through the permutations within that distance is complete. */
/* p < q; new edges p -> q+1 (dp), q -> p+1 (dq) */
typedef struct {
    u32 p, q;
    signed char G;
    u8 wp, wq, dp, dq;
} Ex;
static Ex *EX;
static i64 NEX, EXCAP;
/* Counts the 2-exchanges with gain >= -DELTA by gain and by the weights of the edges they cut, and stores
   those with gain >= store_min. */
static void census(int DELTA, int store_min) {
    int half = DELTA / 2;
    i64 cnt[2][32] = {{0}}, inter[32] = {0};
    NEX = 0;
    i64 typ[2][12][12] = {{{0}}};
#pragma omp parallel for num_threads(THREADS) schedule(dynamic, 16384)
    for (i64 a = 0; a < M - 1; a++) {
        int w = step(a + 1), dm = w + half;
        if (dm > DMAXN)
            dm = DMAXN;
        u64 v = pk(a), v1 = pk(a + 1);
        for (int d = 1; d <= dm; d++)
            for (int t = 0; t < NARR[d]; t++) {
                u64 s = succ_at(v, d, t);
                u32 o[8];
                int m = occ(s, o);
                for (int k = 0; k < m; k++) {
                    i64 q = o[k];
                    if (q == a + 1 || q == 0)
                        continue;
                    i64 z = q - 1;
                    if (z == a)
                        continue;
                    int wz = step(q), d2 = dist_pk(pk(z), v1), G = w + wz - d - d2;
                    if (G < -DELTA)
                        continue;
                    if (d2 <= wz + half && d2 <= DMAXN && z < a)
                        continue; /* also found from z: count it there */
                    int same = piece_of(a) == piece_of(z), gi = G + DELTA;
                    if (gi > 31)
                        gi = 31;
#pragma omp atomic
                    cnt[same][gi]++;
                    if (!same && w < JOINW && wz < JOINW) {
#pragma omp atomic
                        inter[gi]++;
                    }
                    if (G >= 0) {
#pragma omp atomic
                        typ[same][w > 11 ? 11 : w][wz > 11 ? 11 : wz]++;
                    }
                    if (G >= store_min) {
#pragma omp critical
                        {
                            if (NEX == EXCAP) {
                                EXCAP = EXCAP ? 2 * EXCAP : 1 << 20;
                                EX = realloc(EX, (size_t)EXCAP * sizeof(Ex));
                                if (!EX)
                                    DIE("out of memory");
                            }
                            Ex e;
                            if (a < z) {
                                e.p = (u32)a;
                                e.q = (u32)z;
                                e.wp = (u8)w;
                                e.wq = (u8)wz;
                                e.dp = (u8)d;
                                e.dq = (u8)d2;
                            } else {
                                e.p = (u32)z;
                                e.q = (u32)a;
                                e.wp = (u8)wz;
                                e.wq = (u8)w;
                                e.dp = (u8)d2;
                                e.dq = (u8)d;
                            }
                            e.G = (signed char)G;
                            EX[NEX++] = e;
                        }
                    }
                }
            }
    }
    printf("2-exchanges with gain >= %d (new edges up to %d letters longer than the old edge at the same tail):\n",
           -DELTA, half);
    for (int g = 31; g >= 0; g--)
        if (cnt[0][g] || cnt[1][g])
            printf("  G=%+d: %lld inside one piece, %lld between two pieces (%lld of them cut no join)\n", g - DELTA,
                   cnt[1][g], cnt[0][g], inter[g]);
    printf("  G>=0 by the weights of the two cut edges (inside one piece | between pieces):");
    for (int a = 1; a < 12; a++)
        for (int b = a; b < 12; b++) {
            i64 x = typ[1][a][b] + (a != b ? typ[1][b][a] : 0), y = typ[0][a][b] + (a != b ? typ[0][b][a] : 0);
            if (x || y)
                printf(" (%d,%d):%lld|%lld", a, b, x, y);
        }
    printf("\n  stored %lld\n", NEX);
}
static int ex_cmp(const void *a, const void *b) {
    const Ex *x = a, *y = b;
    return x->p < y->p ? -1 : x->p > y->p ? 1 : x->q < y->q ? -1 : x->q > y->q;
}
/* Prints one window: its index, its letters, its piece and its place in the piece. */
static void show_node(const char *tag, i64 i) {
    char s[20];
    if (i == M) {
        printf("%s V", tag);
        return;
    }
    pk_str(pk(i), s);
    i64 p = piece_of(i);
    printf("%s %lld[%s piece %lld +%lld/-%lld]", tag, i, s, p, i - piece_first(p), piece_last(p) - i);
}
/* Mode ex: the census of 2-exchanges, then for every exchange with a gain the best one that crosses it. */
static i64 mode_ex(int DELTA, int store_min, int verbose) {
    build_joins();
    seq_init();
    double t = wall();
    census(DELTA, store_min);
    Move bestm;
    bestm.gain = 0;
    fprintf(stderr, "census %.1fs\n", wall() - t);
    qsort(EX, (size_t)NEX, sizeof(Ex), ex_cmp);
    /* positive exchanges, and for each the best crossing partner: two crossing exchanges are a valid move */
    unsigned short *dp = malloc((size_t)(1 << (KMAX - 1)) * (KMAX - 1) * 2);
    u8 *par = malloc((size_t)(1 << (KMAX - 1)) * (KMAX - 1));
    i64 npos = 0, nfix = 0;
    for (i64 e = 0; e < NEX; e++)
        if (EX[e].G >= 1) {
            Ex x = EX[e];
            npos++;
            i64 bestf = -1;
            int bg = -100;
            i64 ncross = 0;
            for (i64 f = 0; f < NEX; f++) {
                Ex y = EX[f];
                if (y.p == x.p || y.p == x.q || y.q == x.p || y.q == x.q)
                    continue;
                int in1 = y.p > x.p && y.p<x.q, in2 = y.q> x.p && y.q < x.q;
                if (in1 == in2)
                    continue;
                ncross++;
                if (y.G > bg) {
                    bg = y.G;
                    bestf = f;
                }
            }
            if (verbose) {
                printf("G=%+d cut ", x.G);
                show_node("", x.p);
                printf(" (w%d) and", x.wp);
                show_node("", x.q);
                printf(" (w%d); new edges %d, %d; loop of %u windows; %lld crossing exchanges, best G=%d\n", x.wq, x.dp,
                       x.dq, x.q - x.p, ncross, bg);
            }
            if (bestf >= 0 && bg + x.G > 0) {
                nfix++;
                Move m;
                m.K = 4;
                m.cut[0] = x.p;
                m.cut[1] = x.q;
                m.cut[2] = EX[bestf].p;
                m.cut[3] = EX[bestf].q;
                eval_cuts(&m, dp, par);
                printf("  DOUBLE BRIDGE gain %d:", m.gain);
                for (int j = 0; j < 4; j++) {
                    show_node("", m.cut[j]);
                    printf("(w%d)", step(m.cut[j] + 1));
                }
                printf("\n");
                if (m.gain > bestm.gain)
                    bestm = m;
            }
        }
    printf("positive 2-exchanges %lld, with a crossing partner that leaves a gain %lld\n", npos, nfix);
    if (bestm.gain > 0)
        apply_move(&bestm);
    free(dp);
    free(par);
    return bestm.gain;
}

/* ================================================================== 3-exchanges (move a stretch elsewhere) */
/* Cuts after a, b, c; new edges a -> b+1, b -> c+1, c -> a+1; valid (one tour) iff a, b, c are in cyclic order.
   A move with positive gain has a rotation in which every partial sum of (old edge - new edge at the same tail)
   is positive, so: start at an edge of weight w >= 2, follow the permutations nearer than w, and so on.
   GMIN: also report moves with gain >= GMIN (<= 0) when their first partial sums are positive. */
typedef struct {
    u32 a, b, c;
    signed char G;
} Ex3;
static Ex3 *E3;
static i64 NE3, E3CAP;
/* All 3-exchanges (a part of the word moved elsewhere) with gain >= GMIN whose new edges have at most D1 / D2
   letters; counts them by gain and stores them. */
static void scan3(int GMIN, int D1, int D2) {
    i64 cnt[40] = {0}, nvalid[40] = {0};
    NE3 = 0;
    i64 look = 0;
#pragma omp parallel for num_threads(THREADS) schedule(dynamic, 4096) reduction(+ : look)
    for (i64 a = 0; a < M - 1; a++) {
        int w = step(a + 1);
        if (w < 2)
            continue;
        u64 va = pk(a), va1 = pk(a + 1);
        for (int d1 = 1; d1 < w && d1 <= D1; d1++)
            for (int t1 = 0; t1 < NARR[d1]; t1++) {
                u32 o1[8];
                int m1 = occ(succ_at(va, d1, t1), o1);
                look++;
                for (int k1 = 0; k1 < m1; k1++) {
                    i64 q = o1[k1];
                    if (q == a + 1 || q == 0)
                        continue;
                    i64 b = q - 1;
                    if (b == a)
                        continue;
                    int g1 = w - d1, wq = step(q);
                    u64 vb = pk(b);
                    int lim = g1 + wq - 1 - (GMIN < 0 ? GMIN : 0);
                    if (lim > D2)
                        lim = D2; /* new edge b -> c+1 of length d2 <= lim */
                    for (int d2 = 1; d2 <= lim; d2++)
                        for (int t2 = 0; t2 < NARR[d2]; t2++) {
                            u32 o2[8];
                            int m2 = occ(succ_at(vb, d2, t2), o2);
                            look++;
                            for (int k2 = 0; k2 < m2; k2++) {
                                i64 r = o2[k2];
                                if (r == q || r == 0 || r == a + 1)
                                    continue;
                                i64 c = r - 1;
                                if (c == a || c == b)
                                    continue;
                                int G = g1 + wq - d2 + step(r) - dist_pk(pk(c), va1);
                                if (G < GMIN)
                                    continue;
                                int valid = (a < b && b < c) || (b < c && c < a) || (c < a && a < b);
                                int gi = G + 20;
                                if (gi > 39)
                                    gi = 39;
                                if (gi < 0)
                                    gi = 0;
#pragma omp atomic
                                cnt[gi]++;
                                if (!valid)
                                    continue;
#pragma omp atomic
                                nvalid[gi]++;
                                if (G > 0 || (G >= GMIN && GMIN <= 0 && NE3 < (1 << 24))) {
#pragma omp critical
                                    {
                                        if (NE3 == E3CAP) {
                                            E3CAP = E3CAP ? 2 * E3CAP : 1 << 16;
                                            E3 = realloc(E3, (size_t)E3CAP * sizeof(Ex3));
                                        }
                                        E3[NE3].a = (u32)a;
                                        E3[NE3].b = (u32)b;
                                        E3[NE3].c = (u32)c;
                                        E3[NE3].G = (signed char)G;
                                        NE3++;
                                    }
                                }
                            }
                        }
                }
            }
    }
    printf(
        "3-exchanges (first new edge <= %d, second <= %d letters; %lld table look-ups), by gain: all found / valid as one tour\n",
        D1, D2, look);
    for (int g = 39; g >= 0; g--)
        if (cnt[g])
            printf("  G=%+d: %lld / %lld\n", g - 20, cnt[g], nvalid[g]);
}
/* Mode x3: runs scan3 and prints the exchanges with a gain. */
static void mode_x3(int GMIN, int D1, int D2, int verbose) {
    build_joins();
    seq_init();
    double t = wall();
    scan3(GMIN, D1, D2);
    fprintf(stderr, "scan3 %.1fs\n", wall() - t);
    i64 shown = 0;
    for (i64 e = 0; e < NE3 && verbose; e++)
        if (E3[e].G > 0 && shown++ < 60) {
            printf("G=%+d", E3[e].G);
            show_node(" a", E3[e].a);
            printf("(w%d)", step(E3[e].a + 1));
            show_node(" b", E3[e].b);
            printf("(w%d)", step(E3[e].b + 1));
            show_node(" c", E3[e].c);
            printf("(w%d)", step(E3[e].c + 1));
            printf(" new %d %d %d\n", nd(E3[e].a, E3[e].b + 1), nd(E3[e].b, E3[e].c + 1), nd(E3[e].c, E3[e].a + 1));
        }
}

/* ================================================================== relocation of single permutations */
/* R(x) = letters saved when window x is dropped and its neighbours are joined directly ("expensive place" if > 0);
   I(x) = cheapest way to cover x between two consecutive windows elsewhere (new letters there).  Net gain R - I.
   Places are found from both sides through the permutations within DM letters before and after x. */
static void mode_reloc(int DM, int verbose) {
    build_joins();
    i64 hR[16] = {0}, hRI[16][16] = {{0}}, pos = 0, best = -100;
    double t0 = wall();
#pragma omp parallel for num_threads(THREADS) schedule(dynamic, 65536) reduction(+ : pos) reduction(max : best)
    for (i64 i = 1; i < M - 1; i++) {
        int wi = step(i), wo = step(i + 1);
        if (wi + wo <= 2)
            continue; /* inside an arc: d(prev, next) = 2 */
        int R = wi + wo - dist_pk(pk(i - 1), pk(i + 1));
        if (NU[i])
            continue; /* a second copy exists: counted in stats */
#pragma omp atomic
        hR[R > 15 ? 15 : R]++;
        if (R <= 0)
            continue;
        u64 x = pk(i);
        int I = 99;
        for (int d = 1; d <= DM; d++)
            for (int t = 0; t < NARR[d]; t++) {
                u32 o[8];
                int m = occ(pred_at(x, d, t), o);
                for (int k = 0; k < m; k++) {
                    i64 j = o[k];
                    if (j == i - 1 || j == i || j >= M - 1)
                        continue;
                    int c = d + dist_pk(x, pk(j + 1)) - step(j + 1);
                    if (c < I)
                        I = c;
                }
                m = occ(succ_at(x, d, t), o);
                for (int k = 0; k < m; k++) {
                    i64 j = o[k];
                    if (j == i + 1 || j == i || j == 0)
                        continue;
                    int c = d + dist_pk(pk(j - 1), x) - step(j);
                    if (c < I)
                        I = c;
                }
            }
        pos++;
        if (R - I > best)
            best = R - I;
#pragma omp atomic
        hRI[R > 15 ? 15 : R][I > 15 ? 15 : I]++;
        if (verbose && R - I > 0) {
#pragma omp critical
            {
                printf("  RELOCATION gain %d:", R - I);
                show_node("", i);
                printf(" (steps %d, %d)\n", wi, wo);
            }
        }
    }
    printf("relocation: unique windows not inside an arc, by the letters R saved when dropped:");
    for (int r = 0; r < 16; r++)
        if (hR[r])
            printf(" %d:%lld", r, hR[r]);
    printf(
        "\n  expensive places (R > 0): %lld; cheapest other place I (letters added there, partners within %d letters), as R/I:count:",
        pos, DM);
    for (int r = 1; r < 16; r++)
        for (int c = 0; c < 16; c++)
            if (hRI[r][c])
                printf(" %d/%d%s:%lld", r, c, c == 15 ? "+" : "", hRI[r][c]);
    printf("\n  best net gain R - I = %lld (%.1fs)\n", best, wall() - t0);
}

/* ================================================================== deep sequential exchanges (Lin-Kernighan style) */
/* cuts c0, c1, ...; new edges c0 -> c1+1, c1 -> c2+1, ..., c(k-1) -> c0+1.  Every partial sum of
   (old edge - new edge) is kept positive, the first new edge is shorter than the first old edge, the later new
   edges are at most DIN letters.  A closed chain is a move if the stretches form one tour. */
#define LKMAX 10
typedef struct {
    u32 cut[LKMAX];
    int k, G;
} LkMove;
typedef struct {
    i64 cut[LKMAX];
    int kmax, din, d0;
    i64 look, budget;
    LkMove *out;
    i64 nout, cap;
    i64 closed[LKMAX + 1], valid[LKMAX + 1], zero_valid[LKMAX + 1];
    int gmin;
} Lk;
/* Do the K cuts, joined in the order of the chain, give one word (and not a word and detached loops)? */
static int lk_valid(const i64 *cut, int K) {
    int rk[LKMAX], nx[LKMAX]; /* rk: rank of a cut by position; stretch r runs from cut r (exclusive) to cut r+1 */
    for (int i = 0; i < K; i++) {
        int r = 0;
        for (int j = 0; j < K; j++)
            if (cut[j] < cut[i])
                r++;
        rk[i] = r;
    }
    for (int i = 0; i < K; i++)
        nx[(rk[i] + K - 1) % K] = rk[(i + 1) % K];
    int f = 0, c = 0;
    do {
        f = nx[f];
        c++;
    } while (f != 0 && c <= K);
    return c == K;
}
/* Sequential exchange, one level: closes the chain at this level if that gains, then tries every next cut
   whose new edge has few enough letters. */
static void lk_dfs(Lk *s, int level, int g) {
    i64 tail = s->cut[level];
    if (level >= 2) {
        int G = g - dist_pk(pk(tail), pk(s->cut[0] + 1));
        if (G >= s->gmin) {
            int K = level + 1;
            s->closed[K]++;
            if (lk_valid(s->cut, K)) {
                if (G > 0)
                    s->valid[K]++;
                else
                    s->zero_valid[K]++;
                if (G > 0 || s->nout < 4096) {
                    if (s->nout == s->cap) {
                        s->cap = s->cap ? 2 * s->cap : 256;
                        s->out = realloc(s->out, (size_t)s->cap * sizeof(LkMove));
                    }
                    LkMove *m = &s->out[s->nout++];
                    m->k = K;
                    m->G = G;
                    for (int i = 0; i < K; i++)
                        m->cut[i] = (u32)s->cut[i];
                }
            }
        }
    }
    if (level + 1 >= s->kmax || s->look > s->budget)
        return;
    u64 v = pk(tail);
    int lim = g - 1, cap = level == 0 ? s->d0 : s->din;
    if (lim > cap)
        lim = cap;
    for (int e = 1; e <= lim; e++)
        for (int t = 0; t < NARR[e]; t++) {
            u32 o[8];
            int m = occ(succ_at(v, e, t), o);
            s->look++;
            for (int k = 0; k < m; k++) {
                i64 q = o[k];
                if (q == 0 || q == tail + 1)
                    continue;
                i64 c = q - 1;
                int used = 0;
                for (int j = 0; j <= level; j++)
                    if (s->cut[j] == c)
                        used = 1;
                if (used)
                    continue;
                s->cut[level + 1] = c;
                lk_dfs(s, level + 1, g - e + step(q));
            }
        }
}
static int lkm_cmp(const void *a, const void *b) {
    const LkMove *x = a, *y = b;
    return y->G - x->G;
}
/* one pass: search from every edge of weight >= wmin; apply the improving moves that are still valid; returns letters saved */
static i64 lk_pass(int wmin, int kmax, int d0, int din, i64 budget, int verbose, int gmin) {
    LkMove *all = NULL;
    i64 nall = 0, acap = 0;
    i64 closed[LKMAX + 1] = {0}, valid[LKMAX + 1] = {0}, zv[LKMAX + 1] = {0}, look = 0, starts = 0, over = 0;
    double t0 = wall();
#pragma omp parallel num_threads(THREADS) reduction(+ : look, starts, over)
    {
        Lk s;
        memset(&s, 0, sizeof s);
        s.kmax = kmax;
        s.din = din;
        s.d0 = d0;
        s.budget = budget;
        s.gmin = gmin;
#pragma omp for schedule(dynamic, 256)
        for (i64 a = 0; a < M - 1; a++) {
            int w = step(a + 1);
            if (w < wmin)
                continue;
            s.look = 0;
            s.cut[0] = a;
            lk_dfs(&s, 0, w);
            look += s.look;
            starts++;
            if (s.look > s.budget)
                over++;
        }
#pragma omp critical
        {
            for (int k = 0; k <= LKMAX; k++) {
                closed[k] += s.closed[k];
                valid[k] += s.valid[k];
                zv[k] += s.zero_valid[k];
            }
            if (nall + s.nout > acap) {
                acap = 2 * (nall + s.nout) + 16;
                all = realloc(all, (size_t)acap * sizeof(LkMove));
            }
            if (s.nout)
                memcpy(all + nall, s.out, (size_t)s.nout * sizeof(LkMove));
            nall += s.nout;
            free(s.out);
        }
    }
    printf(
        "LK pass: starts %lld (weight >= %d), up to %d cuts, first new edge <= %d, later <= %d letters, %lld look-ups (%lld starts over budget), %.1fs\n",
        starts, wmin, kmax, d0, din, look, over, wall() - t0);
    for (int k = 3; k <= kmax; k++)
        printf(
            "  %d cuts: closed chains with gain >= %d: %lld; valid tours with gain > 0: %lld; valid with gain <= 0: %lld\n",
            k, gmin, closed[k], valid[k], zv[k]);
    if (nall)
        qsort(all, (size_t)nall, sizeof(LkMove), lkm_cmp);
    unsigned short *dp = malloc((size_t)(1 << (KMAX - 1)) * (KMAX - 1) * 2);
    u8 *par = malloc((size_t)(1 << (KMAX - 1)) * (KMAX - 1));
    seq_init();
    i64 saved = 0, applied = 0;
    for (i64 i = 0; i < nall; i++) {
        if (all[i].G <= 0)
            break;
        Move m;
        m.K = all[i].k;
        int ok = 1;
        for (int j = 0; j < m.K; j++) {
            m.cut[j] = all[i].cut[j];
            if (seq_next(m.cut[j]) != m.cut[j] + 1)
                ok = 0;
        } /* the cut edges must still exist */
        if (!ok)
            continue;
        if (eval_cuts(&m, dp, par) > 0) {
            if (verbose) {
                printf("  apply gain %d:", m.gain);
                for (int j = 0; j < m.K; j++) {
                    show_node("", m.cut[j]);
                    printf("(w%d)", step(m.cut[j] + 1));
                }
                printf("\n");
            }
            apply_move(&m);
            saved += m.gain;
            applied++;
        }
    }
    printf("  applied %lld moves, saved %lld letters\n", applied, saved);
    fflush(stdout);
    free(dp);
    free(par);
    free(all);
    return saved;
}
/* Mode lk: rounds of sequential exchanges of up to kmax cuts; a round that gains is applied. */
static void mode_lk(int wmin, int kmax, int d0, int din, i64 budget, const char *outpath, int verbose, int gmin) {
    i64 total = 0;
    for (int round = 0; round < 50; round++) {
        build_joins();
        i64 s = lk_pass(wmin, kmax, d0, din, budget, verbose, gmin);
        if (!s)
            break;
        i64 nl;
        u8 *nw = materialize(&nl);
        if (nl != L - s)
            printf("  note: length %lld, expected %lld\n", nl, L - s);
        free(W);
        W = nw;
        L = nl;
        build();
        if (missing)
            DIE("coverage lost after LK moves");
        total += s;
        printf("  word now %lld letters, coverage ok\n", L);
    }
    if (total && outpath) {
        save_word(outpath, W, L);
        printf("wrote %s length %lld\n", outpath, L);
    }
}

/* ================================================================== chain: re-cut every unit, order kept (dynamic programme) */
/* The word is a sequence of units (consecutive stretches of windows).  Every unit is read as a cycle (its last
   window followed by its first, at the cost of their distance) and may be cut after any of its windows, also inside
   a 1-cycle; consecutive units are joined with maximal overlap (1 .. n letters, so junctions of 1, 2, 3 letters and
   shared 1-cycles are included).  F[o] = cheapest cost of everything up to this unit when it is cut after window o.
   Exact: the partners of a head are all cuts of the previous unit; they are found by look-up for junctions of at
   most D letters (the permutations within D letters before the head), through tables of the cheapest cut by the
   last j letters of its tail for the longer junctions (j = 1 .. n-D-1), and (previous minimum) + n for no overlap;
   a small previous unit is simply tried completely.
   Units: --joinw J: maximal stretches without a step >= J (2: 1-cycle arcs, 3: stretches of weight-2 steps, 4: pieces);
          --base WORD: stretches whose windows lie in the same piece of WORD (the trails of a Pantone-form word);
          --closable C: a unit also ends at a step >= C where it closes on its first window within C letters. */
static u32 *US;
static i64 NUN;              /* first window of every unit */
static unsigned short *TRID; /* --base: piece of the base word, by rank */
static void load_base(const char *path) {
    i64 LB;
    u8 *B = load_word(path, &LB);
    TRID = malloc(fact[n] * 2);
    if (!TRID)
        DIE("out of memory");
    memset(TRID, 0xFF, fact[n] * 2);
    int c[16] = {0}, dc = 0;
    i64 last = -1;
    unsigned id = 0;
    for (int k = 0; k < n - 1; k++)
        if (c[B[k]]++ == 0)
            dc++;
    for (i64 s = 0; s + n <= LB; s++) {
        if (c[B[s + n - 1]]++ == 0)
            dc++;
        if (dc == n) {
            if (last >= 0 && s - last >= JOINW) {
                id++;
                if (id >= 0xFFFF)
                    DIE("too many pieces in the base word");
            }
            TRID[rank_pk(pk_at(B + s))] = (unsigned short)id;
            last = s;
        }
        if (--c[B[s]] == 0)
            dc--;
    }
    free(B);
    fprintf(stderr, "base %s: %u pieces\n", path, id + 1);
}
static int SMALLUNIT = 48; /* a previous unit of at most this many windows is tried completely */
static int DUPAWARE = 0;   /* --dups: a unit that ends with a second copy of its first window may drop it */
static const char *EVFILE; /* --events: unit starts = letter positions in the second column */
static void build_units(int closable) {
    free(US);
    US = malloc((size_t)(M + 2) * 4);
    NUN = 0;
    US[NUN++] = 0;
    i64 s = 0;
    unsigned short tprev = TRID ? TRID[rank_pk(pk(0))] : 0;
    if (EVFILE) {
        FILE *f = fopen(EVFILE, "r");
        if (!f)
            DIE("cannot open %s", EVFILE);
        char line[512];
        i64 last = 0;
        while (fgets(line, sizeof line, f)) {
            long long k, pos;
            if (line[0] == '#' || sscanf(line, "%lld %lld", &k, &pos) != 2)
                continue;
            i64 x = 0, y = M;
            while (x < y) {
                i64 m = (x + y) >> 1;
                if ((i64)P[m] < pos)
                    x = m + 1;
                else
                    y = m;
            }
            if (x > last && x < M) {
                US[NUN++] = (u32)x;
                last = x;
            }
        }
        fclose(f);
        US[NUN] = (u32)M;
        EVFILE = NULL;
        return;
    } /* only for the first pass: positions move afterwards */
    for (i64 i = 1; i < M; i++) {
        int w = step(i), cutit = w >= JOINW;
        if (TRID) {
            unsigned short t = TRID[rank_pk(pk(i))];
            if (t != tprev)
                cutit = 1;
            tprev = t;
        }
        if (!cutit && closable && w >= closable && i - s >= 2 && dist_pk(pk(i - 1), pk(s)) <= closable)
            cutit = 1;
        if (cutit) {
            US[NUN++] = (u32)i;
            s = i;
        }
    }
    US[NUN] = (u32)M;
    US = realloc(US, (size_t)(NUN + 2) * 4);
}
/* rank of j distinct letters (packed, first letter highest) among arrangements */
static inline u32 prank(u64 letters, int j) {
    u32 r = 0;
    unsigned used = 0;
    for (int k = 0; k < j; k++) {
        int c = (int)((letters >> (4 * (j - 1 - k))) & 15);
        r = r * (u32)(n - k) + (u32)(c - __builtin_popcount(used & ((1u << c) - 1)));
        used |= 1u << c;
    }
    return r;
}
typedef struct {
    int f;
    u32 o;
    u32 stamp;
} TabE;
/* Mode chain, one pass: shortest path through the units in their order, every unit cut after any of its
   windows, junctions with the largest overlap.  Returns the gain and leaves the new cuts for materialize. */
static i64 chain_pass(int D, int closable, int verbose) {
    build_units(closable);
    double t0 = wall();
    if (D > n - 2)
        D = n - 2;
    int *F = malloc((size_t)M * sizeof(int));
    u32 *BK = malloc((size_t)M * 4);
    if (!F || !BK)
        DIE("out of memory");
    int JT = n - D - 1;
    TabE *T[16];
    u32 TN[16];
    for (int j = 1; j <= JT; j++) {
        TN[j] = 1;
        for (int k = 0; k < j; k++)
            TN[j] *= (u32)(n - k);
        T[j] = calloc(TN[j], sizeof(TabE));
        if (!T[j])
            DIE("out of memory");
    }
    i64 baseline = 0, look = 0;
    int prev_min = 0;
    i64 prev_arg = 0;
    int prev_small = 1;
    for (i64 p = 0; p < NUN; p++) {
        i64 f = US[p], l = (i64)US[p + 1] - 1;
        int cl = f == l ? 0 : dist_pk(pk(l), pk(f));
        int same = DUPAWARE && l - f >= 2 && pk(l) == pk(f),
            cls = same ? dist_pk(pk(l - 1), pk(f)) : 0; /* the unit ends with a second copy of its first window */
        i64 pf = p ? US[p - 1] : 0, pl = p ? f - 1 : 0;
        if (p)
            baseline += step(f);
#pragma omp parallel for num_threads(THREADS) schedule(static) reduction(+ : look) if (l - f > 20000)
        for (i64 o = f; o <= l; o++) {
            i64 h = o == l ? f : o + 1;
            int delta = o == l ? 0 : cl - step(o + 1);
            if (same && o < l) {
                h = o == l - 1 ? f : o + 1;
                delta = (o == l - 1 ? 0 : cls - step(o + 1)) - step(l);
            } /* the second copy is dropped */
            if (p == 0) {
                F[o] = delta;
                BK[o] = 0xFFFFFFFFu;
                continue;
            }
            u64 hv = pk(h);
            int best;
            u32 bo;
            if (prev_small) {
                best = 1 << 30;
                bo = (u32)pl;
                for (i64 q = pf; q <= pl; q++) {
                    int c = F[q] + dist_pk(pk(q), hv);
                    if (c < best) {
                        best = c;
                        bo = (u32)q;
                    }
                }
            } else {
                best = prev_min + n;
                bo = (u32)prev_arg;
                for (int j = 1; j <= JT; j++) {
                    TabE *e = &T[j][prank(hv >> (4 * (n - j)), j)];
                    if (e->stamp == (u32)p && e->f + n - j < best) {
                        best = e->f + n - j;
                        bo = e->o;
                    }
                }
                for (int d = 1; d <= D; d++)
                    for (int t = 0; t < NARR[d]; t++) {
                        u32 oc[8];
                        int m = occ(pred_at(hv, d, t), oc);
                        look++;
                        for (int k = 0; k < m; k++)
                            if ((i64)oc[k] >= pf && (i64)oc[k] <= pl) {
                                int c = F[oc[k]] + d;
                                if (c < best) {
                                    best = c;
                                    bo = oc[k];
                                }
                            }
                    }
            }
            F[o] = best + delta;
            BK[o] = bo;
        }
        /* minimum of this unit; tables by the last j letters of the tails (stamp p+1 = "previous unit of p+1") */
        prev_min = 1 << 30;
        for (i64 o = f; o <= l; o++)
            if (F[o] < prev_min) {
                prev_min = F[o];
                prev_arg = o;
            }
        prev_small = l - f + 1 <= SMALLUNIT;
        if (!prev_small)
            for (i64 o = f; o <= l; o++) {
                u64 v = pk(o);
                for (int j = 1; j <= JT; j++) {
                    TabE *e = &T[j][prank(v & LOW[j], j)];
                    if (e->stamp != (u32)(p + 1) || F[o] < e->f) {
                        e->stamp = (u32)(p + 1);
                        e->f = F[o];
                        e->o = (u32)o;
                    }
                }
            }
    }
    i64 lf = US[NUN - 1], ll = M - 1, bo = ll;
    for (i64 o = lf; o <= ll; o++)
        if (F[o] < F[bo])
            bo = o;
    i64 gain = baseline - F[bo];
    i64 recut = 0, jh[16] = {0}, gap1 = 0, dropped = 0;
    i64 *cutp = malloc((size_t)NUN * 8);
    {
        i64 o = bo;
        for (i64 p = NUN - 1; p >= 0; p--) {
            cutp[p] = o;
            o = BK[o];
        }
    }
    SEQCAP = (int)(2 * NUN + 8);
    SEQ = realloc(SEQ, (size_t)SEQCAP * sizeof(Iv));
    NSEQ = 0;
    for (i64 p = 0; p < NUN; p++) {
        i64 f = US[p], l = (i64)US[p + 1] - 1, o = cutp[p];
#define PUSH(a, b)                                    \
    do {                                              \
        if (NSEQ && SEQ[NSEQ - 1].hi + 1 == (u32)(a)) \
            SEQ[NSEQ - 1].hi = (u32)(b);              \
        else {                                        \
            SEQ[NSEQ].lo = (u32)(a);                  \
            SEQ[NSEQ].hi = (u32)(b);                  \
            NSEQ++;                                   \
        }                                             \
    } while (0)
        int same = DUPAWARE && l - f >= 2 && pk(l) == pk(f);
        i64 h = o == l ? f : o + 1;
        if (o == l)
            PUSH(f, l);
        else if (same) {
            recut++;
            dropped++;
            if (o == l - 1)
                h = f;
            else
                PUSH(o + 1, l - 1);
            PUSH(f, o);
        } else {
            recut++;
            if (step(o + 1) == 1)
                gap1++;
            PUSH(o + 1, l);
            PUSH(f, o);
        }
        if (p && (o != l || cutp[p - 1] != f - 1)) {
            int d = dist_pk(pk(cutp[p - 1]), pk(h));
            jh[d]++;
        }
    }
    SEQ[NSEQ].lo = SEQ[NSEQ].hi = (u32)M;
    NSEQ++;
    seq_index();
    printf(
        "chain: %lld units (largest previous-unit look-ups within %d letters: %lld), junction letters %lld -> %lld (gain %lld); units re-cut %lld (inside a 1-cycle: %lld, second copies dropped: %lld); changed junctions by weight:",
        NUN, D, look, baseline, baseline - gain, gain, recut, gap1, dropped);
    for (int d = 1; d <= n; d++)
        if (jh[d])
            printf(" %d:%lld", d, jh[d]);
    printf(" (%.1fs)\n", wall() - t0);
    if (verbose)
        for (i64 p = 0; p < NUN; p++)
            if (cutp[p] != (i64)US[p + 1] - 1) {
                i64 o = cutp[p];
                printf("  unit %lld (%lld windows from %u) cut after +%lld (step %d there)\n", p,
                       (i64)US[p + 1] - US[p], US[p], o - US[p], step(o + 1));
            }
    for (int j = 1; j <= JT; j++)
        free(T[j]);
    free(F);
    free(BK);
    free(cutp);
    return gain;
}
/* Mode chain: passes until one gains nothing; the word is written if it got shorter. */
static void mode_chain(int D, int closable, int rounds, const char *outpath, int verbose) {
    i64 total = 0;
    for (int r = 0; r < rounds; r++) {
        i64 g = chain_pass(D, closable, verbose);
        if (g <= 0)
            break;
        i64 nl;
        u8 *nw = materialize(&nl);
        i64 oldL = L;
        free(W);
        W = nw;
        L = nl;
        build();
        if (missing)
            DIE("coverage lost after the chain pass");
        printf("  word now %lld letters (%lld shorter), coverage ok\n", L, oldL - L);
        total += oldL - L;
        fflush(stdout);
        if (oldL - L <= 0)
            break;
    }
    if (total > 0 && outpath) {
        save_word(outpath, W, L);
        printf("wrote %s length %lld\n", outpath, L);
    }
}

/* ================================================================== window re-synthesis (exact) */
/* A window of the word, first and last n-1 letters fixed (so every window of n letters that is not completely
   inside keeps its letters).  REQ = the permutations all of whose occurrences are inside.  The shortest string
   with the same first and last n-1 letters that contains REQ is a shortest Hamiltonian path START -> REQ -> END
   with c(u,v) = letters added by maximal overlap (triangle inequality: no other permutation is ever needed).
   Depth-first branch and bound.  Lower bound for the rest: every uncovered permutation costs one letter; the
   uncovered ones fall into arcs (chains of weight-1 steps inside a 1-cycle), the first visit to an arc comes from
   outside it, these first entries form an arborescence over the arcs rooted at the current end, so the bound is
   (uncovered) + (minimum spanning arborescence with weights entry-1) + (cheapest way to the END context). */
#define WK 256
typedef struct {
    u64 w[4];
} Bits;
typedef struct {
    u64 key;
    unsigned short cost;
    unsigned short gen;
} Memo;
typedef struct {
    int k;
    u64 pv[WK];
    u8 c[WK + 2][WK + 2];
    short rsucc[WK], rpred[WK];
    u8 outord[WK + 2][WK];
    u64 zob[WK + 2];
    int best, limit_hit;
    i64 nodes, node_limit;
    int path[WK], bpath[WK], bn;
    Memo *memo;
    int mbits;
    unsigned short gen;
    int ew[WK + 1][WK + 1], nw2[WK + 1][WK + 1];
    int last_lb,
        root_how; /* root_how: 0 no wasted window, 1 pruned by the sum of entries, 2 by the arborescence, 3 searched */
} Win;
static int NOBOUND = 0; /* test switch: search with the trivial bound only */
static inline int bget(const Bits *b, int i) {
    return (int)((b->w[i >> 6] >> (i & 63)) & 1);
}
static inline void bset(Bits *b, int i) {
    b->w[i >> 6] |= 1ULL << (i & 63);
}
static u64 rng_s = 0x9E3779B97F4A7C15ULL;
/* The next 64 random bits (splitmix64). */
static inline u64 rng(void) {
    u64 z = (rng_s += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
/* minimum spanning arborescence, dense (Chu-Liu/Edmonds); g is destroyed */
static int msa(int V, int root, int g[WK + 1][WK + 1], int tmp[WK + 1][WK + 1]) {
    int res = 0, in[WK + 1], pre[WK + 1], id[WK + 1], vis[WK + 1];
    for (;;) {
        for (int v = 0; v < V; v++) {
            in[v] = 1 << 28;
            pre[v] = -1;
            if (v == root)
                continue;
            for (int u = 0; u < V; u++)
                if (u != v && g[u][v] < in[v]) {
                    in[v] = g[u][v];
                    pre[v] = u;
                }
        }
        int cnt = 0;
        for (int v = 0; v < V; v++) {
            id[v] = -1;
            vis[v] = -1;
        }
        in[root] = 0;
        for (int v = 0; v < V; v++) {
            res += in[v];
            int u = v;
            while (vis[u] != v && id[u] == -1 && u != root) {
                vis[u] = v;
                u = pre[u];
            }
            if (u != root && id[u] == -1) {
                for (int x = pre[u]; x != u; x = pre[x])
                    id[x] = cnt;
                id[u] = cnt++;
            }
        }
        if (cnt == 0)
            return res;
        for (int v = 0; v < V; v++)
            if (id[v] == -1)
                id[v] = cnt++;
        for (int a = 0; a < cnt; a++)
            for (int b = 0; b < cnt; b++)
                tmp[a][b] = 1 << 28;
        for (int u = 0; u < V; u++)
            for (int v = 0; v < V; v++)
                if (id[u] != id[v] && g[u][v] < (1 << 28)) {
                    int x = g[u][v] - in[v];
                    if (x < tmp[id[u]][id[v]])
                        tmp[id[u]][id[v]] = x;
                }
        for (int a = 0; a < cnt; a++)
            for (int b = 0; b < cnt; b++)
                g[a][b] = tmp[a][b];
        root = id[root];
        V = cnt;
    }
}
/* Lower bound for the rest of a window: the permutations not yet covered must each be entered once and the
   end reached (a minimum spanning arborescence over them). */
static int win_lb(Win *w, int cur, const Bits *cov, int nunc) {
    int k = w->k, END = k + 1, uid[WK], U = 0, list[WK], nl = 0, endmin = 1 << 20;
    for (int v = 0; v < k; v++) {
        uid[v] = -1;
        if (!bget(cov, v)) {
            list[nl++] = v;
            if (w->c[v][END] < endmin)
                endmin = w->c[v][END];
        }
    }
    for (int x = 0; x < nl; x++) {
        int v = list[x];
        if (uid[v] >= 0)
            continue;
        int p = w->rpred[v];
        if (p >= 0 && !bget(cov, p))
            continue; /* not a head */
        for (int y = v; y >= 0 && !bget(cov, y) && uid[y] < 0; y = w->rsucc[y])
            uid[y] = U;
        U++;
    }
    for (int x = 0; x < nl; x++) {
        int v = list[x];
        if (uid[v] >= 0)
            continue; /* a complete 1-cycle: no head */
        for (int y = v; y >= 0 && uid[y] < 0; y = w->rsucc[y])
            uid[y] = U;
        U++;
    }
    /* cheapest entries */
    int minin[WK + 1];
    for (int a = 0; a < U; a++)
        minin[a] = 1 << 20;
    for (int x = 0; x < nl; x++) {
        int v = list[x], a = uid[v];
        if (w->c[cur][v] - 1 < minin[a])
            minin[a] = w->c[cur][v] - 1;
    }
    int fromcur[WK + 1];
    for (int a = 0; a < U; a++)
        fromcur[a] = minin[a];
    for (int a = 0; a <= U; a++)
        for (int b = 0; b <= U; b++)
            w->ew[a][b] = 1 << 28;
    for (int x = 0; x < nl; x++) {
        int u = list[x], a = uid[u];
        const u8 *cu = w->c[u];
        for (int y = 0; y < nl; y++) {
            int v = list[y], b = uid[v];
            if (a == b)
                continue;
            int e = cu[v] - 1;
            if (e < w->ew[a][b]) {
                w->ew[a][b] = e;
                if (e < minin[b])
                    minin[b] = e;
            }
        }
    }
    int lb1 = nunc + endmin;
    for (int a = 0; a < U; a++)
        lb1 += minin[a];
    w->last_lb = 1;
    if (lb1 + 0 >= w->best)
        return lb1; /* caller compares cost + lb with best */
    w->last_lb = 2;
    w->ew[0][0] = 0;
    (void)fromcur;
    for (int a = 0; a < U; a++)
        w->ew[U][a] = fromcur[a];
    return nunc + endmin + msa(U + 1, U, w->ew, w->nw2);
}
/* Branch and bound over the orders of the required permutations of one window. */
static void win_dfs(Win *w, int cur, Bits cov, int ncov, int cost, u64 h) {
    int k = w->k, END = k + 1;
    if (ncov == k) {
        int tot = cost + w->c[cur][END];
        if (tot < w->best) {
            w->best = tot;
            w->bn = k;
            memcpy(w->bpath, w->path, sizeof(int) * k);
        }
        return;
    }
    if (++w->nodes > w->node_limit) {
        w->limit_hit = 1;
        return;
    }
    if (cost + (k - ncov) >= w->best)
        return;
    {
        u64 key = h ^ w->zob[cur] * 0x2545F4914F6CDD1DULL;
        Memo *e = &w->memo[key & ((1ULL << w->mbits) - 1)];
        if (e->gen == w->gen && e->key == key && e->cost <= cost)
            return;
        if (e->gen != w->gen || e->key == key || 1) {
            e->gen = w->gen;
            e->key = key;
            e->cost = (unsigned short)cost;
        }
    }
    /* bound: quick sum of minimal entries, then the arborescence */
    if (!NOBOUND) {
        int save = w->best;
        w->best = save - cost;
        int lb = win_lb(w, cur, &cov, k - ncov);
        w->best = save;
        if (cost + lb >= w->best) {
            if (ncov == 0)
                w->root_how = w->last_lb;
            return;
        }
    }
    if (ncov == 0)
        w->root_how = 3;
    const u8 *ord = w->outord[cur];
    for (int x = 0; x < k; x++) {
        int v = ord[x];
        if (bget(&cov, v))
            continue;
        int c2 = cost + w->c[cur][v];
        if (c2 + (k - ncov - 1) >= w->best)
            break;
        Bits nc = cov;
        bset(&nc, v);
        w->path[ncov] = v;
        win_dfs(w, v, nc, ncov + 1, c2, h ^ w->zob[v]);
        if (w->limit_hit)
            return;
    }
}
/* longest suffix of a (la letters) = prefix of b (lb letters), at most min(la,lb,n-1) */
static inline int ov_gen(u64 a, int la, u64 b, int lb) {
    int m = la < lb ? la : lb;
    if (m > n - 1)
        m = n - 1;
    for (int j = m; j >= 1; j--)
        if ((a & LOW[j]) == (b >> (4 * (lb - j))))
            return j;
    return 0;
}
/* solve the window W[a..b) (b - a >= n - 1); returns the new length (== b - a if nothing shorter was found) and writes
   the new string to out.  *status: 0 proved optimal, 1 improved (and the search finished), 2 node limit hit */
static int win_solve(Win *w, i64 a, i64 b, u8 *out, int *status, int *kout) {
    int len = (int)(b - a), k = 0;
    *status = 0;
    *kout = 0;
    /* required permutations */
    i64 x = 0, y = M;
    while (x < y) {
        i64 m = (x + y) >> 1;
        if ((i64)P[m] < a)
            x = m + 1;
        else
            y = m;
    }
    i64 i0 = x, i1 = x;
    while (i1 < M && (i64)P[i1] + n <= b)
        i1++;
    for (i64 i = i0; i < i1; i++) {
        u64 v = pk(i);
        int dupl = 0;
        for (int j = 0; j < k; j++)
            if (w->pv[j] == v)
                dupl = 1;
        if (dupl)
            continue;
        if (NU[i]) {
            int inside = 0;
            for (i64 j = i0; j < i1; j++)
                if (pk(j) == v)
                    inside++;
            if (inside < CNT[rank_pk(v)])
                continue;
        }
        if (k == WK) {
            *status = 2;
            return len;
        }
        w->pv[k++] = v;
    }
    *kout = k;
    w->root_how = 0;
    if (len - (n - 1) <= k)
        return len; /* no window of n letters is wasted */
    int START = k, END = k + 1;
    u64 sv = 0, evv = 0;
    for (int j = 0; j < n - 1; j++) {
        sv = (sv << 4) | W[a + j];
        evv = (evv << 4) | W[b - (n - 1) + j];
    }
    w->k = k;
    for (int u = 0; u < k; u++) {
        for (int v = 0; v < k; v++)
            w->c[u][v] = (u8)(u == v ? 0 : dist_pk(w->pv[u], w->pv[v]));
        w->c[START][u] = (u8)(n - ov_gen(sv, n - 1, w->pv[u], n));
        w->c[u][END] = (u8)(n - 1 - ov_gen(w->pv[u], n, evv, n - 1));
        w->c[u][START] = 255;
        w->c[END][u] = 255;
    }
    w->c[START][END] = (u8)(n - 1 - ov_gen(sv, n - 1, evv, n - 1));
    for (int u = 0; u < k; u++) {
        w->rsucc[u] = w->rpred[u] = -1;
    }
    for (int u = 0; u < k; u++)
        for (int v = 0; v < k; v++)
            if (u != v && w->c[u][v] == 1) {
                w->rsucc[u] = (short)v;
                w->rpred[v] = (short)u;
            }
    for (int u = 0; u <= k; u++) {
        if (u == k + 1)
            continue;
        int cntd[32] = {0};
        const u8 *cu = w->c[u == k ? START : u];
        int o = 0;
        for (int v = 0; v < k; v++)
            cntd[cu[v] > 30 ? 30 : cu[v]]++;
        int st[32];
        for (int d = 0; d < 31; d++) {
            st[d] = o;
            o += cntd[d];
        }
        for (int v = 0; v < k; v++) {
            if (u < k && v == u) {
                w->outord[u][st[0]++] = (u8)v;
                continue;
            }
            w->outord[u][st[cu[v] > 30 ? 30 : cu[v]]++] = (u8)v;
        }
    }
    for (int u = 0; u < k + 2; u++)
        if (!w->zob[u])
            w->zob[u] = rng() | 1;
    w->best = len - (n - 1);
    w->nodes = 0;
    w->limit_hit = 0;
    w->gen++;
    if (w->gen == 0) {
        memset(w->memo, 0, sizeof(Memo) << w->mbits);
        w->gen = 1;
    }
    Bits cov;
    memset(&cov, 0, sizeof cov);
    if (k == 0) {
        if (w->c[START][END] < w->best) {
            w->best = w->c[START][END];
            w->bn = 0;
        }
    } else
        win_dfs(w, START, cov, 0, 0, 0);
    if (w->limit_hit)
        *status = 2;
    if (w->best >= len - (n - 1))
        return len;
    /* build the string */
    int o = 0;
    for (int j = 0; j < n - 1; j++)
        out[o++] = W[a + j];
    int cur = START;
    for (int t = 0; t < w->bn; t++) {
        int v = w->bpath[t], cc = w->c[cur][v];
        for (int j = n - cc; j < n; j++)
            out[o++] = (u8)((w->pv[v] >> (4 * (n - 1 - j))) & 15);
        cur = v;
    }
    {
        int cc = w->c[cur][END];
        for (int j = n - 1 - cc; j < n - 1; j++)
            out[o++] = W[b - (n - 1) + j];
    }
    if (o != n - 1 + w->best)
        DIE("win_solve: length mismatch %d %d", o, n - 1 + w->best);
    /* independent check: contexts and coverage */
    if (memcmp(out, W + a, n - 1) || memcmp(out + o - (n - 1), W + b - (n - 1), n - 1))
        DIE("win_solve: context broken");
    for (int j = 0; j < k; j++) {
        int f = 0;
        for (int s = 0; s + n <= o && !f; s++)
            if (pk_at(out + s) == w->pv[j])
                f = 1;
        if (!f)
            DIE("win_solve: permutation lost");
    }
    if (*status == 0)
        *status = 1;
    return o;
}
/* A window solver with a memo table of 2^mbits entries and a limit on its search nodes. */
static Win *win_new(int mbits, i64 node_limit) {
    Win *w = calloc(1, sizeof(Win));
    w->mbits = mbits;
    w->memo = calloc((size_t)1 << mbits, sizeof(Memo));
    w->gen = 1;
    w->node_limit = node_limit;
    return w;
}

/* replace W[a..b) by s (ls letters) if coverage is kept; counts are updated.  returns 1 if applied */
static int replace_checked(i64 a, i64 b, const u8 *s, int ls) {
    i64 lo = a - (n - 1) > 0 ? a - (n - 1) : 0,
        hi = b + (n - 1) < L ? b + (n - 1) : L; /* letters whose windows change */
    int ol = (int)(hi - lo), nl = ol - (int)(b - a) + ls;
    u8 *nb = malloc((size_t)nl + 16);
    memcpy(nb, W + lo, (size_t)(a - lo));
    memcpy(nb + (a - lo), s, (size_t)ls);
    memcpy(nb + (a - lo) + ls, W + b, (size_t)(hi - b));
    for (int t = 0; t + n <= nl; t++) {
        u64 v = pk_at(nb + t);
        if (is_perm_pk(v)) {
            u64 r = rank_pk(v);
            if (CNT[r] < 255)
                CNT[r]++;
        }
    }
    int ok = 1;
    for (int t = 0; t + n <= ol; t++) {
        u64 v = pk_at(W + lo + t);
        if (is_perm_pk(v)) {
            u64 r = rank_pk(v);
            CNT[r]--;
            if (CNT[r] == 0)
                ok = 0;
        }
    }
    if (!ok) { /* undo */
        for (int t = 0; t + n <= ol; t++) {
            u64 v = pk_at(W + lo + t);
            if (is_perm_pk(v))
                CNT[rank_pk(v)]++;
        }
        for (int t = 0; t + n <= nl; t++) {
            u64 v = pk_at(nb + t);
            if (is_perm_pk(v))
                CNT[rank_pk(v)]--;
        }
        free(nb);
        return 0;
    }
    memmove(W + a + ls, W + b, (size_t)(L - b));
    memcpy(W + a, s, (size_t)ls);
    L += ls - (b - a);
    free(nb);
    return 1;
}

typedef struct {
    i64 a, b;
    int ls;
    u8 *s;
} Repl;
/* right to left */
static int repl_cmp(const void *x, const void *y) {
    const Repl *p = x, *q = y;
    return p->a > q->a ? -1 : p->a < q->a;
}
/* solve the windows [A[i], B[i]) in parallel, apply the improvements, return the letters saved */
static i64 run_windows(const i64 *A, const i64 *B, i64 NWIN, i64 node_limit, const char *label, int verbose) {
    Repl *R = NULL;
    i64 nr = 0, rcap = 0;
    i64 st[3] = {0}, how[4] = {0}, nodes = 0, kmax = 0, ksum = 0, searched = 0;
    double t0 = wall();
#pragma omp parallel num_threads(THREADS) reduction(+ : nodes, ksum, searched) reduction(max : kmax)
    {
        Win *w = win_new(18, node_limit);
        u8 *out = malloc(8192);
#pragma omp for schedule(dynamic, 64)
        for (i64 i = 0; i < NWIN; i++) {
            int status, k;
            i64 a = A[i], b = B[i];
            if (a < 0)
                a = 0;
            if (b > L)
                b = L;
            if (b - a < n - 1 || b - a > 4000)
                continue;
            int nl = win_solve(w, a, b, out, &status, &k);
            nodes += w->nodes;
            if (w->nodes > 1)
                searched++;
            w->nodes = 0;
            ksum += k;
            if (k > kmax)
                kmax = k;
#pragma omp atomic
            how[w->root_how]++;
#pragma omp atomic
            st[status]++;
            if (nl < b - a) {
#pragma omp critical
                {
                    if (nr == rcap) {
                        rcap = rcap ? 2 * rcap : 256;
                        R = realloc(R, (size_t)rcap * sizeof(Repl));
                    }
                    R[nr].a = a;
                    R[nr].b = b;
                    R[nr].ls = nl;
                    R[nr].s = malloc((size_t)nl);
                    memcpy(R[nr].s, out, (size_t)nl);
                    nr++;
                }
            }
        }
        free(out);
        free(w->memo);
        free(w);
    }
    if (nr)
        qsort(R, (size_t)nr, sizeof(Repl), repl_cmp);
    i64 saved = 0, applied = 0, lastA = 1LL << 60;
    for (i64 i = 0; i < nr; i++) {
        if (R[i].b + (n - 1) <= lastA && replace_checked(R[i].a, R[i].b, R[i].s, R[i].ls)) {
            saved += (R[i].b - R[i].a) - R[i].ls;
            applied++;
            lastA = R[i].a - (n - 1);
            if (verbose) {
                printf("  window [%lld,%lld) %lld -> %d letters\n", R[i].a, R[i].b, R[i].b - R[i].a, R[i].ls);
            }
        }
        free(R[i].s);
    }
    free(R);
    /* the ends of the word have no context to keep: drop letters there while coverage holds */
    {
        u8 dummy = 0;
        while (L > n && replace_checked(L - 1, L, &dummy, 0))
            saved++;
        while (L > n && replace_checked(0, 1, &dummy, 0))
            saved++;
    }
    printf(
        "%s: %lld windows (largest %lld required permutations, mean %.1f): proved optimal %lld, improvable %lld, node limit hit %lld; at the root: no wasted window %lld, closed by the sum of entries %lld, by the arborescence %lld, searched %lld (more than one node: %lld); %lld nodes; applied %lld, saved %lld letters (%.1fs)\n",
        label, NWIN, kmax, NWIN ? (double)ksum / NWIN : 0.0, st[0], st[1], st[2], how[0], how[1], how[2], how[3],
        searched, nodes, applied, saved, wall() - t0);
    fflush(stdout);
    return saved;
}
/* Mode win: lists the windows to look at (around joins, duplicates or weight-3 steps, or a sweep over the
   word), solves each exactly and applies the replacements that are shorter. */
static void mode_win(const char *what, int R, i64 node_limit, const char *outpath, int verbose) {
    build_joins();
    i64 total = 0;
    for (int round = 0; round < 20; round++) {
        i64 NWIN = 0, cap = 0;
        i64 *A = NULL, *B = NULL;
#define ADDW(x, y)                           \
    do {                                     \
        if (NWIN == cap) {                   \
            cap = cap ? 2 * cap : 4096;      \
            A = realloc(A, (size_t)cap * 8); \
            B = realloc(B, (size_t)cap * 8); \
        }                                    \
        A[NWIN] = (x);                       \
        B[NWIN] = (y);                       \
        NWIN++;                              \
    } while (0)
        if (!strcmp(what, "joins")) {
            for (i64 j = 0; j < NJ; j++) {
                i64 i = JN[j], lo = i - 1 - R, hi = i + R;
                if (lo < 0)
                    lo = 0;
                if (hi > M - 1)
                    hi = M - 1;
                ADDW((i64)P[lo], (i64)P[hi] + n);
            }
        } else if (!strcmp(what, "dups")) {
            for (i64 i = 0; i < M; i++)
                if (NU[i]) {
                    i64 lo = i - R, hi = i + R;
                    if (lo < 0)
                        lo = 0;
                    if (hi > M - 1)
                        hi = M - 1;
                    ADDW((i64)P[lo], (i64)P[hi] + n);
                }
        } else if (!strcmp(what, "gap3")) {
            for (i64 i = 1; i < M; i++)
                if (step(i) == 3) {
                    i64 lo = i - 1 - R, hi = i + R;
                    if (lo < 0)
                        lo = 0;
                    if (hi > M - 1)
                        hi = M - 1;
                    ADDW((i64)P[lo], (i64)P[hi] + n);
                }
        } else if (!strcmp(what, "sweep")) {
            for (i64 a = 0; a < L; a += R) {
                i64 lo = a - (n - 1), hi = a + 2 * R + (n - 1);
                if (lo < 0)
                    lo = 0;
                if (hi > L)
                    hi = L;
                ADDW(lo, hi);
            }
        } else
            DIE("win: joins | dups | gap3 | sweep");
        char label[64];
        snprintf(label, sizeof label, "%s R=%d round %d", what, R, round);
        i64 s = run_windows(A, B, NWIN, node_limit, label, verbose);
        free(A);
        free(B);
        total += s;
        if (!s)
            break;
        build();
        build_joins();
        if (missing)
            DIE("coverage lost");
    }
    if (total && outpath) {
        build();
        if (missing)
            DIE("coverage lost");
        save_word(outpath, W, L);
        printf("wrote %s length %lld\n", outpath, L);
    }
}

/* test of the bound: solve random windows with and without it and compare the optimal lengths */
static void mode_selftest(int R, i64 count, int atjoins) {
    if (atjoins)
        build_joins();
    Win *w = win_new(18, 50000000);
    u8 *o1 = malloc(8192), *o2 = malloc(8192);
    i64 diff = 0, imp = 0, done = 0, n1 = 0, n2 = 0, lim = 0;
    for (i64 t = 0; t < count; t++) {
        i64 a = (i64)(rng() % (u64)(L - R - 2 * n)), b = a + n - 1 + 1 + (i64)(rng() % (u64)R) + n - 1;
        int s1, s2, k;
        if (atjoins && NJ) {
            i64 j = JN[rng() % (u64)NJ];
            i64 lo = j - 1 - (i64)(rng() % (u64)R), hi = j + (i64)(rng() % (u64)R);
            if (lo < 0)
                lo = 0;
            if (hi > M - 1)
                hi = M - 1;
            a = P[lo];
            b = (i64)P[hi] + n;
        }
        NOBOUND = 0;
        int l1 = win_solve(w, a, b, o1, &s1, &k);
        n1 += w->nodes;
        NOBOUND = 1;
        int l2 = win_solve(w, a, b, o2, &s2, &k);
        n2 += w->nodes;
        NOBOUND = 0;
        if (s1 == 2 || s2 == 2) {
            lim++;
            continue;
        }
        done++;
        if (l1 != l2) {
            diff++;
            if (diff < 10)
                printf("MISMATCH window [%lld,%lld): with bound %d, without %d (k=%d)\n", a, b, l1, l2, k);
        }
        if (l1 < b - a)
            imp++;
    }
    printf(
        "selftest: %lld windows compared (%lld skipped at the node limit), %lld improvable, %lld mismatches; nodes with bound %lld, without %lld\n",
        done, lim, imp, diff, n1, n2);
}

/* Prints the usage line and stops. */
static void usage(void) {
    fprintf(
        stderr,
        "usage: letter MODE WORD [options] [--threads T]   modes: stats, diff A B, del, win, reloc, ex, x3, lk, chain, selftest, ctx (see the head of letter.c)\n");
    exit(1);
}
/* Loads the word, builds its tables and runs the mode named by the first argument. */
int main(int argc, char **argv) {
    if (argc < 3)
        usage();
    double t0 = wall();
    const char *mode = argv[1];
    for (int i = 3; i < argc; i++)
        if (!strcmp(argv[i], "--threads") && i + 1 < argc)
            THREADS = atoi(argv[++i]);
    W = load_word(argv[2], &L);
    init_n();
    build();
    fprintf(stderr, "loaded %s: n=%d L=%lld windows=%lld missing=%lld (%.1fs)\n", argv[2], n, L, M, missing,
            wall() - t0);
    if (!strcmp(mode, "stats"))
        mode_stats();
    else if (!strcmp(mode, "diff")) {
        if (argc < 4)
            usage();
        mode_diff(argv[3]);
    } else if (!strcmp(mode, "del"))
        mode_del();
    else if (!strcmp(mode, "ex")) {
        init_arr();
        int D = 0, sm = 0, vb = 0;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--delta") && i + 1 < argc)
                D = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--store") && i + 1 < argc)
                sm = atoi(argv[++i]);
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        const char *out = NULL;
        for (int i = 3; i < argc; i++)
            if (!strcmp(argv[i], "--out") && i + 1 < argc)
                out = argv[++i];
        i64 total = 0;
        for (int r = 0; r < (out ? 100 : 1); r++) {
            i64 g = mode_ex(D, sm, vb);
            if (g <= 0 || !out)
                break; /* --out: apply the best double bridge, repeat */
            i64 nl;
            u8 *nw = materialize(&nl);
            free(W);
            W = nw;
            L = nl;
            build();
            if (missing)
                DIE("coverage lost after a double bridge");
            total += g;
            printf("  word now %lld letters, coverage ok\n", L);
            fflush(stdout);
        }
        if (total && out) {
            save_word(out, W, L);
            printf("wrote %s length %lld\n", out, L);
        }
    } else if (!strcmp(mode, "x3")) {
        init_arr();
        int g = 1, d1 = 8, d2 = 7, vb = 0;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--gmin") && i + 1 < argc)
                g = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--d1") && i + 1 < argc)
                d1 = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--d2") && i + 1 < argc)
                d2 = atoi(argv[++i]);
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        mode_x3(g, d1, d2, vb);
    } else if (!strcmp(mode, "reloc")) {
        init_arr();
        int dm = 6, vb = 0;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--dm") && i + 1 < argc)
                dm = atoi(argv[++i]);
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        mode_reloc(dm, vb);
    } else if (!strcmp(mode, "lk")) {
        init_arr();
        const char *out = NULL;
        int wmin = 4, kmax = 5, d0 = 8, din = 3, vb = 0, gmin = 1;
        i64 budget = 1LL << 40;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--wmin") && i + 1 < argc)
                wmin = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--k") && i + 1 < argc)
                kmax = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--d0") && i + 1 < argc)
                d0 = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--din") && i + 1 < argc)
                din = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--budget") && i + 1 < argc)
                budget = atoll(argv[++i]);
            else if (!strcmp(argv[i], "--out") && i + 1 < argc)
                out = argv[++i];
            else if (!strcmp(argv[i], "--gmin") && i + 1 < argc)
                gmin = atoi(argv[++i]);
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        if (kmax > LKMAX)
            kmax = LKMAX;
        mode_lk(wmin, kmax, d0, din, budget, out, vb, gmin);
    } else if (!strcmp(mode, "chain")) {
        init_arr();
        const char *out = NULL, *base = NULL;
        int D = 4, cl = 0, vb = 0, rounds = 5;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--D") && i + 1 < argc)
                D = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--closable") && i + 1 < argc)
                cl = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--rounds") && i + 1 < argc)
                rounds = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--joinw") && i + 1 < argc)
                JOINW = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--base") && i + 1 < argc)
                base = argv[++i];
            else if (!strcmp(argv[i], "--events") && i + 1 < argc)
                EVFILE = argv[++i];
            else if (!strcmp(argv[i], "--dups"))
                DUPAWARE = 1;
            else if (!strcmp(argv[i], "--small") && i + 1 < argc)
                SMALLUNIT = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--out") && i + 1 < argc)
                out = argv[++i];
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        if (base) {
            int jw = JOINW;
            JOINW = 4;
            load_base(base);
            JOINW = jw;
        }
        mode_chain(D, cl, rounds, out, vb);
    } else if (!strcmp(mode, "ctx")) {
        i64 pos = atoll(argv[3]);
        int r = argc > 4 ? atoi(argv[4]) : 40;
        i64 a = pos - r < 0 ? 0 : pos - r, b = pos + r > L ? L : pos + r;
        for (i64 k = a; k < b; k++)
            putchar(AL[W[k]]);
        printf("\n");
        for (i64 k = a; k < b; k++)
            putchar(k == pos ? '^' : ' ');
        printf("\nsteps:");
        i64 x = 0, y = M;
        while (x < y) {
            i64 m = (x + y) >> 1;
            if ((i64)P[m] < a)
                x = m + 1;
            else
                y = m;
        }
        for (i64 i = x; i < M && (i64)P[i] < b; i++)
            printf(" %d%s", step(i), NU[i] ? "*" : "");
        printf("\n(first window listed starts at %u, index %lld)\n", P[x], x);
    } else if (!strcmp(mode, "selftest")) {
        int R = 40, aj = 0;
        i64 c = 2000;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--R") && i + 1 < argc)
                R = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--count") && i + 1 < argc)
                c = atoll(argv[++i]);
            else if (!strcmp(argv[i], "--joins"))
                aj = 1;
            else if (!strcmp(argv[i], "--joinw") && i + 1 < argc)
                JOINW = atoi(argv[++i]);
        }
        mode_selftest(R, c, aj);
    } else if (!strcmp(mode, "win")) {
        init_arr();
        const char *what = "joins", *out = NULL;
        int R = 22, vb = 0;
        i64 lim = 200000;
        for (int i = 3; i < argc; i++) {
            if (!strcmp(argv[i], "--what") && i + 1 < argc)
                what = argv[++i];
            else if (!strcmp(argv[i], "--R") && i + 1 < argc)
                R = atoi(argv[++i]);
            else if (!strcmp(argv[i], "--nodes") && i + 1 < argc)
                lim = atoll(argv[++i]);
            else if (!strcmp(argv[i], "--out") && i + 1 < argc)
                out = argv[++i];
            else if (!strcmp(argv[i], "-v"))
                vb = 1;
        }
        mode_win(what, R, lim, out, vb);
    } else
        usage();
    fprintf(stderr, "done (%.1fs)\n", wall() - t0);
    return 0;
}
