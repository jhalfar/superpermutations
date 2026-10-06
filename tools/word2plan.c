/* word2plan.c - write any word that is made of the closed trails of a base word as a plan on that base word.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   trailsearch.c reads a base word BASE of Pantone's construction, cuts it into pieces and closed trails, and can
   continue from a plan (--plan-in): a list of events relative to BASE.  This tool takes BASE and another valid
   word OTHER that is made of the same trails (cut at other places, in another order, split into segments) and
   writes the plan for which
       trailsearch BASE.txt out.txt --plan-in PLAN --time 0
   writes exactly OTHER.  The parsing of BASE (pieces, trails, their numbering, real duplicates, cuts) is the one of
   trailsearch.c, so the trail numbers and cuts in the plan are the ones the loader expects.
   I use it to take in other people's words, and to write my words as plans on Pantone's words for publication.

   Method: a table indexed by permutation rank (n! entries of 4 bytes) gives the place (trail, offset) of every
   permutation window of the trails; windows that occur twice have their other places in a small sorted list.
   OTHER is cut into maximal runs of consecutive windows that follow one trail cyclically; each run becomes
       P k            the run is literally piece k of BASE,
       O t start g g1 the run is trail t written once from the cut (start, g, g1) (g1 > 0: a duplicate is dropped),
       S t st len     any other part of trail t (len letters from offset st).
   A window that lies inside the join of two events (the join letters happen to form a permutation) is no event.
   The plan is checked here against OTHER letter by letter with the loader's own rules before it is written.

   Tight joins.  Two runs that meet with a gap below 3 overlap in more than h = n - 3 letters, which a join of the
   model cannot do (this happens in words with cuts inside a 1-cycle).  They are first re-cut at a shared duplicate
   window if there is one; otherwise one of them is written as a segment that is 1 or 2 letters short.  Such a plan
   rebuilds the word but is NOT safe to search from (the short segment has lost a window that only its neighbour
   completes).  The remedy needs no change of the loader: --rebase NEWBASE.txt writes a base word in which every
   chain of tightly joined runs is one open piece (trailsearch reads it as an open path and never moves it) and
   every other trail is one closed piece; running word2plan again with NEWBASE as the base gives a plan that is
   safe.

   --rephase OUT.txt keeps the order of the trails of OTHER and gives every trail its best cut (exact, a shortest
   path), with cuts inside a 1-cycle allowed and events that overlap in up to n - 1 letters (the model of
   recut_wide.c).  The result can have tight joins, so it is written as a word; take it in again (with --rebase)
   to search from it.  --rephase-narrow OUT.txt does the same with the cuts and joins of trailsearch.c.

   Memory: the two words + 4 n! bytes: 250 MB for 11 symbols, 3.0 GB for 12 (--rephase: 2 more bytes per window;
   20 seconds at n = 11, 8 minutes and 4.5 GB at n = 12).  13 symbols would need 5-byte entries (31 GB) and are
   refused.

   Build:  gcc -O2 -o word2plan word2plan.c
   Use:    word2plan BASE.txt OTHER.txt PLAN [--noskip] [--events FILE] [--rebase NEWBASE.txt]
                     [--rephase OUT.txt] [--rephase-narrow OUT.txt] [--quiet]
          --noskip       the plan will be loaded with trailsearch --noskip (no cut drops a duplicate)
          --events FILE  also list every event with its position in OTHER and the overlap with the previous event

   Words: "opening" = cut, "gap" = weight of the step that is cut, "event" = one piece as written.

   Where the parts start.  Each part begins with a comment line of dashes: trails and the loader (as in
   trailsearch.c); the table that says where every permutation window lies in the trails; the windows of one trail;
   the runs of the other word; --rephase.  main is at the end. */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#if defined(_WIN32)
#define fseek64 _fseeki64
#define ftell64 _ftelli64
#else
#define fseek64 fseeko
#define ftell64 ftello
#endif

typedef long long i64;
typedef unsigned long long u64;
typedef unsigned int u32;

static const char *AL = "0123456789ABCDEF";
static unsigned char *W, *F;
static i64 L, LF;
static int n, h;
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

static u64 HMASK[17], fact[17];
static unsigned char PC[65536]; /* PC: popcount of 16 bits */
/* h - largest k with suffix_k(e) == prefix_k(s) */
static inline int dist(u64 e, u64 s) {
    for (int k = h; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (h - k))))
            return h - k;
    return h;
}

/* ---------- trails (as in trailsearch.c) */
typedef struct {
    unsigned char *c;
    i64 R;
    int fixed;
    i64 go, m, pf, pn;
} Trail;
/* go: table entries of this trail are go + offset; m: number of windows; pf, pn: its pieces in PLIST */
static Trail *TR;
static i64 NT;
static i64 *PS, *PL, *POFF, *PLIST, *trail_of_piece;
static i64 NP; /* pieces of the base word; POFF: offset in the trail */
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
/* exactly the loader's function (it wraps at R also for an open path) */
static inline u64 hw_cyc(const Trail *t, i64 pos) {
    i64 R = t->R;
    while (pos >= R)
        pos -= R;
    while (pos < 0)
        pos += R;
    if (pos + h <= R)
        return hw_lin(t->c + pos);
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | t->c[(pos + k) % R];
    return v;
}
/* Rank (0 .. n! - 1, lexicographic) of the permutation in the n letters at p.  p must hold n different letters. */
static inline u64 rank_lin(const unsigned char *p) {
    u64 r = 0;
    int used = 0;
    for (int k = 0; k < n; k++) {
        int c = p[k];
        r += (u64)(c - PC[used & ((1 << c) - 1)]) * fact[n - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* Rank of the permutation window that starts at cyclic position pos of trail t (pos may be negative or beyond R). */
static inline u64 rank_cyc(const Trail *t, i64 pos) {
    u64 r = 0;
    int used = 0;
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    for (int k = 0; k < n; k++) {
        int c = t->c[(pos + k) % R];
        r += (u64)(c - PC[used & ((1 << c) - 1)]) * fact[n - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* Reads a word file into memory as numbers 0 .. 15 (alphabet 0-9, A-F); a trailing line end is dropped.
   Stops with a message on any other symbol.  16 spare bytes follow the word. */
static unsigned char *load_word(const char *path, i64 *len) {
    FILE *f = fopen(path, "rb");
    if (!f)
        DIE("cannot open %s", path);
    fseek64(f, 0, SEEK_END);
    i64 sz = ftell64(f);
    fseek64(f, 0, SEEK_SET);
    unsigned char *w = malloc(sz + 16);
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
        map[(unsigned char)AL[c]] = c;
    for (i64 i = 0; i < got; i++) {
        int v = map[w[i]];
        if (v < 0)
            DIE("bad symbol in %s", path);
        w[i] = (unsigned char)v;
    }
    *len = got;
    return w;
}
static double wall(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static int closes(i64 k, int ex) {
    i64 s = PS[k], l = PL[k], R = l - h - ex;
    return R > 2 * n && !memcmp(W + s + R, W + s, (size_t)(h + ex));
}

/* ---------- places of the windows: TAB[rank] = go + offset of the first place, top bit: more places in SD */
#define EMPTY 0xFFFFFFFFu
#define MORE 0x80000000u
/* wc (first entry of a rank only): occurrences in the base word */
typedef struct {
    u64 r;
    u32 gp, wc;
} Side;
static u32 *TAB;
static Side *SD;
static i64 NSD, SDCAP;
static int side_cmp(const void *a, const void *b) {
    const Side *x = a, *y = b;
    return x->r < y->r ? -1 : x->r > y->r ? 1 : x->gp < y->gp ? -1 : x->gp > y->gp;
}
/* First entry of SD (sorted by permutation) that is not below r. */
static i64 side_find(u64 r) {
    i64 lo = 0, hi = NSD;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (SD[m].r < r)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* Notes that the permutation of rank r lies at global position gp of the trails; a second place of the same
   permutation goes to the side list. */
static inline void tab_add(u64 r, i64 gp) {
    if (TAB[r] == EMPTY) {
        TAB[r] = (u32)gp;
        return;
    }
    TAB[r] |= MORE;
    if (NSD == SDCAP) {
        SDCAP = SDCAP ? SDCAP * 2 : 1 << 16;
        SD = realloc(SD, (size_t)SDCAP * sizeof(Side));
        if (!SD)
            DIE("out of memory");
    }
    SD[NSD].r = r;
    SD[NSD].gp = (u32)gp;
    SD[NSD].wc = 0;
    NSD++;
}
/* The trail that holds global position gp (binary search in the starts of the trails). */
static inline u32 trail_of_gp(i64 gp) {
    i64 lo = 0, hi = NT - 1;
    while (lo < hi) {
        i64 m = (lo + hi + 1) >> 1;
        if (TR[m].go <= gp)
            lo = m;
        else
            hi = m - 1;
    }
    return (u32)lo;
}
static int use_skip = 1, quiet = 0;
/* the loader's dupb: twice in the trails and twice in the base word */
static int realdup(u64 r) {
    if (TAB[r] == EMPTY || !(TAB[r] & MORE))
        return 0;
    return SD[side_find(r)].wc >= 2;
}

/* ---------- windows of one trail, computed locally */
static int is_win(const Trail *T, i64 pos) {
    int used = 0;
    i64 R = T->R;
    if (T->fixed) {
        if (pos < 0 || pos + n > R + h)
            return 0;
        for (int k = 0; k < n; k++)
            used |= 1 << T->c[pos + k];
    } else {
        pos %= R;
        if (pos < 0)
            pos += R;
        for (int k = 0; k < n; k++) {
            used |= 1 << T->c[pos];
            if (++pos == R)
                pos = 0;
        }
    }
    return used == (1 << n) - 1;
}
static i64 prev_gap(const Trail *T, i64 pos) {
    for (i64 g = 1; g <= T->R; g++)
        if (is_win(T, pos - g))
            return g;
    return 0;
}
/* is (start, g) an cut of trail t in the loader's option table?  sets g1 */
static int opening(u32 t, i64 st, i64 g, int *g1) {
    const Trail *T = &TR[t];
    *g1 = 0;
    if (T->fixed || T->m < 2 || g < 2 || !is_win(T, st))
        return 0;
    i64 ga = prev_gap(T, st);
    if (g == ga)
        return 1;
    if (!use_skip || T->m < 3)
        return 0;
    i64 gb = prev_gap(T, st - ga);
    if (g != ga + gb || !realdup(rank_cyc(T, st - ga)))
        return 0;
    *g1 = (int)gb;
    return 1;
}

/* ---------- runs of the other word */
typedef struct {
    u32 t;
    i64 p0, adv, x0, nw;
    int lt, rt;
} Run;
/* trail t from offset p0 (a window); the last window lies adv letters later; x0: position in the other word;
   nw windows; lt / rt: letters cut off at the start / end (tight junctions only) */
static Run *RN;
static i64 NR, RCAP;
enum { EV_PIECE, EV_OPT, EV_SEG };
typedef struct {
    int kind;
    u32 t;
    i64 a, l;
    int g, g1;
    u64 s, e;
    i64 x;
} Ev;
/* EV_PIECE: a = piece.  EV_OPT: a = start, g, g1.  EV_SEG: a = start offset, l letters.  x: position in the other word */

/* letters of the other word from x that follow the trail from pos */
static i64 match_len(const Trail *T, i64 pos, i64 x) {
    i64 k = 0, R = T->R, lim = T->fixed ? R + h - pos : R + n;
    if (lim > LF - x)
        lim = LF - x;
    if (!T->fixed)
        pos %= R;
    while (k < lim) {
        if (F[x + k] != T->c[pos])
            break;
        k++;
        if (++pos == R && !T->fixed)
            pos = 0;
    }
    return k;
}
/* The piece of the base word that is the len letters of trail t from offset st, or -1. */
static i64 piece_of(u32 t, i64 st, i64 len) {
    const Trail *T = &TR[t];
    for (i64 q = T->pf; q < T->pf + T->pn; q++) {
        i64 k = PLIST[q];
        if (POFF[k] == st && PL[k] == len)
            return k;
    }
    return -1;
}

/* ---------- --rephase: the best cuts for the order of the other word, in a wider model than trailsearch's:
   a trail may be cut between any two consecutive windows (gap 1, 2 or 3, or across one real duplicate) and two
   events overlap in as many letters as their last / first windows allow (up to n - 1, not only h = n - 3).
   Exact: a shortest path through the cuts of consecutive events.  value(c) = -gap(c) + min over the cuts c' of the
   previous event of value(c') + d(E_c', S_c), found through a table of the suffixes of all E_c'.
   Runs that are not a whole trail stay as they are.  Two trails must not skip the same duplicate: if that happens
   the two lose their skip cuts and the pass is repeated. */
typedef struct {
    u64 key;
    int val;
    u32 gen;
} DSlot;
static DSlot *DT;
static u64 DCAP;
static u32 DGEN;
static int HH;
static inline u64 hmix(u64 k) {
    k ^= k >> 33;
    k *= 0xFF51AFD7ED558CCDULL;
    k ^= k >> 33;
    k *= 0xC4CEB9FE1A85EC53ULL;
    k ^= k >> 33;
    return k;
}
/* Table of one layer step of --rephase: for every end of E of 1 to HH letters the smallest cost v. */
static inline void d_out(u64 E, int v) {
    for (int k = HH; k >= 1; k--) {
        u64 key = ((E & HMASK[k]) << 4) | (u64)k, q = hmix(key) & (DCAP - 1);
        while (DT[q].gen == DGEN && DT[q].key != key)
            q = (q + 1) & (DCAP - 1);
        if (DT[q].gen != DGEN) {
            DT[q].gen = DGEN;
            DT[q].key = key;
            DT[q].val = v;
        } else if (v < DT[q].val)
            DT[q].val = v;
    }
}
/* The cheapest way into the start word S: the minimum, over the end words E stored with d_out, of their value
   plus the cost of the join E -> S.  For every k the first k letters of S are looked up among the stored endings. */
/* the stored values are relative to their minimum, so HH is always possible */
static inline int d_in(u64 S) {
    int v = HH;
    for (int k = HH; k >= 1; k--) {
        u64 key = ((S >> (4 * (HH - k))) << 4) | (u64)k, q = hmix(key) & (DCAP - 1);
        while (DT[q].gen == DGEN && DT[q].key != key)
            q = (q + 1) & (DCAP - 1);
        if (DT[q].gen == DGEN && DT[q].val + HH - k < v)
            v = DT[q].val + HH - k;
    }
    return v;
}
static inline int dist2(u64 e, u64 s) {
    for (int k = HH; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (HH - k))))
            return HH - k;
    return HH;
}
/* HH letters from offset pos */
static inline u64 wlet(const Trail *T, i64 pos) {
    u64 v = 0;
    i64 R = T->R;
    if (!T->fixed) {
        pos %= R;
        if (pos < 0)
            pos += R;
    }
    for (int k = 0; k < HH; k++) {
        v = (v << 4) | T->c[pos];
        if (++pos == R && !T->fixed)
            pos = 0;
    }
    return v;
}
/* window offsets of a closed trail */
static i64 wins(const Trail *T, i64 *wp) {
    i64 R = T->R, m = 0;
    int cnt[16] = {0}, distinct = 0;
    for (int k = 0; k < n - 1; k++)
        if (cnt[T->c[k % R]]++ == 0)
            distinct++;
    for (i64 p = 0; p < R; p++) {
        i64 q = p + n - 1;
        if (q >= R)
            q -= R;
        if (cnt[T->c[q]]++ == 0)
            distinct++;
        if (distinct == n)
            wp[m++] = p;
        if (--cnt[T->c[p]] == 0)
            distinct--;
    }
    return m;
}
static int i64_cmp(const void *a, const void *b) {
    i64 x = *(const i64 *)a, y = *(const i64 *)b;
    return x < y ? -1 : x > y;
}
/* --rephase / --rephase-narrow: keeps the order of the trails of the other word and gives every trail its
   best cut by a shortest path through layers (wide: cuts inside a 1-cycle and overlaps up to n - 1).  Writes
   the result as a word. */
static void rephase(const char *path, int wide) {
    double t0 = wall();
    i64 N = NR, maxm = 1, tw = 0;
    HH = wide ? n - 1 : h;
    int *cntT = calloc((size_t)NT + 1, sizeof(int)), *bmin = malloc((size_t)N * sizeof(int));
    char *ban = calloc((size_t)NT + 1, 1), *mov = calloc((size_t)N, 1);
    i64 *coff = malloc(((size_t)NT + 1) * 8), *cst = malloc((size_t)N * 8), *clen = malloc((size_t)N * 8),
        *csk = malloc((size_t)N * 8), *sk = malloc((size_t)N * 16);
    for (i64 t = 0; t < NT; t++) {
        coff[t] = 2 * tw;
        tw += TR[t].m;
        if (TR[t].m > maxm)
            maxm = TR[t].m;
    }
    unsigned char *rel = malloc((size_t)(2 * tw + 2)), *dupf = malloc((size_t)maxm + 2);
    i64 *wp = malloc(((size_t)maxm + 2) * 8);
    DCAP = 1 << 16;
    DT = calloc(DCAP, sizeof(DSlot));
    if (!DT || !rel || !wp || !dupf)
        DIE("out of memory");
    DGEN = 0;
    for (i64 i = 0; i < N; i++)
        cntT[RN[i].t]++;
    i64 nmov = 0;
    for (i64 i = 0; i < N;
         i++) { /* movable: the only run of a closed trail, written from a cut (possibly across one real duplicate) */
        const Run *q = &RN[i];
        const Trail *T = &TR[q->t];
        if (cntT[q->t] != 1 || T->fixed || T->m < 3)
            continue;
        i64 g = T->R - q->adv, ga = prev_gap(T, q->p0);
        if (g == ga)
            mov[i] = 1;
        else if (use_skip && g == ga + prev_gap(T, q->p0 - ga) && realdup(rank_cyc(T, q->p0 - ga)))
            mov[i] = 2;
        nmov += mov[i] != 0;
    }
#define OWN_S(q, T) wlet(T, (q)->p0)
#define OWN_E(q, T) wlet(T, (q)->p0 + (q)->adv + n - HH)
#define CUT_OK(g) (wide || (g) >= 2) /* trailsearch's own model has no gap-1 cuts */
    for (int round = 0;; round++) {
        for (i64 i = 0; i < N; i++) {
            const Run *q = &RN[i];
            const Trail *T = &TR[q->t];
            i64 R = T->R;
            if (!mov[i]) {
                bmin[i] = i ? d_in(OWN_S(q, T)) : 0;
                DGEN++;
                d_out(OWN_E(q, T), 0);
                continue;
            }
            i64 m = wins(T, wp), nc = 0;
            unsigned char *rl = rel + coff[q->t];
            int mn = 1 << 20;
            for (i64 j = 0; j < m; j++)
                dupf[j] = (unsigned char)(use_skip && !ban[q->t] && realdup(rank_cyc(T, wp[j])));
            for (i64 j = 0; j < m; j++) {
                i64 j1 = j ? j - 1 : m - 1, j2 = j1 ? j1 - 1 : m - 1;
                int g = (int)((wp[j] - wp[j1] + R) % R), g2 = g + (int)((wp[j1] - wp[j2] + R) % R);
                int own = wp[j] == q->p0, sv = i ? d_in(wlet(T, wp[j])) : 0, v;
                if (CUT_OK(g) || (own && mov[i] == 1)) {
                    v = sv - g + 8;
                    rl[2 * j] = (unsigned char)v;
                    if (v - 8 < mn)
                        mn = v - 8;
                    nc++;
                } else
                    rl[2 * j] = 255;
                if (dupf[j1] && CUT_OK(g2)) {
                    v = sv - g2 + 8;
                    rl[2 * j + 1] = (unsigned char)v;
                    if (v - 8 < mn)
                        mn = v - 8;
                    nc++;
                } else
                    rl[2 * j + 1] = 255;
            }
            bmin[i] = mn;
            if ((u64)(nc + 1) * HH * 2 > DCAP) {
                free(DT);
                while ((u64)(nc + 1) * HH * 2 > DCAP)
                    DCAP <<= 1;
                DT = calloc(DCAP, sizeof(DSlot));
                if (!DT)
                    DIE("out of memory");
                DGEN = 0;
            }
            DGEN++;
            for (i64 j = 0; j < m; j++) {
                i64 j1 = j ? j - 1 : m - 1, j2 = j1 ? j1 - 1 : m - 1;
                if (rl[2 * j] != 255) {
                    rl[2 * j] = (unsigned char)(rl[2 * j] - 8 - mn);
                    d_out(wlet(T, wp[j1] + n - HH), rl[2 * j]);
                }
                if (rl[2 * j + 1] != 255) {
                    rl[2 * j + 1] = (unsigned char)(rl[2 * j + 1] - 8 - mn);
                    d_out(wlet(T, wp[j2] + n - HH), rl[2 * j + 1]);
                }
            }
        }
        u64 S = 0;
        int need = 0;
        i64 ns = 0, conflicts = 0;
        for (i64 i = N - 1; i >= 0; i--) {
            const Run *q = &RN[i];
            const Trail *T = &TR[q->t];
            i64 R = T->R;
            if (!mov[i]) {
                cst[i] = q->p0;
                clen[i] = q->adv + n;
                csk[i] = -1;
                need = bmin[i];
                S = OWN_S(q, T);
                continue;
            }
            i64 m = wins(T, wp), best = -1;
            unsigned char *rl = rel + coff[q->t];
            /* the cut the word has now wins ties */
            {
                i64 lo = 0, hi = m - 1;
                while (lo < hi) {
                    i64 md = (lo + hi) >> 1;
                    if (wp[md] < q->p0)
                        lo = md + 1;
                    else
                        hi = md;
                }
                i64 c = 2 * lo + (mov[i] == 2), j1 = lo ? lo - 1 : m - 1, j2 = j1 ? j1 - 1 : m - 1;
                if (wp[lo] == q->p0 && rl[c] != 255 &&
                    (i == N - 1 ? rl[c] == 0 : rl[c] + dist2(wlet(T, wp[c & 1 ? j2 : j1] + n - HH), S) == need))
                    best = c;
            }
            for (i64 c = 0; c < 2 * m && best < 0; c++) {
                if (rl[c] == 255)
                    continue;
                i64 j = c >> 1, j1 = j ? j - 1 : m - 1, j2 = j1 ? j1 - 1 : m - 1;
                if (i == N - 1 ? rl[c] == 0 : rl[c] + dist2(wlet(T, wp[c & 1 ? j2 : j1] + n - HH), S) == need)
                    best = c;
            }
            if (best < 0)
                DIE("internal error: rephase back-tracking at event %lld", i);
            i64 j = best >> 1, j1 = j ? j - 1 : m - 1, j2 = j1 ? j1 - 1 : m - 1, pe = wp[best & 1 ? j2 : j1];
            int g = (int)((wp[j] - pe + R) % R);
            cst[i] = wp[j];
            clen[i] = R + n - g;
            csk[i] = best & 1 ? (i64)rank_cyc(T, wp[j1]) : -1;
            need = rl[best] + bmin[i] + g;
            S = wlet(T, wp[j]);
        }
        for (i64 i = 0; i < N; i++)
            if (csk[i] >= 0) {
                sk[2 * ns] = csk[i];
                sk[2 * ns + 1] = i;
                ns++;
            }
        qsort(sk, (size_t)ns, 16, i64_cmp);
        for (i64 z = 0; z + 1 < ns; z++)
            if (sk[2 * z] == sk[2 * z + 2]) {
                conflicts++;
                ban[RN[sk[2 * z + 1]].t] = ban[RN[sk[2 * z + 3]].t] = 1;
            }
        if (!conflicts)
            break;
        printf("rephase: %lld duplicates skipped twice, pass %d is repeated without the skip cuts of those trails\n",
               conflicts, round + 1);
        fflush(stdout);
        if (round == 30)
            DIE("rephase: giving up");
    }
    /* write: consecutive events overlap in the largest suffix / prefix of up to n - 1 letters (the word itself decides) */
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0;
    char *out = malloc(cap);
    i64 total = 0, nre = 0, ng1 = 0, ntj = 0, nskp = 0;
    u64 tail = 0;
    HH = n - 1;
    for (i64 i = 0; i < N; i++) {
        const Trail *T = &TR[RN[i].t];
        i64 R = T->R;
        int ov = i ? HH - dist2(tail, wlet(T, cst[i])) : 0;
        if (cst[i] != RN[i].p0 || clen[i] != RN[i].adv + n)
            nre++;
        if (mov[i] && clen[i] == R + n - 1)
            ng1++;
        if (csk[i] >= 0)
            nskp++;
        if (ov > h)
            ntj++;
        for (i64 r = ov; r < clen[i]; r++) {
            out[ob++] = AL[T->c[T->fixed ? cst[i] + r : (cst[i] + r) % R]];
            if (ob == cap) {
                fwrite(out, 1, ob, f);
                ob = 0;
            }
        }
        total += clen[i] - ov;
        tail = wlet(T, cst[i] + clen[i] - HH);
    }
    out[ob++] = '\n';
    fwrite(out, 1, ob, f);
    fclose(f);
    free(out);
    printf("rephase (%s model): %lld of %lld events may be re-opened; best cuts for this order: %lld -> %lld letters\n",
           wide ? "wide" : "trailsearch", nmov, N, LF, total);
    printf(
        "rephase: %lld events re-opened; the result has %lld gap-1 cuts, %lld duplicate skips, %lld joins that overlap in more than h letters (%.1fs)\n",
        nre, ng1, nskp, ntj, wall() - t0);
    printf("rephase: wrote %s; check it with delcheck, then import it: word2plan BASE %s PLAN [--rebase NEWBASE]\n",
           path, path);
    free(cntT);
    free(bmin);
    free(ban);
    free(mov);
    free(coff);
    free(cst);
    free(clen);
    free(csk);
    free(sk);
    free(rel);
    free(dupf);
    free(wp);
    free(DT);
}

/* Loads the base word as trailsearch.c does, builds the table permutation -> place in the trails, cuts the
   other word into runs that follow one trail, turns the runs into events, checks the plan letter by letter
   and writes it; then --events, --rebase and --rephase. */
int main(int argc, char **argv) {
    if (argc < 4)
        DIE("usage: word2plan BASE.txt OTHER.txt PLAN [--noskip] [--events FILE] [--rebase NEWBASE.txt] [--rephase OUT.txt] [--rephase-narrow OUT.txt] [--quiet]");
    const char *evpath = NULL, *rebase = NULL, *reph = NULL, *reph_narrow = NULL;
    for (int a = 4; a < argc; a++) {
        if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--quiet"))
            quiet = 1;
        else if (!strcmp(argv[a], "--events") && a + 1 < argc)
            evpath = argv[++a];
        else if (!strcmp(argv[a], "--rebase") && a + 1 < argc)
            rebase = argv[++a];
        else if (!strcmp(argv[a], "--rephase") && a + 1 < argc)
            reph = argv[++a];
        else if (!strcmp(argv[a], "--rephase-narrow") && a + 1 < argc)
            reph_narrow = argv[++a];
        else
            DIE("unknown option %s", argv[a]);
    }
    double t00 = wall();
    W = load_word(argv[1], &L);
    F = load_word(argv[2], &LF);
    int mx = 0;
    for (i64 i = 0; i < L; i++)
        if (W[i] > mx)
            mx = W[i];
    n = mx + 1;
    h = n - 3;
    if (n < 6 || n > 13)
        DIE("6 to 13 symbols");
    for (i64 i = 0; i < LF; i++)
        if (F[i] > mx)
            DIE("%s uses more symbols than %s", argv[2], argv[1]);
    for (int k = 0; k <= 16; k++)
        HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    for (int i = 1; i < 65536; i++)
        PC[i] = (unsigned char)(PC[i >> 1] + (i & 1));

    /* ---------- base word: pieces and trails, exactly as trailsearch.c does it */
    {
        int cnt[16] = {0}, distinct = 0;
        i64 nw = 0, cap = 1 << 16, prev = -1, pstart = -1;
        PS = malloc(cap * 8);
        PL = malloc(cap * 8);
        NP = 0;
        for (i64 i = 0; i < L; i++) {
            if (cnt[W[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[W[i - n]] == 0)
                    distinct--;
            }
            if (i < n - 1 || distinct != n)
                continue;
            i64 p = i - n + 1;
            nw++;
            if (prev < 0)
                pstart = p;
            else if (p - prev >= 4) {
                if (NP == cap) {
                    cap *= 2;
                    PS = realloc(PS, cap * 8);
                    PL = realloc(PL, cap * 8);
                }
                PS[NP] = pstart;
                PL[NP] = prev + n - pstart;
                NP++;
                pstart = p;
            }
            prev = p;
        }
        if (prev < 0)
            DIE("no permutation in the word");
        if (NP == cap) {
            cap *= 2;
            PS = realloc(PS, cap * 8);
            PL = realloc(PL, cap * 8);
        }
        PS[NP] = pstart;
        PL[NP] = prev + n - pstart;
        NP++;
        printf("base: n=%d L=%lld perm windows %lld pieces %lld\n", n, L, nw, NP);
    }
    char *closed = calloc((size_t)NP, 1);
    trail_of_piece = malloc(NP * 8);
    POFF = calloc((size_t)NP, 8);
    PLIST = malloc(NP * 8);
    i64 npl = 0;
    for (i64 k = 0; k < NP; k++)
        trail_of_piece[k] = -1;
    TR = calloc((size_t)NP + 1, sizeof(Trail));
    NT = 0;
    i64 nclosed = 0, nopen = 0, nlinear = 0;
    for (i64 k = 0; k < NP; k++)
        if (closes(k, 0)) {
            closed[k] = 1;
            nclosed++;
            trail_of_piece[k] = NT;
            TR[NT].c = W + PS[k];
            TR[NT].R = PL[k] - h;
            TR[NT].pf = npl;
            TR[NT].pn = 1;
            PLIST[npl++] = k;
            NT++;
        }
    {
        i64 no = 0;
        i64 *op = malloc((NP + 1) * 8);
        for (i64 k = 0; k < NP; k++)
            if (!closed[k])
                op[no++] = k;
        char *used = calloc((size_t)NP + 1, 1), *haspred = calloc((size_t)NP + 1, 1);
        i64 *chain = malloc((no + 1) * 8);
        for (i64 a = 0; a < no; a++) {
            u64 tw = hw_lin(W + PS[op[a]] + PL[op[a]] - h);
            for (i64 b = 0; b < no; b++)
                if (b != a && hw_lin(W + PS[op[b]]) == tw)
                    haspred[op[b]] = 1;
        }
        for (int phase = 0; phase < 2; phase++)
            for (i64 a = 0; a < no; a++) {
                i64 k = op[a];
                if (used[k] || (phase == 0 && haspred[k]))
                    continue;
                i64 nc = 0;
                chain[nc++] = k;
                used[k] = 1;
                u64 hwd = hw_lin(W + PS[k]), tw;
                for (;;) {
                    i64 lastp = chain[nc - 1];
                    tw = hw_lin(W + PS[lastp] + PL[lastp] - h);
                    if (tw == hwd)
                        break;
                    i64 nx = -1;
                    for (i64 b = 0; b < no; b++)
                        if (!used[op[b]] && hw_lin(W + PS[op[b]]) == tw) {
                            nx = op[b];
                            break;
                        }
                    if (nx < 0)
                        break;
                    chain[nc++] = nx;
                    used[nx] = 1;
                }
                int ex = (tw != hwd && nc == 1) ? (closes(k, 1) ? 1 : closes(k, 2) ? 2 : 0) : 0;
                if (ex) {
                    closed[k] = 1;
                    nclosed++;
                    trail_of_piece[k] = NT;
                    TR[NT].c = W + PS[k];
                    TR[NT].R = PL[k] - h - ex;
                    TR[NT].pf = npl;
                    TR[NT].pn = 1;
                    PLIST[npl++] = k;
                    NT++;
                    continue;
                }
                i64 R = 0;
                for (i64 b = 0; b < nc; b++)
                    R += PL[chain[b]] - h;
                unsigned char *c = malloc((size_t)R + h + 16);
                i64 q = 0;
                TR[NT].pf = npl;
                TR[NT].pn = nc;
                for (i64 b = 0; b < nc; b++) {
                    memcpy(c + q, W + PS[chain[b]], (size_t)(PL[chain[b]] - h));
                    POFF[chain[b]] = q;
                    PLIST[npl++] = chain[b];
                    q += PL[chain[b]] - h;
                    trail_of_piece[chain[b]] = NT;
                }
                TR[NT].c = c;
                TR[NT].R = R;
                if (tw != hwd) {
                    i64 lastp = chain[nc - 1];
                    memcpy(c + q, W + PS[lastp] + PL[lastp] - h, (size_t)h);
                    TR[NT].fixed = 1;
                    nlinear += nc;
                } else
                    nopen += nc;
                NT++;
            }
        free(op);
        free(used);
        free(haspred);
        free(chain);
    }
    i64 sumR = 0, tot = 0;
    for (i64 t = 0; t < NT; t++) {
        sumR += TR[t].R;
        TR[t].go = tot;
        tot += TR[t].R + (TR[t].fixed ? h : 0);
    }
    printf("base: trails %lld (closed pieces %lld, chained open pieces %lld), sum R %lld\n", NT, nclosed, nopen, sumR);
    if (nlinear)
        printf("base: %lld pieces form an open path that is not a closed trail (trailsearch never moves them)\n",
               nlinear);
    if (tot >= (i64)MORE - 1)
        DIE("the trails have %lld letters: more than 4-byte table entries can address (13 symbols need another index)",
            tot);

    /* ---------- table of window places */
    u64 NF = fact[n];
    TAB = malloc((size_t)NF * 4);
    if (!TAB)
        DIE("out of memory for the table (%llu MB)", (unsigned long long)(NF * 4 >> 20));
    memset(TAB, 0xFF, (size_t)NF * 4);
    i64 nwin = 0, nplain = 0;
    for (i64 t = 0; t < NT; t++) {
        Trail *T = &TR[t];
        i64 R = T->R, m = 0, first = -1, prev = -1;
        int cnt[16] = {0}, distinct = 0;
        if (T->fixed) {
            for (i64 i = 0; i < R + h; i++) {
                if (cnt[T->c[i]]++ == 0)
                    distinct++;
                if (i >= n) {
                    if (--cnt[T->c[i - n]] == 0)
                        distinct--;
                }
                if (i >= n - 1 && distinct == n) {
                    tab_add(rank_lin(T->c + i - n + 1), T->go + i - n + 1);
                    m++;
                }
            }
        } else {
            for (int k = 0; k < n - 1; k++)
                if (cnt[T->c[k % R]]++ == 0)
                    distinct++;
            for (i64 p = 0; p < R; p++) {
                i64 q = p + n - 1;
                if (q >= R)
                    q -= R;
                if (cnt[T->c[q]]++ == 0)
                    distinct++;
                if (distinct == n) {
                    tab_add(p + n <= R ? rank_lin(T->c + p) : rank_cyc(T, p), T->go + p);
                    m++;
                    if (prev >= 0) {
                        if (p - prev > 3)
                            DIE("gap %lld inside trail %lld (trailsearch refuses this word)", p - prev, t);
                        if (p - prev >= 2)
                            nplain++;
                    } else
                        first = p;
                    prev = p;
                }
                if (--cnt[T->c[p]] == 0)
                    distinct--;
            }
            if (m >= 2) {
                i64 g = first + R - prev;
                if (g > 3)
                    DIE("gap %lld inside trail %lld (trailsearch refuses this word)", g, t);
                if (g >= 2)
                    nplain++;
            }
        }
        T->m = m;
        nwin += m;
    }
    u64 scount = 0;
    for (u64 r = 0; r < NF; r++)
        if (TAB[r] != EMPTY)
            scount++;
    qsort(SD, (size_t)NSD, sizeof(Side), side_cmp);
    i64 ndup = 0;
    for (i64 i = 0; i < NSD; i++)
        if (!i || SD[i].r != SD[i - 1].r)
            ndup++;
    printf("base: trail windows %lld distinct %llu (n! check: %s), duplicated %lld (%.1fs)\n", nwin, scount,
           scount == NF ? "True" : "False", ndup, wall() - t00);
    if (scount != NF)
        DIE("the trails of the base word do not contain every permutation (%llu missing): trailsearch cannot use it as a base",
            (unsigned long long)(NF - scount));
    /* real duplicates: also twice in the base word itself */
    {
        int cnt[16] = {0}, distinct = 0;
        for (i64 i = 0; i < L; i++) {
            if (cnt[W[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[W[i - n]] == 0)
                    distinct--;
            }
            if (i < n - 1 || distinct != n)
                continue;
            u64 r = rank_lin(W + i - n + 1);
            if (TAB[r] & MORE)
                SD[side_find(r)].wc++;
        }
        i64 real = 0, nskipopt = 0;
        for (i64 i = 0; i < NSD; i++)
            if (!i || SD[i].r != SD[i - 1].r) {
                if (SD[i].wc < 2)
                    continue;
                real++;
                i64 gp = TAB[SD[i].r] & ~MORE;
                if (!TR[trail_of_gp(gp)].fixed && TR[trail_of_gp(gp)].m >= 3)
                    nskipopt++;
                for (i64 j = i; j < NSD && SD[j].r == SD[i].r; j++)
                    if (!TR[trail_of_gp(SD[j].gp)].fixed && TR[trail_of_gp(SD[j].gp)].m >= 3)
                        nskipopt++;
            }
        if (real != ndup)
            printf(
                "base: %lld duplicated windows exist only in the cyclic words, not in the word: they will not be skipped\n",
                ndup - real);
        if (!use_skip)
            nskipopt = 0;
        printf("base: options %lld (dup-skip options %lld) (%.1fs)\n", nplain + nskipopt, nskipopt, wall() - t00);
    }

    /* ---------- the other word: maximal runs along one trail */
    u64 *seen = calloc((size_t)(NF >> 6) + 1, 8);
    u64 fdist = 0;
    i64 fwin = 0, cur = -1;
    {
        int cnt[16] = {0}, distinct = 0;
        for (i64 i = 0; i < LF; i++) {
            if (cnt[F[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[F[i - n]] == 0)
                    distinct--;
            }
            if (i < n - 1 || distinct != n)
                continue;
            i64 x = i - n + 1;
            u64 r = rank_lin(F + x);
            fwin++;
            if (!((seen[r >> 6] >> (r & 63)) & 1)) {
                seen[r >> 6] |= 1ULL << (r & 63);
                fdist++;
            }
            u32 v = TAB[r];
            i64 gp0 = v & ~MORE, sf = (v & MORE) ? side_find(r) : NSD;
            if (cur >= 0) {
                Run *q = &RN[cur];
                const Trail *T = &TR[q->t];
                i64 G = x - (q->x0 + q->adv), np = q->p0 + q->adv + G;
                if (G <= 3 && (T->fixed || q->adv + G < T->R)) {
                    if (!T->fixed && np >= T->R)
                        np -= T->R;
                    i64 want = T->go + np;
                    int ok = gp0 == want;
                    for (i64 j = sf; !ok && j < NSD && SD[j].r == r; j++)
                        ok = SD[j].gp == want;
                    if (ok) {
                        q->adv += G;
                        q->nw++;
                        continue;
                    }
                }
            }
            /* a new run: the place whose trail the word follows longest */
            i64 bgp = gp0;
            if (v & MORE) {
                u32 t0 = trail_of_gp(gp0);
                i64 bl = match_len(&TR[t0], gp0 - TR[t0].go, x);
                for (i64 j = sf; j < NSD && SD[j].r == r; j++) {
                    u32 t1 = trail_of_gp(SD[j].gp);
                    i64 l1 = match_len(&TR[t1], SD[j].gp - TR[t1].go, x);
                    if (l1 > bl) {
                        bl = l1;
                        bgp = SD[j].gp;
                    }
                }
            }
            if (NR == RCAP) {
                RCAP = RCAP ? RCAP * 2 : 1 << 16;
                RN = realloc(RN, (size_t)RCAP * sizeof(Run));
                if (!RN)
                    DIE("out of memory");
            }
            Run *q = &RN[NR];
            q->t = trail_of_gp(bgp);
            q->p0 = bgp - TR[q->t].go;
            q->adv = 0;
            q->x0 = x;
            q->nw = 1;
            q->lt = q->rt = 0;
            cur = NR++;
        }
    }
    printf("other: L=%lld perm windows %lld distinct %llu (n! check: %s), runs %lld (%.1fs)\n", LF, fwin, fdist,
           fdist == NF ? "True" : "False", NR, wall() - t00);
    if (fdist != NF)
        printf("WARNING: the other word misses %llu permutations\n", (unsigned long long)(NF - fdist));
    free(seen);
    if (!NR)
        DIE("no permutation in the other word");

    /* ---------- incidental windows: a run that touches a neighbour with a gap below 3 and lies inside the letters
       of its two neighbours, which meet with the overlap the model gives them, is no event: their join writes it */
    i64 ndrop = 0, ndropw = 0;
    {
        i64 m = 0;
        for (i64 i = 0; i < NR; i++) {
            if (m >= 1 && i + 1 < NR) {
                const Run *A = &RN[m - 1], *B = &RN[i], *C = &RN[i + 1];
                i64 al = A->x0 + A->adv;
                i64 gab = B->x0 - al, gbc = C->x0 - (B->x0 + B->adv), gac = C->x0 - al;
                if ((gab < 3 || gbc < 3) && gac >= 3 && gac <= n &&
                    dist(hw_lin(F + al + 3), hw_lin(F + C->x0)) == h - (n - gac)) {
                    ndrop++;
                    ndropw += B->nw;
                    if (!quiet && ndrop <= 20)
                        printf(
                            "  INCIDENTAL: %lld window(s) of trail %u (offset %lld) at position %lld lie in the join of trails %u and %u (cost %lld)\n",
                            B->nw, B->t, B->p0, B->x0, A->t, C->t, (i64)h - (n - gac));
                    continue;
                }
            }
            RN[m++] = RN[i];
        }
        NR = m;
    }

    /* ---------- tight junctions: runs A, B whose last / first windows are G < 3 apart.
       1. if the last windows of A are duplicates that also precede B in B's trail, give them to B (re-cut);
       2. otherwise cut 3 - G letters off the start of B (or the end of A if B is a whole trail and A is not). */
    i64 ntight = 0, nrecut = 0, ntrim = 0, ntrim_whole = 0, nvanish = 0;
    for (i64 i = 0; i + 1 < NR; i++) {
        Run *A = &RN[i], *B = &RN[i + 1];
        i64 G = B->x0 - (A->x0 + A->adv);
        if (G >= 3)
            continue;
        ntight++;
        /* re-cut: try to move k = 1, 2, ... last windows of A to the front of B until the gap is 3 or more */
        {
            const Trail *TA = &TR[A->t], *TB = &TR[B->t];
            i64 a_adv = A->adv, a_nw = A->nw, b_p0 = B->p0, b_adv = B->adv, b_x0 = B->x0, b_nw = B->nw, g = G;
            int done = 0;
            while (a_nw >= 1 && !TB->fixed && b_adv + g < TB->R) {
                /* the last window of A (trail offset p0 + a_adv) must be the window g before B's first in B's trail */
                i64 bp = b_p0 - g;
                if (bp < 0)
                    bp += TB->R;
                if (!is_win(TB, bp) ||
                    rank_cyc(TB, bp) != (TA->fixed ? rank_lin(TA->c + A->p0 + a_adv) : rank_cyc(TA, A->p0 + a_adv)))
                    break;
                b_p0 = bp;
                b_adv += g;
                b_x0 -= g;
                b_nw++;
                a_nw--;
                if (!a_nw) {
                    done = 2;
                    break;
                }
                i64 ga = prev_gap(TA, A->p0 + a_adv);
                a_adv -= ga;
                g = ga;
                if (g >= 3) {
                    done = 1;
                    break;
                }
            }
            if (done) {
                B->p0 = b_p0;
                B->adv = b_adv;
                B->x0 = b_x0;
                B->nw = b_nw;
                A->adv = a_adv;
                A->nw = a_nw;
                nrecut++;
                if (done == 2) {
                    nvanish++;
                    memmove(A, B, (size_t)(NR - i - 1) * sizeof(Run));
                    NR--;
                    i -= i > 0 ? 2 : 1;
                }
                continue;
            }
        }
        ntrim++;
    }
    /* ---------- --rebase: a base word in which every chain of runs linked by tight junctions is one open piece
       (trailsearch reads it as an open path that it never moves) and every other trail is one closed piece */
    if (rebase) {
        char *fz = calloc((size_t)NT + 1, 1);
        i64 nfz = 0, nfp = 0, nlet = 0, npc = 0;
        int last = -1;
        for (i64 i = 0; i + 1 < NR; i++)
            if (RN[i + 1].x0 - (RN[i].x0 + RN[i].adv) < 3)
                fz[RN[i].t] = fz[RN[i + 1].t] = 1;
        FILE *f = fopen(rebase, "wb");
        if (!f)
            DIE("cannot write %s", rebase);
        size_t cap = 1 << 22, ob = 0;
        char *out = malloc(cap);
#define PUT(c)                     \
    do {                           \
        out[ob++] = AL[c];         \
        nlet++;                    \
        if (ob == cap) {           \
            fwrite(out, 1, ob, f); \
            ob = 0;                \
        }                          \
    } while (0)
#define SEP(first)       \
    do {                 \
        if (last >= 0) { \
            PUT(last);   \
            PUT(first);  \
        }                \
        npc++;           \
    } while (0) /* two letters that no window can cross */
        for (i64 t = 0; t < NT; t++) {
            const Trail *T = &TR[t];
            if (fz[t]) {
                nfz++;
                continue;
            }
            i64 len = T->fixed ? T->R + h : T->R + n - prev_gap(T, 0);
            SEP(T->c[0]);
            for (i64 r = 0; r < len; r++)
                PUT(T->c[T->fixed ? r : r % T->R]);
            last = T->c[T->fixed ? len - 1 : (len - 1) % T->R];
        }
        for (i64 i = 0; i < NR; i++)
            if (fz[RN[i].t]) {
                i64 j = i;
                while (j + 1 < NR && RN[j + 1].x0 - (RN[j].x0 + RN[j].adv) < 3)
                    j++;
                i64 a = RN[i].x0, b = RN[j].x0 + RN[j].adv + n;
                SEP(F[a]);
                for (i64 x = a; x < b; x++)
                    PUT(F[x]);
                last = F[b - 1];
                nfp++;
                i = j;
            }
        out[ob++] = '\n';
        fwrite(out, 1, ob, f);
        fclose(f);
        free(out);
        free(fz);
        printf(
            "rebase: wrote %s (%lld letters, %lld pieces): %lld trails frozen into %lld open pieces, %lld trails unchanged\n",
            rebase, nlet, npc, nfz, nfp, NT - nfz);
        printf("rebase: next: word2plan %s %s PLAN  (trailsearch should then report %lld trails)\n", rebase, argv[2],
               NT - nfz + nfp);
    }

    if (reph_narrow)
        rephase(reph_narrow, 0);
    if (reph)
        rephase(reph, 1);

    /* trims (after all re-cuts, so that "whole" is judged on the final runs) */
    for (i64 i = 0; i + 1 < NR; i++) {
        Run *A = &RN[i], *B = &RN[i + 1];
        i64 G = B->x0 - (A->x0 + A->adv);
        int g1;
        if (G >= 3)
            continue;
        const Trail *TA = &TR[A->t], *TB = &TR[B->t];
        int wa = piece_of(A->t, A->p0, A->adv + n) >= 0 || opening(A->t, A->p0, TA->R - A->adv, &g1);
        int wb = piece_of(B->t, B->p0, B->adv + n) >= 0 || opening(B->t, B->p0, TB->R - B->adv, &g1);
        if (wb && !wa)
            A->rt = (int)(3 - G);
        else
            B->lt = (int)(3 - G);
        if (wa && wb)
            ntrim_whole++;
    }

    /* ---------- events */
    Ev *ev = malloc((size_t)NR * sizeof(Ev));
    i64 N = 0, nP = 0, nO = 0, nS = 0, nOskip = 0, nOg2 = 0, nwhole_noopt = 0, nfixbad = 0;
    i64 *cov = calloc((size_t)NT + 1, 8), *nev = calloc((size_t)NT + 1, 8), *decl = calloc((size_t)NT + 1, 8);
    for (i64 i = 0; i < NR; i++) {
        Run *q = &RN[i];
        const Trail *T = &TR[q->t];
        Ev x;
        memset(&x, 0, sizeof x);
        x.t = q->t;
        x.x = q->x0 + q->lt;
        i64 len = q->adv + n, k = -1;
        int g1 = 0;
        cov[q->t] += q->nw;
        nev[q->t]++;
        if (!q->lt && !q->rt && (k = piece_of(q->t, q->p0, len)) >= 0) {
            x.kind = EV_PIECE;
            x.a = k;
            x.l = PL[k];
            x.s = hw_lin(W + PS[k]);
            x.e = hw_lin(W + PS[k] + PL[k] - h);
            nP++;
        } else if (!q->lt && !q->rt && opening(q->t, q->p0, T->R - q->adv, &g1)) {
            int g = (int)(T->R - q->adv);
            x.kind = EV_OPT;
            x.a = q->p0;
            x.g = g;
            x.g1 = g1;
            x.l = T->R + h + 3 - g;
            x.s = hw_cyc(T, q->p0);
            x.e = hw_cyc(T, q->p0 - g + 3);
            nO++;
            if (g1) {
                nOskip++;
                decl[q->t]++;
            } else if (g == 2)
                nOg2++;
        } else {
            x.kind = EV_SEG;
            x.a = q->p0 + q->lt;
            x.l = len - q->lt - q->rt;
            x.s = hw_cyc(T, x.a);
            x.e = hw_cyc(T, x.a + x.l - h);
            nS++;
            if (T->fixed && x.a + x.l > T->R)
                nfixbad++;
            if (!T->fixed && q->nw == T->m)
                nwhole_noopt++;
        }
        ev[N++] = x;
    }

    /* ---------- check: rebuild the word with the loader's rules and compare */
    i64 fp = 0, nwaste = 0, waste = 0, nhole = 0, bad = -1;
    u64 tail = 0;
    i64 hist[17] = {0};
    for (i64 i = 0; i < N && bad < 0; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        if (i) {
            hist[h - skip]++;
            i64 actual = fp - x->x; /* overlap in the other word */
            if (actual < 0) {
                nhole++;
                if (!quiet && nhole <= 20)
                    printf("  UNCOVERED: %lld letters at position %lld (before event %lld) belong to no window\n",
                           -actual, fp, i);
            } else if (skip > actual) {
                nwaste++;
                waste += skip - actual;
                if (!quiet && nwaste <= 20)
                    printf(
                        "  WASTE: events %lld / %lld overlap in %lld letters at position %lld but could overlap in %lld\n",
                        i - 1, i, actual, x->x, skip);
            }
        } else if (x->x != 0) {
            nhole++;
            if (!quiet)
                printf("  UNCOVERED: %lld letters before the first window\n", x->x);
        }
        for (i64 r = skip; r < x->l; r++) {
            unsigned char c;
            if (x->kind == EV_PIECE)
                c = W[PS[x->a] + r];
            else
                c = TR[x->t].c[(x->a + r) % TR[x->t].R];
            if (fp >= LF || F[fp] != c) {
                bad = i;
                break;
            }
            fp++;
        }
        tail = x->e;
    }
    if (bad < 0 && fp != LF) {
        nhole++;
        if (!quiet)
            printf("  UNCOVERED: %lld letters after the last window\n", LF - fp);
    }
    i64 mlen = 0;
    for (i64 i = 0; i < N; i++)
        mlen += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++)
        mlen -= h - dist(ev[i].e, ev[i + 1].s);

    /* ---------- per-trail coverage */
    i64 nmulti = 0, n3 = 0, nmiss = 0, miss = 0, nabsent = 0, nover = 0;
    for (i64 t = 0; t < NT; t++) {
        i64 d = TR[t].m - cov[t];
        if (!nev[t]) {
            nabsent++;
            continue;
        }
        if (nev[t] >= 2)
            nmulti++;
        if (nev[t] >= 3)
            n3++;
        if (d < 0)
            nover++;
        if (d > decl[t]) {
            nmiss++;
            miss += d - decl[t];
            if (!quiet && nmiss <= 20)
                printf(
                    "  UNDECLARED SKIP: trail %lld is written in %lld events that leave out %lld of its %lld windows (the plan declares %lld)\n",
                    t, nev[t], d, TR[t].m, decl[t]);
        }
    }

    printf("plan: %lld events: P %lld, O %lld (gap-2 %lld, duplicate-skip %lld), S %lld\n", N, nP, nO, nOg2, nOskip,
           nS);
    printf("plan: trails in 2 or more events %lld, in 3 or more %lld, absent %lld\n", nmulti, n3, nabsent);
    printf("plan: joins by cost:");
    for (int d = 0; d <= h; d++)
        if (hist[d])
            printf(" %d:%lld", d, hist[d]);
    printf("\n");
    printf("plan: model length %lld, other word %lld\n", mlen, LF);
    printf("issues: incidental windows dropped %lld (in %lld runs)\n", ndropw, ndrop);
    printf(
        "issues: tight junctions %lld (re-cut at a shared duplicate %lld, of which a run vanished %lld; trimmed segments %lld, of which between two whole trails %lld)\n",
        ntight, nrecut, nvanish, ntrim, ntrim_whole);
    printf(
        "issues: whole trails at a cut that is not an opening %lld, undeclared skipped windows %lld (in %lld trails), trails covered twice %lld\n",
        nwhole_noopt, miss, nmiss, nover);
    printf(
        "issues: wasteful joins %lld (%lld letters), uncovered stretches %lld, open-path segments the loader cannot read %lld\n",
        nwaste, waste, nhole, nfixbad);

    FILE *f = fopen(argv[3], "wb");
    if (!f)
        DIE("cannot write %s", argv[3]); /* "wb": LF line ends on every system */
    fprintf(f, "TRAILSEARCH-PLAN %d %lld %lld\n", n, L, N);
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        if (x->kind == EV_PIECE)
            fprintf(f, "P %lld\n", x->a);
        else if (x->kind == EV_OPT)
            fprintf(f, "O %u %lld %d %d\n", x->t, x->a, x->g, x->g1);
        else
            fprintf(f, "S %u %lld %lld\n", x->t, x->a, x->l);
    }
    fclose(f);
    if (evpath) {
        f = fopen(evpath, "wb");
        if (!f)
            DIE("cannot write %s", evpath);
        fprintf(f, "# event  position  letters  join-cost-with-previous  windows  line\n");
        for (i64 i = 0; i < N; i++) {
            const Ev *x = &ev[i];
            fprintf(f, "%lld %lld %lld %d %lld ", i, x->x, x->l, i ? dist(ev[i - 1].e, x->s) : 0, RN[i].nw);
            if (x->kind == EV_PIECE)
                fprintf(f, "P %lld (trail %u)\n", x->a, x->t);
            else if (x->kind == EV_OPT)
                fprintf(f, "O %u %lld %d %d\n", x->t, x->a, x->g, x->g1);
            else
                fprintf(f, "S %u %lld %lld (R %lld, cut %d+%d)\n", x->t, x->a, x->l, TR[x->t].R, RN[i].lt, RN[i].rt);
        }
        fclose(f);
    }
    if (bad >= 0 || fp != LF || mlen != LF) {
        printf(
            "RESULT: NOT EXACT - the plan rebuilds a word of %lld letters that %s (first difference at letter %lld, event %lld); %s written anyway\n",
            mlen, mlen == LF ? "differs" : "is not the other word", fp, bad, argv[3]);
        return 2;
    }
    int safe = !ntrim && !miss && !nover && !nfixbad && !nabsent;
    printf(
        "RESULT: exact - %s rebuilds the other word letter for letter (%.1fs)%s\n", argv[3], wall() - t00,
        safe
            ? "; every event holds whole windows and every skipped window is declared: safe to search from"
            : "; BUT see the issues above: NOT safe to search from. Use --rebase NEWBASE.txt and convert again on NEWBASE");
    return 0;
}
