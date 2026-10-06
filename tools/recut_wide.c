/* recut_wide.c - the fixed-order pass with cuts inside a 1-cycle and tight joins.  Experimental.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).
   Cuts inside a 1-cycle are Theo H.'s idea, from his n = 11 word of 43,930,624 letters.

   What it does.  The other tools cut a closed trail at a step of weight 3 (free) or weight 2 (one letter), and
   join two pieces on their first and last h = n - 3 letters.  Theo H.'s word also cuts four trails inside a
   1-cycle, at a step of weight 1.  Such a piece has R + n - 1 letters, two more than the usual one, but two such
   pieces, or one of them and an ordinary piece, can overlap in n - 2 or n - 1 letters instead of at most h: a
   "tight join", which costs -1 or -2 against the model of the other tools.  This file measures joins on n - 1
   letters and offers the cuts inside a 1-cycle to the fixed-order pass.  I call this the wide model and the other
   the narrow one.
   The cuts inside a 1-cycle are not in the table of cuts (there would be 11 times more of them at n = 11).  They
   are generated where a neighbour in the order offers a tight join, or a chain of such pieces around one.  A piece
   cut inside a 1-cycle is written into the plan as a segment that holds the whole trail (S t start R+n-1), so the
   plan format is the same.
   Validity: every piece still consists of whole windows of its trail, and a join shares only letters that both
   pieces have, so no permutation is lost.

   Build:  gcc -O2 -mpopcnt -fopenmp -o recut_wide recut_wide.c -lm          (Linux: add -ldl)
   Use:    recut_wide BASE.txt OUT.txt --plan-in PLAN --wide --co-skip --time 0

   Take the word, not the plan.  A plan written here with tight joins is a plan of the wide model.  trailsearch,
   recut, relocate and segins read it without a warning but join on h letters, and rebuild a valid word that is
   longer (by 9 letters per tight join in my n = 11 tests).  To go on with the other tools from such a word, run
   word2plan --rebase on it: that writes a base word in which every chain of tightly joined pieces is one open
   piece that no tool moves.  My n = 12 words since 522,745,530 are plans on such a base.

   Options.
     --wide        the wide model, in the loader, in the pass and in the search
     --co          the pass once before the search and once after it (with --time 0: nothing else)
     --co-skip     the same, and a cut may drop either occurrence of a duplicated permutation
     --g1 M        which cuts inside a 1-cycle the pass is offered: 0 = those next to a tight join with the neighbour
                   in the order, 1 (default) = also one step of chains of such pieces, 2 = chains to the end,
                   3 = every such cut (exact, 10 times the states).  1 gave the result of 3 on all 17 orders I
                   compared; 0 does not (43,930,631 against 43,930,629 on one of them)
     --coit N      inside the search: the pass on the current sequence of a thread every N iterations
                   (--coit-g1 M: with that rule in place of the one of --g1)
     --gpu, --ptx FILE, --gpumin N, --gpucheck, --gpucopy, --gpuprof
                   the search on a card, with the first generation of the card code.  With --wide the kernel file
                   must be built from kern_wide.cu.  Not tested again for this release
     and all options of trailsearch.c.  Without --wide, --co and --coit the search is the plain one.

   What it gave.  One pass in the wide model: 43,930,628 to 43,930,624 (the narrow pass gives 43,930,625), 43,930,632
   to 43,930,629 (narrow 631) and, with the same pass as it is written in word2plan --rephase, 522,745,537 to
   522,745,530 (narrow 531).  On every later word I tried it gives exactly what the narrow pass gives.  The search in the wide model was not better than the narrow one in ten
   runs from Pantone's n = 11 word (means 651.1 and 654.4 in the last three digits, not significant).
   Memory and time.  n = 11: 2.7 seconds for the pass on 2 threads (narrow: 0.3).  n = 12: 60 seconds.  n = 13: never
   run; by the count 1.2 to 1.6 GB on top of the narrow pass.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.
   A "gap-1 opening" is a cut inside a 1-cycle.

   Layout of this file.  It is a copy of the present trailsearch.c with the first generation of the card code of
   trailsearch_gpu.c, and these parts added, marked by lines of equal signs: the wide model (words of n - 1
   letters, tight joins), the fixed-order pass in both models (cw_run), and the wide model in the search. */
#if !defined(_WIN32)
#define _FILE_OFFSET_BITS 64
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
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
typedef unsigned int u32;

static const char *AL = "0123456789ABCDEF";
static unsigned char *W;
static i64 L;
static int n, h;
static int wide = 0; /* --wide */
#define NL "\n"
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

/* ==================== shared base (trailsearch.c): model, plan, index, search moves ==================== */
/* ---------- h-words packed 4 bits per symbol (first symbol highest) */
static u64 HMASK[17];
/* h - largest k with suffix_k(e) == prefix_k(s) */
static inline int dist(u64 e, u64 s) {
    for (int k = h; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (h - k))))
            return h - k;
    return h;
}

/* ---------- trails */
/* cyclic word, its length, option range */
typedef struct {
    unsigned char *c;
    i64 R;
    i64 olo, ohi;
    int fixed;
} Trail;
/* fixed: an open path of R + h letters that is not a closed trail in the word; its pieces are never moved */
static Trail *TR;
static i64 NT;
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
/* h-word at cyclic position pos */
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
static u64 fact[17];
/* Rank (0 .. n! - 1, lexicographic) of the permutation in the n letters at p.  p must hold n different letters. */
static inline u64 rank_lin(const unsigned char *p) {
    u64 r = 0;
    int used = 0;
    for (int k = 0; k < n; k++) {
        int c = p[k];
        r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* rank of the permutation window at cyclic position pos */
static inline u64 rank_cyc(const Trail *t, i64 pos) {
    u64 r = 0;
    int used = 0;
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    if (pos + n <= R) {
        const unsigned char *p = t->c + pos;
        for (int k = 0; k < n; k++) {
            int c = p[k];
            r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
            used |= 1 << c;
        }
    } else
        for (int k = 0; k < n; k++) {
            int c = t->c[(pos + k) % R];
            r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[n - 1 - k];
            used |= 1 << c;
        }
    return r;
}

/* ---------- options: 6 bytes each */
typedef struct __attribute__((packed)) {
    u32 start;
    unsigned char g, g1;
} Opt;
/* the piece starts at `start`; total gap g; g1 > 0: skip option, the skipped window lies g1 after the previous window.
   The options of a trail are contiguous (TR[t].olo .. ohi), so the trail of an option is found by binary search. */
static Opt *OP;
static i64 NO;
/* The trail of cut o (binary search in the first cuts of the trails). */
static inline u32 otrail(i64 o) {
    i64 lo = 0, hi = NT - 1;
    while (lo < hi) {
        i64 m = (lo + hi + 1) >> 1;
        if (TR[m].olo <= o)
            lo = m;
        else
            hi = m - 1;
    }
    return (u32)lo;
}
static inline int oD(i64 o) {
    return 3 - (int)OP[o].g;
}
static inline u64 oS_t(const Trail *T, i64 o) {
    return hw_cyc(T, OP[o].start);
}
static inline u64 oE_t(const Trail *T, i64 o) {
    return hw_cyc(T, (i64)OP[o].start - OP[o].g + 3);
}
static inline i64 oSK_t(const Trail *T, i64 o) {
    return OP[o].g1 ? (i64)rank_cyc(T, (i64)OP[o].start - OP[o].g + OP[o].g1) : -1;
}
static inline u64 oS(i64 o) {
    return oS_t(&TR[otrail(o)], o);
}
static inline u64 oE(i64 o) {
    return oE_t(&TR[otrail(o)], o);
}

/* ---------- events */
enum { EV_PIECE, EV_OPT, EV_SEG };
typedef struct {
    int kind;
    u32 t;
    u64 s, e;
    i64 l;
    i64 a;
    i64 skip;
    u32 x2;
} Ev;
/* x2 (wide model only, else 0): the 2 letters after the first h (bits 0-7) and the 2 letters before the last h (bits 8-15) */
/* EV_PIECE: a = piece index.  EV_OPT: a = option.  EV_SEG: a = start offset in the trail, l letters. */
static i64 *PS, *PL;
static i64 NP; /* pieces of the input word */

/* ==================== own part: the wide model ==================== */
/* ---------- wide model: words of n - 1 letters (the h-word and the 2 letters beyond it), joins that overlap in n - 2
   or n - 1 letters ("tight", cost -1 / -2).  jdist is the cost of the join of two events; with --wide off it is dist. */
/* letter r of the event */
static inline unsigned char ev_letter(const Ev *x, i64 r) {
    if (x->kind == EV_PIECE)
        return W[PS[x->a] + r];
    const Trail *t = &TR[x->t];
    i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a;
    return t->c[(st + r) % t->R];
}
/* Fills x->x2 with the two letters after the start h-word and the two before the end h-word, so that a join
   can be measured on n - 1 letters.  Does nothing without --wide. */
static inline void ev_wide(Ev *x) {
    x->x2 = 0;
    if (!wide)
        return;
    x->x2 = (u32)ev_letter(x, h) << 4 | ev_letter(x, h + 1) | (u32)ev_letter(x, x->l - h - 2) << 12 |
            (u32)ev_letter(x, x->l - h - 1) << 8;
}
#define WS(x) (((x)->s << 8) | ((x)->x2 & 255))           /* first n - 1 letters */
#define WE(x) (((u64)((x)->x2 >> 8) << (4 * h)) | (x)->e) /* last n - 1 letters */
static inline int wtight(u64 we, u64 ws) {
    return we == ws ? 2 : (we & HMASK[h + 1]) == (ws >> 4) ? 1 : 0;
}
/* join of two wide words */
static inline int wdist(u64 we, u64 ws) {
    int t = wtight(we, ws);
    return t ? -t : dist(we & HMASK[h], ws >> 8);
}
static inline int jdist(const Ev *a, const Ev *b) {
    if (wide) {
        int t = wtight(WE(a), WS(b));
        if (t)
            return -t;
    }
    return dist(a->e, b->s);
}
/* word of n - 1 letters at cyclic position pos */
static inline u64 ww_cyc(const Trail *t, i64 pos) {
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
    if (pos + n - 1 <= R) { /* two 8-byte loads (all buffers have 16 spare bytes at the end) */
#define WW_P8(q, x)                                       \
    {                                                     \
        memcpy(&x, q, 8);                                 \
        x = __builtin_bswap64(x) & 0x0F0F0F0F0F0F0F0FULL; \
        x = (x | (x >> 4)) & 0x00FF00FF00FF00FFULL;       \
        x = (x | (x >> 8)) & 0x0000FFFF0000FFFFULL;       \
        x = (x | (x >> 16)) & 0xFFFFFFFFULL;              \
    }
        const unsigned char *p = t->c + pos;
        u64 a, b;
        int l = n - 1;
        WW_P8(p, a);
        if (l <= 8)
            return a >> (4 * (8 - l));
        WW_P8(p + l - 8, b);
        return (a << (4 * (l - 8))) | (b & HMASK[l - 8]);
#undef WW_P8
    }
#endif
    u64 v = 0;
    for (int k = 0; k < n - 1; k++) {
        v = (v << 4) | t->c[pos];
        if (++pos == R)
            pos = 0;
    }
    return v;
}
/* Length of the word of a sequence: the letters of all events minus the overlaps at the joins. */
static i64 seq_length(const Ev *ev, i64 N) {
    i64 len = 0;
    for (i64 i = 0; i < N; i++)
        len += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++)
        len -= h - jdist(&ev[i], &ev[i + 1]);
    return len;
}
/* The event for cut o: its trail written once from that cut.  Start word, end word, length R + h + cost of the
   cut, and the rank of the occurrence it drops (-1: none). */
static Ev make_event(i64 o) {
    u32 t = otrail(o);
    const Trail *T = &TR[t];
    Ev x;
    x.kind = EV_OPT;
    x.t = t;
    x.s = oS_t(T, o);
    x.e = oE_t(T, o);
    x.l = T->R + h + oD(o);
    x.a = o;
    x.skip = oSK_t(T, o);
    ev_wide(&x);
    return x;
}
/* The event for piece k of the input word, left as it is. */
static Ev piece_event(i64 k, i64 trail) {
    Ev x;
    x.kind = EV_PIECE;
    x.t = (u32)trail;
    x.s = hw_lin(W + PS[k]);
    x.e = hw_lin(W + PS[k] + PL[k] - h);
    x.l = PL[k];
    x.a = k;
    x.skip = -1;
    ev_wide(&x);
    return x;
}
/* a segment event: l letters of trail t from offset st */
static Ev seg_event(u32 t, i64 st, i64 l) {
    Ev x;
    x.kind = EV_SEG;
    x.t = t;
    x.a = st;
    x.l = l;
    x.s = hw_cyc(&TR[t], st);
    x.e = hw_cyc(&TR[t], st + l - h);
    x.skip = -1;
    ev_wide(&x);
    return x;
}
/* the whole trail written from the gap-1 cut in front of the window at st: R + n - 1 letters */
static inline Ev g1_event(u32 t, i64 st) {
    return seg_event(t, st, TR[t].R + n - 1);
}
static inline int is_g1(const Ev *x) {
    return x->kind == EV_SEG && !TR[x->t].fixed && x->l == TR[x->t].R + n - 1;
}
/* two events for a trail split at plain cuts c1 (start of segment 1) and c2 (end of segment 1) */
static void seg_events(i64 c1, i64 c2, Ev *e1, Ev *e2) {
    u32 t = otrail(c1);
    i64 R = TR[t].R;
    i64 st1 = OP[c1].start, en1 = ((i64)OP[c2].start - OP[c2].g + R) % R, l1 = ((en1 - st1) % R + R) % R + n;
    i64 st2 = OP[c2].start, en2 = ((i64)OP[c1].start - OP[c1].g + R) % R, l2 = ((en2 - st2) % R + R) % R + n;
    e1->kind = EV_SEG;
    e1->t = t;
    e1->s = oS(c1);
    e1->e = oE(c2);
    e1->l = l1;
    e1->a = st1;
    e1->skip = -1;
    ev_wide(e1);
    e2->kind = EV_SEG;
    e2->t = t;
    e2->s = oS(c2);
    e2->e = oE(c1);
    e2->l = l2;
    e2->a = st2;
    e2->skip = -1;
    ev_wide(e2);
}

/* ==================== shared base again; the card code is the first generation of trailsearch_gpu.c ==================== */
/* ---------- output */
static void write_word(const Ev *ev, i64 N, const char *path, i64 expect) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0;
    char *out = malloc(cap);
    i64 total = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - jdist(&ev[i - 1], x) : 0;
        for (i64 r = skip; r < x->l; r++) {
            unsigned char c;
            if (x->kind == EV_PIECE)
                c = W[PS[x->a] + r];
            else {
                const Trail *t = &TR[x->t];
                i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a;
                c = t->c[(st + r) % t->R];
            }
            out[ob++] = AL[c];
            if (ob == cap) {
                fwrite(out, 1, ob, f);
                ob = 0;
            }
        }
        total += x->l - skip;
    }
    out[ob++] = '\n';
    fwrite(out, 1, ob, f);
    fclose(f);
    free(out);
    if (total != expect)
        DIE("internal error: wrote %lld letters, model says %lld", total, expect);
}
/* Writes the sequence as a plan: a head line, then one line per event (P, O or S), with LF line ends. */
static void write_plan(const Ev *ev, i64 N, const char *path) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path); /* "wb": LF line ends on every system */
    fprintf(f, "TRAILSEARCH-PLAN %d %lld %lld\n", n, L, N);
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        if (x->kind == EV_PIECE)
            fprintf(f, "P %lld\n", x->a);
        else if (x->kind == EV_OPT)
            fprintf(f, "O %u %u %d %d\n", x->t, OP[x->a].start, OP[x->a].g, OP[x->a].g1);
        else
            fprintf(f, "S %u %lld %lld\n", x->t, x->a, x->l);
    }
    fclose(f);
}

/* ---------- hash multimap: key -> list of ints */
typedef struct {
    u64 key;
    int head;
} Slot;
typedef struct {
    Slot *t;
    u64 mask;
    int *next, *val;
    i64 n, cap;
} HTab;
static inline u64 hmix(u64 k) {
    k ^= k >> 33;
    k *= 0xFF51AFD7ED558CCDULL;
    k ^= k >> 33;
    k *= 0xC4CEB9FE1A85EC53ULL;
    k ^= k >> 33;
    return k;
}
#define HKEY(word, j, kind) (((u64)(word) << 8) | ((u64)(j) << 4) | (u64)(kind)) /* word < 2^40 */
static void h_reset(HTab *H, i64 entries) {
    u64 need = 1024;
    while (need < (u64)entries + (u64)entries / 2 + 16)
        need <<= 1;
    if (!H->t || need - 1 != H->mask) {
        free(H->t);
        H->t = malloc(need * sizeof(Slot));
        H->mask = need - 1;
    }
    for (u64 i = 0; i <= H->mask; i++) {
        H->t[i].head = -1;
        H->t[i].key = ~0ULL;
    }
    if (entries > H->cap) {
        H->cap = entries + entries / 2 + 64;
        free(H->next);
        free(H->val);
        H->next = malloc(H->cap * sizeof(int));
        H->val = malloc(H->cap * sizeof(int));
    }
    H->n = 0;
}
/* Adds value v to the list of key (open addressing with linear probing; the new entry becomes the head of its
   list).  The caller guarantees room: h_reset / h_init were called with enough entries. */
static inline void h_add(HTab *H, u64 key, int v) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL && H->t[i].key != key)
        i = (i + 1) & H->mask;
    H->t[i].key = key;
    H->next[H->n] = H->t[i].head;
    H->val[H->n] = v;
    H->t[i].head = (int)H->n++;
}
/* First entry of the list of key, or -1.  The list is walked with H->next[], the values are in H->val[]. */
static inline int h_get(const HTab *H, u64 key) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != ~0ULL) {
        if (H->t[i].key == key)
            return H->t[i].head;
        i = (i + 1) & H->mask;
    }
    return -1;
}
#define KLEV 3     /* joins of cost <= KLEV are looked up */
#define ENT_PER 12 /* index entries per event */
static double tlimit = 600, T0 = 1.5, ckpt_sec = 600, prel = 0.4, sync_sec = 60;
static double bigp = 1.0;  /* probability of keeping a big trail (more than splitmax options) in the removal set */
static double focus = 0.0; /* probability of skipping an iteration whose removal set has no big trail */
static int kmax = 6, use_skip = 1, use_split = 1, splitmax = 3000, NTHR = 1;
static u64 seed = 1;
static i64 maxit = -1;

/* ---------- one search thread: the sequence is a doubly linked list of nodes, so an insertion does not renumber
   anything and the hash index (word -> node) is only ever appended to; dead nodes are skipped at lookup and the
   index is rebuilt when it is mostly garbage.  A rejected move is undone by unlinking / relinking nodes. */
/* lab: order label (increasing along the list) */
typedef struct {
    Ev v;
    int prev, next, alive;
    u64 lab;
} Node;
typedef struct {
    i64 c2;
    int i, jm;
    i64 cst;
} Pair;
typedef struct {
    u64 lab;
    int id;
} RelRun;
typedef struct {
    int tid;
    u64 rs[4];
    Node *nd;
    int ncap, nn, first, last;
    i64 N;
    int relabeled;
    HTab H;
    u32 *rst;
    int rstcap;
    RelRun *rr;
    int rrcap, nrr;
    u64 *bf, bfmask; /* bf: one-hash Bloom filter over the keys of H */
    int *order, *cand, *tnx, *wk, *wc, *rel, *remlog, *inslog;
    int nremlog, ninslog;
    i64 ncand;
    int *thead, *rth;
    i64 *rk;
    int rkcap;
    struct Iv *iv;
    int ivcap; /* see seq_build */
    i64 *skp;
    int nskp, skpcap;
    i64 *vid;
    int vcap;
    Pair *pr;
    i64 pcap;
    int *Ib, *Jb;
    int icap, jcap;
    char *rem;
    u32 *pend;
    Ev *tmp;
    struct GM *G;
    u64 trh; /* GPU mirror (NULL: none); checksum of the accept / reject history */
    HTab TX;
    u32 *txk;
    int txcap; /* wide: tight index (trail * 2 + side -> nodes), the keys of every node */
    i64 wst
        [5]; /* wide: offered cuts measured, insertions they won, of these gap-1 cuts, passes of --coit with a gain, passes */
    u64 cohash;
    i64 colen;
    double
        cosec; /* --coit: order of the trails and length after the last pass (same order, same length: nothing to do); seconds */
    i64 cur, best_len, it, acc;
    u64 nzk, nzit; /* noise keys of the thread and of the iteration */
} Ctx;

typedef struct GM GM;
static void gm_link(Ctx *c, int id);
static void gm_ins(Ctx *c, int id);
static void gm_reset(Ctx *c);
static void gm_del(Ctx *c, u64 i, int p); /* GPU mirror hooks */
static double wall(void);
static void tx_add(Ctx *c, int id);
static void tx_del(Ctx *c, int id);
static void tx_reset(Ctx *c); /* wide: tight index hooks */
static u32 *CYC;

static inline u64 rotl(u64 x, int k) {
    return (x << k) | (x >> (64 - k));
}
/* xoshiro256** */
static inline u64 rnd64(Ctx *c) {
    u64 *s = c->rs, r = rotl(s[1] * 5, 7) * 9, t = s[1] << 17;
    s[2] ^= s[0];
    s[3] ^= s[1];
    s[1] ^= s[2];
    s[0] ^= s[3];
    s[2] ^= t;
    s[3] = rotl(s[3], 45);
    return r;
}
/* Seeds the random generator of a search thread from s (splitmix64). */
static void rseed(Ctx *c, u64 s) {
    for (int i = 0; i < 4; i++) {
        s += 0x9E3779B97F4A7C15ULL;
        u64 z = s;
        z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
        z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
        c->rs[i] = z ^ (z >> 31);
    }
}
static inline double rndu(Ctx *c) {
    return (rnd64(c) >> 11) * (1.0 / 9007199254740992.0);
}
/* 0 .. m-1 */
static inline i64 rndn(Ctx *c, i64 m) {
    return (i64)(rnd64(c) % (u64)m);
}
/* a .. b */
static inline i64 rndint(Ctx *c, i64 a, i64 b) {
    return a + rndn(c, b - a + 1);
}

/* index kinds: 0 = suffix (length h-j) of e, 1 = prefix (length h-j) of s, 2 / 3 = the lookups of best_split */
#define BFH(key) (((u64)(key) * 0x9E3779B97F4A7C15ULL) >> 32)
#define BFBIT(c, key)                          \
    {                                          \
        u64 b_ = BFH(key) & (c)->bfmask;       \
        (c)->bf[b_ >> 6] |= 1ULL << (b_ & 63); \
    }
static inline int bf_has(const Ctx *c, u64 key) {
    u64 b = BFH(key) & c->bfmask;
    return (int)((c->bf[b >> 6] >> (b & 63)) & 1);
}
/* Enters node id into the index of the thread: for overlaps h down to h - KLEV the end of its end word and the
   beginning of its start word, and (with two-segment insertion on) the four keys best_split looks up.
   Sets the bits of the Bloom filter.  The keys and their order are what index_del relies on. */
static inline void index_add(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    for (int j = 0; j <= KLEV; j++) {
        u64 k0 = HKEY(x->e & HMASK[h - j], j, 0), k1 = HKEY(x->s >> (4 * j), j, 1);
        h_add(&c->H, k0, id);
        h_add(&c->H, k1, id);
        BFBIT(c, k0);
        BFBIT(c, k1);
    }
    if (use_split) {
        h_add(&c->H, HKEY(x->s, 0, 2), id);
        h_add(&c->H, HKEY(x->s >> 4, 1, 2), id);
        h_add(&c->H, HKEY(x->e, 0, 3), id);
        h_add(&c->H, HKEY(x->e & HMASK[h - 1], 1, 3), id);
    }
}
/* a node that will never be relinked leaves the index: its entries are taken out of their chains (the entry arrays stay
   append-only, so the index is rebuilt exactly when it was before) */
static void index_del(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    HTab *H = &c->H;
    u64 k[2 * (KLEV + 1) + 4];
    int nk = 0;
    for (int j = 0; j <= KLEV; j++) {
        k[nk++] = HKEY(x->e & HMASK[h - j], j, 0);
        k[nk++] = HKEY(x->s >> (4 * j), j, 1);
    }
    if (use_split) {
        k[nk++] = HKEY(x->s, 0, 2);
        k[nk++] = HKEY(x->s >> 4, 1, 2);
        k[nk++] = HKEY(x->e, 0, 3);
        k[nk++] = HKEY(x->e & HMASK[h - 1], 1, 3);
    }
    for (int z = 0; z < nk; z++) {
        u64 i = hmix(k[z]) & H->mask;
        while (H->t[i].key != k[z])
            i = (i + 1) & H->mask;
        int p = -1, e = H->t[i].head;
        while (H->val[e] != id) {
            p = e;
            e = H->next[e];
        }
        if (p < 0)
            H->t[i].head = H->next[e];
        else
            H->next[p] = H->next[e];
        if (c->G)
            gm_del(c, i, p);
    }
    if (c->txk)
        tx_del(c, id);
}
static void seq_build(Ctx *c);
/* Loads a sequence of N events into the thread: nodes, order labels, index, Bloom filter and the kept arrays
   (seq_build).  Buffers grow when needed.  ev may be the thread's own c->tmp. */
static void ctx_load(Ctx *c, const Ev *ev, i64 N) {
    int need = (int)(4 * N + 65536), self = ev == c->tmp;
    if (need > c->ncap) {
        c->ncap = need;
        c->nd = realloc(c->nd, (size_t)need * sizeof(Node));
        int **arr[] = {&c->order, &c->cand, &c->tnx, &c->wk, &c->wc, &c->rel, &c->remlog, &c->inslog};
        for (int k = 0; k < 8; k++)
            *arr[k] = realloc(*arr[k], (size_t)need * sizeof(int));
        c->tmp = realloc(c->tmp, (size_t)need * sizeof(Ev));
        if (self)
            ev = c->tmp;
        if (!c->nd || !c->inslog || !c->tmp)
            DIE("out of memory");
    }
    c->nn = (int)N;
    c->N = N;
    c->first = 0;
    c->last = (int)N - 1;
    for (i64 i = 0; i < N; i++) {
        Node *q = &c->nd[i];
        q->v = ev[i];
        q->prev = (int)i - 1;
        q->next = i + 1 < N ? (int)i + 1 : -1;
        q->alive = 1;
        q->lab = (u64)(i + 1) << 32;
    }
    i64 ecap = (N > 100000 ? 2 : 4) * ENT_PER * N + 65536; /* live entries plus head-room for dead ones */
    h_reset(&c->H, ecap);
    {
        u64 bits = 1 << 16;
        while (bits < (u64)ecap * 16)
            bits <<= 1;
        if (bits - 1 != c->bfmask || !c->bf) {
            free(c->bf);
            c->bf = malloc(bits / 8);
            c->bfmask = bits - 1;
        }
        memset(c->bf, 0, bits / 8);
    }
    for (i64 i = 0; i < N; i++)
        index_add(c, (int)i);
    if (CYC)
        tx_reset(c);
    seq_build(c);
    if (c->G)
        gm_reset(c);
}
static i64 ctx_export(const Ctx *c, Ev *out) {
    i64 m = 0;
    for (int id = c->first; id >= 0; id = c->nd[id].next)
        out[m++] = c->nd[id].v;
    return m;
}
/* Length of the word of the current sequence, by walking the list. */
static i64 ctx_length(const Ctx *c) {
    i64 len = 0;
    for (int id = c->first; id >= 0;) {
        const Node *q = &c->nd[id];
        len += q->v.l;
        if (q->next >= 0)
            len -= h - jdist(&q->v, &c->nd[q->next].v);
        id = q->next;
    }
    return len;
}
static void relabel(Ctx *c) {
    u64 k = 1;
    for (int id = c->first; id >= 0; id = c->nd[id].next)
        c->nd[id].lab = (k++) << 32;
    c->relabeled = 1;
}
/* Takes node id out of the list.  Its prev / next stay as they were, so node_relink can undo it. */
static void node_unlink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0)
        c->nd[q->prev].next = q->next;
    else
        c->first = q->next;
    if (q->next >= 0)
        c->nd[q->next].prev = q->prev;
    else
        c->last = q->prev;
    q->alive = 0;
    c->N--;
    if (c->G)
        gm_link(c, id);
}
/* Puts back a node that node_unlink took out.  Nodes must come back in the reverse order of their removal. */
static void node_relink(Ctx *c, int id) {
    Node *q = &c->nd[id];
    if (q->prev >= 0)
        c->nd[q->prev].next = id;
    else
        c->first = id;
    if (q->next >= 0)
        c->nd[q->next].prev = id;
    else
        c->last = id;
    q->alive = 1;
    c->N++;
    if (c->G)
        gm_link(c, id);
}
/* Inserts a new node with event x after node a: a label between its neighbours (the list is relabelled if
   there is no room), an index entry, a line in the insertion log for undo.  Returns the node. */
static int node_insert_after(Ctx *c, int a, const Ev *x) {
    int b = c->nd[a].next;
    u64 la = c->nd[a].lab, lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33);
    if (lb - la < 2) {
        relabel(c);
        la = c->nd[a].lab;
        lb = b >= 0 ? c->nd[b].lab : la + (1ULL << 33);
    }
    int id = c->nn++;
    Node *q = &c->nd[id];
    q->v = *x;
    q->prev = a;
    q->next = b;
    q->alive = 1;
    q->lab = la + (lb - la) / 2;
    c->nd[a].next = id;
    if (b >= 0)
        c->nd[b].prev = id;
    else
        c->last = id;
    index_add(c, id);
    if (c->txk)
        tx_add(c, id);
    c->inslog[c->ninslog++] = id;
    c->N++;
    c->tnx[id] = c->thead[x->t];
    c->thead[x->t] = id;
    if (c->G)
        gm_ins(c, id);
    return id;
}
static int skp_has(const Ctx *c, i64 r) {
    for (int i = 0; i < c->nskp; i++)
        if (c->skp[i] == r)
            return 1;
    return 0;
}
/* Adds permutation r to the list of duplicates dropped by the skip cuts of the move under way. */
static void skp_add(Ctx *c, i64 r) {
    if (c->nskp == c->skpcap) {
        c->skpcap = c->skpcap ? c->skpcap * 2 : 256;
        c->skp = realloc(c->skp, c->skpcap * sizeof(i64));
    }
    c->skp[c->nskp++] = r;
}
static void skp_del(Ctx *c, i64 r) {
    for (int i = 0; i < c->nskp; i++)
        if (c->skp[i] == r) {
            c->skp[i] = c->skp[--c->nskp];
            return;
        }
}

/* ---------- what the search keeps about the sequence between iterations, so that an iteration does not walk the
   whole list: order[] (position -> node), cand[] (the positions i whose join i -> i+1 costs >= 2, increasing; they
   are also the ends of the runs), the nodes of every trail (thead[t], then tnx[]) and skp[] (the skipped windows of
   the sequence, in any order).  Built here after every load, patched after an accepted move (seq_patch); a
   rejected move restores the list exactly, so nothing has to be done for it. */
static void seq_build(Ctx *c) {
    const Node *nd = c->nd;
    i64 N = 0, nc = 0;
    memset(c->thead, 0xff, ((size_t)NT + 1) * sizeof(int));
    c->nskp = 0;
    for (int id = c->first; id >= 0; id = nd[id].next) {
        if (N && jdist(&nd[c->order[N - 1]].v, &nd[id].v) >= 2)
            c->cand[nc++] = (int)N - 1;
        c->order[N++] = id;
        c->tnx[id] = c->thead[nd[id].v.t];
        c->thead[nd[id].v.t] = id;
        if (nd[id].v.skip >= 0)
            skp_add(c, nd[id].v.skip);
    }
    c->ncand = nc;
}
/* position of node id in order[0 .. N-1], by its label */
static inline i64 seq_pos(const Ctx *c, int id, i64 N) {
    u64 lab = c->nd[id].lab;
    i64 lo = 0, hi = N - 1;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (c->nd[c->order[m]].lab < lab)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* number of entries of cand[] below p */
static inline i64 cand_lb(const Ctx *c, i64 p) {
    i64 lo = 0, hi = c->ncand;
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (c->cand[m] < p)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* what node id adds to the length where it stands */
static inline i64 node_len(const Ctx *c, int id) {
    const Node *nd = c->nd, *x = &nd[id];
    int a = x->prev, b = x->next;
    i64 d = x->v.l;
    if (a >= 0)
        d -= h - jdist(&nd[a].v, &x->v);
    if (b >= 0)
        d -= h - jdist(&x->v, &nd[b].v);
    if (a >= 0 && b >= 0)
        d += h - jdist(&nd[a].v, &nd[b].v);
    return d;
}
/* After an accepted move: the nodes at positions rk[] >> 32 of order[0 .. N0-1] were removed and the nodes with
   id >= nn0 were inserted (no relabelling in between, so the old labels still sort order[]).  The changes are
   merged into intervals (l, r) of old positions whose ends are untouched nodes (-1 / N0: the ends of the list);
   between them the list is walked, outside them order[] and cand[] are only shifted. */
typedef struct Iv {
    int l, r, w, ia, ib, nc;
    i64 sh, ish;
} Iv;
static int iv_cmp(const void *a, const void *b) {
    int x = ((const Iv *)a)->l, y = ((const Iv *)b)->l;
    return x < y ? -1 : x > y;
}
static int i64_cmp(const void *a, const void *b) {
    i64 x = *(const i64 *)a, y = *(const i64 *)b;
    return x < y ? -1 : x > y;
}
/* Brings order[] and cand[] up to date after an accepted move (see the comment above the type Iv). */
static void seq_patch(Ctx *c, i64 N0, int nn0) {
    const Node *nd = c->nd;
    int *order = c->order, *cand = c->cand, *wk = c->wk, *wc = c->wc;
    int m = 0, k = 0;
    if (c->nremlog + c->ninslog > c->ivcap) {
        c->ivcap = 2 * (c->nremlog + c->ninslog) + 64;
        c->iv = realloc(c->iv, (size_t)c->ivcap * sizeof(Iv));
    }
    Iv *iv = c->iv;
    for (int q = 0; q < c->nremlog; q++) {
        int p = (int)(c->rk[q] >> 32);
        iv[m].l = p - 1;
        iv[m].r = p + 1;
        m++;
    }
    for (int q = 0; q < c->ninslog; q++) {
        int a = nd[c->inslog[q]].prev;
        if (a >= nn0)
            continue; /* only the first node of a chain of new nodes */
        int p = a < 0 ? -1 : (int)seq_pos(c, a, N0);
        iv[m].l = p;
        iv[m].r = p + 1;
        m++;
    }
    if (!m)
        return;
    qsort(iv, (size_t)m, sizeof(Iv), iv_cmp);
    for (int q = 1; q < m; q++) {
        if (iv[q].l <= iv[k].r) {
            if (iv[q].r > iv[k].r)
                iv[k].r = iv[q].r;
        } else
            iv[++k] = iv[q];
    }
    m = k + 1;
    i64 nw = 0, sh = 0, ish = 0, z = 0;
    for (int q = 0; q < m; q++) { /* the new nodes between l and r */
        int id = iv[q].l < 0 ? c->first : nd[order[iv[q].l]].next, stop = iv[q].r >= N0 ? -1 : order[iv[q].r];
        for (iv[q].w = 0; id != stop; id = nd[id].next) {
            wk[nw++] = id;
            iv[q].w++;
        }
        sh += iv[q].w - (iv[q].r - iv[q].l - 1);
        iv[q].sh = sh; /* shift of everything from r to the next l */
        iv[q].ia = (int)cand_lb(c, iv[q].l);
        iv[q].ib = (int)cand_lb(c, iv[q].r);
    }
#define SEG_A(q) ((i64)iv[q].r)
#define SEG_B(q) ((q) + 1 < m ? (i64)iv[(q) + 1].l : N0 - 1)
    /* in place: the segments that move left from left to right, then those that move right from right to left */
    for (int q = 0; q < m; q++)
        if (iv[q].sh < 0 && SEG_B(q) >= SEG_A(q))
            memmove(order + SEG_A(q) + iv[q].sh, order + SEG_A(q), (size_t)(SEG_B(q) - SEG_A(q) + 1) * sizeof(int));
    for (int q = m - 1; q >= 0; q--)
        if (iv[q].sh > 0 && SEG_B(q) >= SEG_A(q))
            memmove(order + SEG_A(q) + iv[q].sh, order + SEG_A(q), (size_t)(SEG_B(q) - SEG_A(q) + 1) * sizeof(int));
    for (int q = 0; q < m; q++) {
        memcpy(order + iv[q].l + 1 + (q ? iv[q - 1].sh : 0), wk + z, (size_t)iv[q].w * sizeof(int));
        z += iv[q].w;
    }
    /* cand[]: the joins from l to r are computed again, the others keep their place in the list */
    nw = 0;
    for (int q = 0; q < m; q++) {
        i64 lo = iv[q].l + (q ? iv[q - 1].sh : 0), hi = lo + iv[q].w;
        if (lo < 0)
            lo = 0;
        if (hi > c->N - 2)
            hi = c->N - 2;
        iv[q].nc = 0;
        for (i64 j = lo; j <= hi; j++)
            if (jdist(&nd[order[j]].v, &nd[order[j + 1]].v) >= 2) {
                wc[nw++] = (int)j;
                iv[q].nc++;
            }
        ish += iv[q].nc - (iv[q].ib - iv[q].ia);
        iv[q].ish = ish;
    }
#define CSEG_B(q) ((q) + 1 < m ? (i64)iv[(q) + 1].ia : c->ncand)
    for (int q = 0; q < m; q++)
        if (iv[q].ish <= 0 && (iv[q].ish || iv[q].sh))
            for (i64 i = iv[q].ib, b = CSEG_B(q); i < b; i++)
                cand[i + iv[q].ish] = cand[i] + (int)iv[q].sh;
    for (int q = m - 1; q >= 0; q--)
        if (iv[q].ish > 0)
            for (i64 i = CSEG_B(q) - 1; i >= iv[q].ib; i--)
                cand[i + iv[q].ish] = cand[i] + (int)iv[q].sh;
    z = 0;
    for (int q = 0; q < m; q++) {
        memcpy(cand + iv[q].ia + (q ? iv[q - 1].ish : 0), wc + z, (size_t)iv[q].nc * sizeof(int));
        z += iv[q].nc;
    }
    c->ncand += ish;
#undef SEG_A
#undef SEG_B
#undef CSEG_B
}
#ifdef TS_CHECK /* -DTS_CHECK=1: print the final state of every thread; =2: also verify the kept arrays at every iteration */
static void seq_check(Ctx *c) {
    const Node *nd = c->nd;
    i64 N = 0, nc = 0, ns = 0;
    for (int id = c->first; id >= 0; id = nd[id].next) {
        if (N && jdist(&nd[c->order[N - 1]].v, &nd[id].v) >= 2) {
            if (nc >= c->ncand || c->cand[nc] != N - 1)
                DIE("check: cand[%lld] at it %lld", nc, c->it);
            nc++;
        }
        if (c->order[N] != id)
            DIE("check: order[%lld] at it %lld", N, c->it);
        if (N && nd[c->order[N - 1]].lab >= nd[id].lab)
            DIE("check: labels at it %lld", c->it);
        int z = c->thead[nd[id].v.t];
        while (z >= 0 && z != id)
            z = c->tnx[z];
        if (z < 0)
            DIE("check: trail chain at it %lld", c->it);
        if (nd[id].v.skip >= 0) {
            ns++;
            if (!skp_has(c, nd[id].v.skip))
                DIE("check: skp at it %lld", c->it);
        }
        N++;
    }
    if (N != c->N || nc != c->ncand || ns != c->nskp)
        DIE("check: N %lld/%lld ncand %lld/%lld nskp %lld/%d at it %lld", N, c->N, nc, c->ncand, ns, c->nskp, c->it);
    for (i64 t = 0; t < NT; t++)
        for (int z = c->thead[t]; z >= 0; z = c->tnx[z]) {
            if (!nd[z].alive || nd[z].v.t != t)
                DIE("check: dead node in a trail chain at it %lld", c->it);
            N--;
        }
    if (N)
        DIE("check: trail chains at it %lld", c->it);
    if (c->cur != ctx_length(c))
        DIE("check: length %lld, kept %lld at it %lld", ctx_length(c), c->cur, c->it);
}
#endif

/* ---------- best insertion of trail t: insert after node `after`.
   The best candidate is the smallest triple (value, cut, node), value = (delta + 64) * 65536 + noise bits.  The
   noise of a candidate is a hash of (iteration key, cut, node), not a draw from the thread's random stream, so the
   answer does not depend on the order in which the candidates are met (a GPU computes the same thing). */
/* wide: an cut offered by the tight index */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
    int wide;
} Ins;
#define VFIX(d) ((u64)((d) + 64) << 16)
#define NZAMP(noise) ((u64)((noise) * 65536.0 + 0.5))
/* 16 pseudo-random bits */
static inline u64 nz16(u64 itk, u64 o, u64 a) {
    u64 x = (itk ^ o) * 0x9E3779B97F4A7C15ULL;
    x ^= x >> 32;
    x = (x ^ a) * 0xD6E8FEB86659FD93ULL;
    x ^= x >> 32;
    x *= 0xD6E8FEB86659FD93ULL;
    return x >> 48;
}
/* Best place and cut for trail t in the current sequence.  Every cut of t is looked up in the index by the ends
   of its two words, so only places where it overlaps a neighbour are tried; if there is none the trail is appended.
   noise > 0 adds a random amount below noise to every candidate.  Returns the node to insert after, the cut and
   the change of length. */
static Ins best_insertion(Ctx *c, u32 t, double noise) {
    Ins best;
    best.val = 1e18;
    best.delta = 0;
    best.after = -1;
    best.opt = -1;
    best.wide = 0;
    u64 bfx = ~0ULL, amp = NZAMP(noise);
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    /* options are processed in batches so that the filter words of a whole batch are prefetched before they are tested */
    enum { BATCH = 16, NK = 2 * (KLEV + 1) };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 Sb[BATCH], Eb[BATCH], key[BATCH][NK], bit[BATCH][NK];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
            Sb[q] = S;
            Eb[q] = E;
            for (int j = 0; j <= KLEV; j++) {
                key[q][2 * j] = HKEY(S >> (4 * j), j, 0);
                key[q][2 * j + 1] = HKEY(E & HMASK[h - j], j, 1);
            }
            for (int k = 0; k < NK; k++) {
                bit[q][k] = BFH(key[q][k]) & c->bfmask;
                __builtin_prefetch(&c->bf[bit[q][k] >> 6]);
            }
        }
        for (int q = 0; q < m; q++) {
            i64 o = o0 + q;
            u64 S = Sb[q], E = Eb[q];
            int D = oD(o), skchecked = 0, skbad = 0;
            for (int k = 0; k < NK && !skbad; k++) {
                if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1))
                    continue;
                for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e]) {
                    int x = H->val[e], a, b2;
                    if (!nd[x].alive)
                        continue;
                    if (!(k & 1)) {
                        a = x;
                        b2 = nd[x].next;
                    } else {
                        b2 = x;
                        a = nd[x].prev;
                    }
                    if (a < 0 || b2 < 0)
                        continue;
                    if (!skchecked) {
                        skchecked = 1;
                        if (OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o))) {
                            skbad = 1;
                            break;
                        }
                    }
                    i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - jdist(&nd[a].v, &nd[b2].v);
                    u64 fx = VFIX(d) + (amp ? (nz16(c->nzit, (u64)o, (u64)a) * amp) >> 16 : 0);
                    if (fx < bfx || (fx == bfx && o == best.opt && a < best.after)) {
                        bfx = fx;
                        best.delta = d;
                        best.after = a;
                        best.opt = o;
                    }
                }
            }
        }
    }
    if (best.after >= 0)
        best.val = (double)bfx / 65536.0 - 64.0;
    else { /* nothing overlaps: append with the cheapest cut */
        i64 k = T->olo;
        for (i64 o = T->olo; o < T->ohi; o++)
            if (oD(o) < oD(k))
                k = o;
        best.delta = dist(nd[c->last].v.e, oS_t(T, k)) + oD(k);
        best.val = (double)best.delta;
        best.after = c->last;
        best.opt = k;
    }
    return best;
}

/* ---------- insertion of a small trail as two segments wrapped around a block i .. jm of the sequence:
   ..., prev(i), seg1, i, ..., jm, seg2, next(jm), ...   seg1 ends and seg2 starts at a vertex v of t (plain gap-3
   cut c2); seg1 starts and seg2 ends at any plain cut c1 */
typedef struct {
    int ok;
    i64 delta;
    int i, jm;
    i64 c1, c2;
} Split;
static int pair_cmp(const void *a, const void *b) {
    i64 x = ((const Pair *)a)->cst, y = ((const Pair *)b)->cst;
    return x < y ? -1 : x > y;
}
/* Best way to write small trail t as two segments around a block i .. jm of the sequence (see the comment
   above the type Split).  At most maxv of its free cuts are tried as the inner cut.  ok = 0: nothing found. */
static Split best_split(Ctx *c, u32 t, int maxv) {
    Split r;
    r.ok = 0;
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    int nv = 0;
    for (i64 o = T->olo; o < T->ohi; o++)
        if (OP[o].g == 3 && !OP[o].g1) {
            if (nv == c->vcap) {
                c->vcap = c->vcap ? c->vcap * 2 : 1024;
                c->vid = realloc(c->vid, c->vcap * sizeof(i64));
            }
            c->vid[nv++] = o;
        }
    if (nv > maxv) {
        for (int k = 0; k < maxv; k++) {
            int m = k + (int)rndn(c, nv - k);
            i64 x = c->vid[k];
            c->vid[k] = c->vid[m];
            c->vid[m] = x;
        }
        nv = maxv;
    }
    i64 np = 0;
    for (int a = 0; a < nv; a++) {
        i64 c2 = c->vid[a];
        u64 v = oS_t(T, c2);
        int ni = 0, nj = 0; /* I: inner nodes i with d(v, s_i) <= 1;  J: nodes jm (not the last) with d(e_jm, v) <= 1 */
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v & HMASK[h - lev], lev, 2)); q >= 0; q = H->next[q]) {
                int x = H->val[q];
                if (!nd[x].alive || nd[x].prev < 0 || nd[x].next < 0)
                    continue;
                if (ni == c->icap) {
                    c->icap = c->icap ? c->icap * 2 : 1024;
                    c->Ib = realloc(c->Ib, c->icap * sizeof(int));
                }
                c->Ib[ni++] = x;
            }
        if (!ni)
            continue;
        for (int lev = 0; lev <= 1; lev++)
            for (int q = h_get(H, HKEY(v >> (4 * lev), lev, 3)); q >= 0; q = H->next[q]) {
                int x = H->val[q];
                if (!nd[x].alive || nd[x].next < 0)
                    continue;
                if (nj == c->jcap) {
                    c->jcap = c->jcap ? c->jcap * 2 : 1024;
                    c->Jb = realloc(c->Jb, c->jcap * sizeof(int));
                }
                c->Jb[nj++] = x;
            }
        if (!nj)
            continue;
        for (int x = 0; x < ni; x++) {
            int i = c->Ib[x];
            int dvi = dist(v, nd[i].v.s);
            for (int y = 0; y < nj; y++) {
                int jm = c->Jb[y];
                if (nd[jm].lab < nd[i].lab)
                    continue;
                i64 cst = dvi + dist(nd[jm].v.e, v) - jdist(&nd[nd[i].prev].v, &nd[i].v) -
                          jdist(&nd[jm].v, &nd[nd[jm].next].v);
                if (np == c->pcap) {
                    c->pcap = c->pcap ? c->pcap * 2 : 4096;
                    c->pr = realloc(c->pr, c->pcap * sizeof(Pair));
                }
                c->pr[np].c2 = c2;
                c->pr[np].i = i;
                c->pr[np].jm = jm;
                c->pr[np].cst = cst;
                np++;
            }
        }
    }
    if (!np)
        return r;
    qsort(c->pr, (size_t)np, sizeof(Pair), pair_cmp);
    if (np > 64)
        np = 64;
    i64 bd = 1LL << 40, bk = -1, bc1 = -1;
    for (i64 k = 0; k < np; k++) {
        u64 ep = nd[nd[c->pr[k].i].prev].v.e, sn = nd[nd[c->pr[k].jm].next].v.s;
        for (i64 o = T->olo; o < T->ohi; o++) {
            i64 d = dist(ep, oS_t(T, o)) + oD(o) + dist(oE_t(T, o), sn) + c->pr[k].cst;
            if (d < bd) {
                bd = d;
                bk = k;
                bc1 = o;
            }
        }
    }
    if (bk < 0 || bc1 == c->pr[bk].c2 || OP[bc1].g1)
        return r;
    r.ok = 1;
    r.delta = bd;
    r.i = c->pr[bk].i;
    r.jm = c->pr[bk].jm;
    r.c1 = bc1;
    r.c2 = c->pr[bk].c2;
    return r;
}

/* ---------- related runs: the runs (not longer than runcap, other than the one that starts at node xs) whose end word
   is within one step of the start word S of an cut of the trails of nodes ids[0..m), or whose start word is within
   one step of an end word E.  The index of the sequence answers this at levels 0 and 1 (all nodes are alive here).
   rel receives the first nodes of these runs in sequence order. */
static int rel_cmp(const void *a, const void *b) {
    u64 x = ((const RelRun *)a)->lab, y = ((const RelRun *)b)->lab;
    return x < y ? -1 : x > y;
}
/* Node x has an end whose h-word fits.  If x is the last (side 0) or the first (side 1) piece of a run of at
   most runcap pieces, the first node of that run is put on the list c->rr, once per query.  The run that starts at
   xs is left out. */
/* side 0: e of x matches an S; 1: s of x matches an E */
static void rel_hit(Ctx *c, int x, int side, int xs, int runcap) {
    const Node *nd = c->nd;
    u32 it = (u32)c->it, *st = c->rst + 3 * (size_t)x;
    if (st[side] == it)
        return;
    st[side] = it;
    int s = x, len = 1;
    if (!side) {
        if (nd[x].next >= 0 && jdist(&nd[x].v, &nd[nd[x].next].v) < 2)
            return; /* not the end of a run */
        while (nd[s].prev >= 0 && jdist(&nd[nd[s].prev].v, &nd[s].v) < 2) {
            s = nd[s].prev;
            if (++len > runcap)
                return;
        }
    } else {
        if (nd[x].prev >= 0 && jdist(&nd[nd[x].prev].v, &nd[x].v) < 2)
            return; /* not the start of a run */
        for (int y = x; nd[y].next >= 0 && jdist(&nd[y].v, &nd[nd[y].next].v) < 2; y = nd[y].next)
            if (++len > runcap)
                return;
    }
    if (s == xs || c->rst[3 * (size_t)s + 2] == it)
        return;
    c->rst[3 * (size_t)s + 2] = it;
    if (c->nrr == c->rrcap) {
        c->rrcap = c->rrcap ? c->rrcap * 2 : 256;
        c->rr = realloc(c->rr, c->rrcap * sizeof(RelRun));
    }
    c->rr[c->nrr].lab = nd[s].lab;
    c->rr[c->nrr++].id = s;
}
/* Starts a query for related runs: empties the list and makes room for the stamps. */
static void rel_begin(Ctx *c) {
    if (c->rstcap < c->ncap) {
        free(c->rst);
        c->rst = calloc((size_t)c->ncap * 3, sizeof(u32));
        c->rstcap = c->ncap;
        if (!c->rst)
            DIE("out of memory");
    }
    c->nrr = 0;
}
/* Ends a query for related runs: the first nodes of the runs found, in sequence order.  Returns their number. */
static int rel_end(Ctx *c, int *rel) {
    if (c->nrr)
        qsort(c->rr, (size_t)c->nrr, sizeof(RelRun), rel_cmp);
    for (int q = 0; q < c->nrr; q++)
        rel[q] = c->rr[q].id;
    return c->nrr;
}
/* ---------- GPU (option --gpu): best_insertion of the big trails and the related-runs probe run on the card.
   The kernels (kern.cu) are compiled to PTX once (nvcc -arch=sm_120 -ptx -o kern.ptx kern.cu) and loaded through the
   CUDA driver library that comes with the display driver, so nothing has to be installed to build or run this.
   Shared by all threads: S, E, cost and flags of every cut (11 bytes per cut).
   Per search thread: a mirror of its nodes, hash table, index entries and Bloom filter.  The host notes which nodes,
   table slots and filter words it changes; before the next launch their current values travel in one command buffer
   together with the trails to place: one exchange per repair round.  The command buffer is host memory mapped into
   the address space of the card, so an exchange is three launches (patch, probe, fetch the answers) and one wait;
   where the driver cannot map host memory (or with --gpucopy) it is one upload, two launches and one read-back.
   The card returns the best (value, cut) of each trail; the node is found by evaluating that one cut on the
   host, which also proves at every call that the mirror still agrees with the host. */
#if defined(_WIN32)
#include <windows.h>
#define CUAPI __stdcall
static void *lib_open(void) {
    return LoadLibraryA("nvcuda.dll");
}
static void *lib_sym(void *l, const char *s) {
    return (void *)GetProcAddress((HMODULE)l, s);
}
#else
#include <dlfcn.h>
#define CUAPI
static void *lib_open(void) {
    return dlopen("libcuda.so.1", RTLD_NOW);
}
static void *lib_sym(void *l, const char *s) {
    return dlsym(l, s);
}
#endif
typedef u64 DP; /* CUdeviceptr */
static int(CUAPI *cuInit)(unsigned), (CUAPI * cuDeviceGet)(int *, int), (CUAPI * cuDeviceGetName)(char *, int, int),
    (CUAPI * cuCtxCreate)(void **, unsigned, int), (CUAPI * cuCtxSetCurrent)(void *);
static int(CUAPI *cuModuleLoadData)(void **, const void *),
    (CUAPI * cuModuleGetFunction)(void **, void *, const char *);
static int(CUAPI *cuMemAlloc)(DP *, size_t), (CUAPI * cuMemFree)(DP), (CUAPI * cuMemAllocHost)(void **, size_t),
    (CUAPI * cuMemsetD32)(DP, unsigned, size_t);
static int(CUAPI *cuMemcpyHtoD)(DP, const void *, size_t), (CUAPI * cuMemcpyDtoH)(void *, DP, size_t);
static int(CUAPI *cuMemcpyHtoDAsync)(DP, const void *, size_t, void *),
    (CUAPI * cuMemcpyDtoHAsync)(void *, DP, size_t, void *);
static int(CUAPI *cuLaunchKernel)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *,
                                  void **, void **);
static int(CUAPI *cuMemHostAlloc)(void **, size_t, unsigned),
    (CUAPI * cuMemHostGetDevicePointer)(DP *, void *, unsigned);
static int(CUAPI *cuStreamCreate)(void **, unsigned), (CUAPI * cuStreamSynchronize)(void *),
    (CUAPI * cuMemGetInfo)(size_t *, size_t *);
#define CK(x)                                                     \
    do {                                                          \
        int e_ = (x);                                             \
        if (e_)                                                   \
            DIE("CUDA driver error %d at line %d", e_, __LINE__); \
    } while (0)
/* as in kern.cu; a dead node has prev = next = -2 */
typedef struct {
    u64 s, e;
    int prev, next;
} GNode;
/* wide: bits 60.. of e say that the join of the node with its successor is tight (1: n - 2 letters, 2: n - 1); the card
   then takes -1 / -2 as the cost of that join instead of measuring it on h letters */
#define GFLAG(c, q) \
    ((q)->v.e | (wide && (q)->alive && (q)->next >= 0 ? (u64)wtight(WE(&(q)->v), WS(&(c)->nd[(q)->next].v)) << 60 : 0))
typedef struct {
    DP nd, tab, nx, vl, bf;
    u64 mask, bfmask;
    DP oS, oE, oSh, oEh, oF, stamp;
    int h, pad;
} GDev;
/* touched nodes / slots per upload, command words, answers */
enum { G_TN = 1 << 14, G_TS = 1 << 15, G_CMD = 1 << 19, G_OUT = 1 << 16, G_BLK = 256 };
struct GM {
    GDev d;
    void *stream;
    DP cmd, map;
    u64 *hc; /* command buffer on the card and (pinned) on the host */
    int ndcap;
    u64 tabn, bfw;
    i64 entcap, entsync;
    int full; /* sizes on the card; full: the mirror must be loaded */
    int *tn, ntn;
    unsigned char *dirty;
    u64 *ts, *tb;
    int nts, ntb, *te, nte; /* touched nodes, table slots, filter words, index entries */
    Ins *ins;
    char *has;
    int *lst; /* answers of a round, by position in pend */
    int *xhead, *xnext, nx, xcap;
    i64 *xo, *xr; /* skip cuts met so far, by trail: cut and skipped rank */
    u32 gen;
    double t_build, t_up, t_kern, t_down, t_post, t_full, t_all;
    i64 nround, nprobe, nrelt, nopen, nretry, nfull, nsync, ncpu, nans;
};
static int use_gpu = 0, gpu_prof = 0, gpu_check = 0;
static i64 gpu_min = 3000;
static const char *ptx_path = NULL;
static int gpu_map = 1;
static void *g_cu, *g_fpatch, *g_fprobe, *g_frelt, *g_fcopy;
static DP g_oS, g_oE, g_oSh, g_oEh, g_oF;
static double g_devmb;

/* returns 1 if the card is ready; 0 (with the reason) if the search has to stay on the host */
static int gpu_init(const char *argv0, int LT) {
    double t0 = wall();
    void *lib = lib_open();
    if (!lib) {
        printf("gpu: the CUDA driver library was not found; searching on the CPU\n");
        return 0;
    }
    const char *miss = NULL;
#define SYM(v, name)                       \
    do {                                   \
        *(void **)&v = lib_sym(lib, name); \
        if (!v)                            \
            miss = name;                   \
    } while (0)
    SYM(cuInit, "cuInit");
    SYM(cuDeviceGet, "cuDeviceGet");
    SYM(cuDeviceGetName, "cuDeviceGetName");
    SYM(cuCtxCreate, "cuCtxCreate_v2");
    SYM(cuCtxSetCurrent, "cuCtxSetCurrent");
    SYM(cuModuleLoadData, "cuModuleLoadData");
    SYM(cuModuleGetFunction, "cuModuleGetFunction");
    SYM(cuMemAlloc, "cuMemAlloc_v2");
    SYM(cuMemFree, "cuMemFree_v2");
    SYM(cuMemAllocHost, "cuMemAllocHost_v2");
    SYM(cuMemsetD32, "cuMemsetD32_v2");
    SYM(cuMemcpyHtoD, "cuMemcpyHtoD_v2");
    SYM(cuMemcpyDtoH, "cuMemcpyDtoH_v2");
    SYM(cuMemcpyHtoDAsync, "cuMemcpyHtoDAsync_v2");
    SYM(cuMemcpyDtoHAsync, "cuMemcpyDtoHAsync_v2");
    SYM(cuLaunchKernel, "cuLaunchKernel");
    *(void **)&cuMemHostAlloc = lib_sym(lib, "cuMemHostAlloc");
    *(void **)&cuMemHostGetDevicePointer = lib_sym(lib, "cuMemHostGetDevicePointer_v2");
    SYM(cuStreamCreate, "cuStreamCreate");
    SYM(cuStreamSynchronize, "cuStreamSynchronize");
    SYM(cuMemGetInfo, "cuMemGetInfo_v2");
#undef SYM
    if (miss) {
        printf("gpu: %s is missing in the CUDA driver library; searching on the CPU\n", miss);
        return 0;
    }
    /* the PTX file: --ptx FILE, or kern.ptx next to the program, or in the current directory */
    char path[4096];
    FILE *pf = NULL;
    if (ptx_path)
        pf = fopen(ptx_path, "rb");
    else {
        const char *sl = strrchr(argv0, '/'), *bs = strrchr(argv0, '\\');
        if (bs > sl)
            sl = bs;
        if (sl) {
            snprintf(path, sizeof path, "%.*s/kern.ptx", (int)(sl - argv0), argv0);
            pf = fopen(path, "rb");
        }
        if (!pf)
            pf = fopen("kern.ptx", "rb");
    }
    if (!pf) {
        printf("gpu: the kernel file %s was not found; searching on the CPU\n", ptx_path ? ptx_path : "kern.ptx");
        return 0;
    }
    fseek(pf, 0, SEEK_END);
    long psz = ftell(pf);
    fseek(pf, 0, SEEK_SET);
    char *ptx = calloc((size_t)psz + 1, 1);
    if (fread(ptx, 1, (size_t)psz, pf) != (size_t)psz) {
        fclose(pf);
        printf("gpu: cannot read the kernel file; searching on the CPU\n");
        return 0;
    }
    fclose(pf);
    int dev, e;
    void *mod;
    char name[128] = "";
    if ((e = cuInit(0)) || (e = cuDeviceGet(&dev, 0)) || (e = cuDeviceGetName(name, sizeof name, dev)) ||
        (e = cuCtxCreate(&g_cu, 0, dev))) {
        printf("gpu: no usable CUDA device (driver error %d); searching on the CPU\n", e);
        return 0;
    }
    void *fw;
    if (!(e = cuModuleLoadData(&mod, ptx)) && wide && cuModuleGetFunction(&fw, mod, "ts_wide")) {
        printf("gpu: this kernel file does not know the wide model (build kern_wide.cu); searching on the CPU\n");
        return 0;
    }
    if (e || (e = cuModuleGetFunction(&g_fpatch, mod, "ts_patch")) ||
        (e = cuModuleGetFunction(&g_fprobe, mod, "ts_probe")) || (e = cuModuleGetFunction(&g_frelt, mod, "ts_relt")) ||
        (e = cuModuleGetFunction(&g_fcopy, mod, "ts_copy"))) {
        printf("gpu: the kernel file was not accepted by the driver (error %d); searching on the CPU\n", e);
        return 0;
    }
    free(ptx);
    double t1 = wall();
    /* cuts, in pieces: low 32 bits of S and E, the 8 bits above them, and cost + 3 with bit 7 set for a skip cut */
    size_t fr0, fr1, tot;
    CK(cuMemGetInfo(&fr0, &tot));
    size_t need = (size_t)NO * 11;
    if (need + (1ULL << 30) > fr0) {
        printf("gpu: %.1f GB needed for the openings, %.1f GB free on the card; searching on the CPU\n", need / 1e9,
               fr0 / 1e9);
        return 0;
    }
    CK(cuMemAlloc(&g_oS, (size_t)NO * 4 + 16));
    CK(cuMemAlloc(&g_oE, (size_t)NO * 4 + 16));
    CK(cuMemAlloc(&g_oF, (size_t)NO + 16));
    CK(cuMemAlloc(&g_oSh, (size_t)NO + 16));
    CK(cuMemAlloc(&g_oEh, (size_t)NO + 16));
    i64 CH = 1 << 22;
    u32 *bs = malloc(CH * 4), *be = malloc(CH * 4);
    unsigned char *bsh = malloc(CH), *beh = malloc(CH), *bf = malloc(CH);
    if (!bs || !be || !bsh || !beh || !bf)
        DIE("out of memory");
    for (i64 o0 = 0; o0 < NO; o0 += CH) {
        i64 m = NO - o0 < CH ? NO - o0 : CH;
#pragma omp parallel num_threads(LT)
        {
            i64 t = -1;
#pragma omp for schedule(static)
            for (i64 q = 0; q < m; q++) {
                i64 o = o0 + q;
                if (t < 0)
                    t = otrail(o);
                while (o >= TR[t].ohi)
                    t++;
                u64 S = oS_t(&TR[t], o), E = oE_t(&TR[t], o);
                bs[q] = (u32)S;
                be[q] = (u32)E;
                bsh[q] = (unsigned char)(S >> 32);
                beh[q] = (unsigned char)(E >> 32);
                bf[q] = (unsigned char)((oD(o) + 3) | (OP[o].g1 ? 0x80 : 0));
            }
        }
        CK(cuMemcpyHtoD(g_oS + 4 * (u64)o0, bs, (size_t)m * 4));
        CK(cuMemcpyHtoD(g_oE + 4 * (u64)o0, be, (size_t)m * 4));
        CK(cuMemcpyHtoD(g_oF + (u64)o0, bf, (size_t)m));
        CK(cuMemcpyHtoD(g_oSh + (u64)o0, bsh, (size_t)m));
        CK(cuMemcpyHtoD(g_oEh + (u64)o0, beh, (size_t)m));
    }
    free(bs);
    free(be);
    free(bsh);
    free(beh);
    free(bf);
    CK(cuMemGetInfo(&fr1, &tot));
    g_devmb = (fr0 - fr1) / 1e6;
    printf(
        "gpu: %s; driver and kernels ready in %.2fs, %lld openings loaded in %.2fs (%.0f MB on the card, %.1f of %.1f GB free); trails with more than %lld openings go to the card\n",
        name, t1 - t0, NO, wall() - t1, g_devmb, fr1 / 1e9, tot / 1e9, gpu_min);
    fflush(stdout);
    return 1;
}
/* Gives a search thread its share of the card: a stream, a command buffer (host memory mapped into the card
   where the driver allows it) and the mirror of its nodes, index and filter. */
static void gm_attach(Ctx *c) {
    GM *g = calloc(1, sizeof(GM));
    if (!g)
        DIE("out of memory");
#pragma omp critical(gpu)
    {
        CK(cuCtxSetCurrent(g_cu));
        CK(cuStreamCreate(&g->stream, 0));
        CK(cuMemAlloc(&g->cmd, (size_t)G_CMD * 8));
        void *p = NULL;
        /* the command buffer of the host, mapped into the address space of the card if the driver can do that: the
           kernels then fetch the commands and deliver the answers themselves, and no copy call is needed */
        if (gpu_map && cuMemHostAlloc && cuMemHostGetDevicePointer && !cuMemHostAlloc(&p, (size_t)G_CMD * 8, 2) &&
            cuMemHostGetDevicePointer(&g->map, p, 0))
            g->map = 0;
        if (!g->map)
            CK(cuMemAllocHost(&p, (size_t)G_CMD * 8));
        g->hc = p;
    }
    g->tn = malloc(G_TN * sizeof(int));
    g->ts = malloc(G_TS * 8);
    g->tb = malloc(G_TS * 8);
    g->te = malloc(G_TS * sizeof(int));
    g->ins = malloc(((size_t)NT + 1) * sizeof(Ins));
    g->has = calloc((size_t)NT + 1, 1);
    g->lst = malloc(((size_t)NT + 1) * sizeof(int));
    g->xhead = malloc(((size_t)NT + 1) * sizeof(int));
    for (i64 t = 0; t <= NT; t++)
        g->xhead[t] = -1;
    g->d.oS = g_oS;
    g->d.oE = g_oE;
    g->d.oSh = g_oSh;
    g->d.oEh = g_oEh;
    g->d.oF = g_oF;
    g->d.h = h;
    g->full = 1;
    c->G = g;
}
/* the whole mirror: after ctx_load */
static void gm_full(Ctx *c) {
    GM *g = c->G;
    double t0 = wall();
    const HTab *H = &c->H;
    if (c->ncap != g->ndcap) {
        if (g->d.nd) {
            CK(cuMemFree(g->d.nd));
            CK(cuMemFree(g->d.stamp));
        }
        CK(cuMemAlloc(&g->d.nd, (size_t)c->ncap * sizeof(GNode)));
        CK(cuMemAlloc(&g->d.stamp, (size_t)c->ncap * 8));
        CK(cuMemsetD32(g->d.stamp, 0, (size_t)c->ncap * 2));
        g->ndcap = c->ncap;
        g->gen = 0;
        free(g->dirty);
        g->dirty = malloc((size_t)c->ncap);
    }
    if (H->mask + 1 != g->tabn) {
        if (g->d.tab)
            CK(cuMemFree(g->d.tab));
        CK(cuMemAlloc(&g->d.tab, (size_t)(H->mask + 1) * sizeof(Slot)));
        g->tabn = H->mask + 1;
    }
    if (H->cap != g->entcap) {
        if (g->d.nx) {
            CK(cuMemFree(g->d.nx));
            CK(cuMemFree(g->d.vl));
        }
        CK(cuMemAlloc(&g->d.nx, (size_t)H->cap * 4));
        CK(cuMemAlloc(&g->d.vl, (size_t)H->cap * 4));
        g->entcap = H->cap;
    }
    if ((c->bfmask + 1) / 64 != g->bfw) {
        if (g->d.bf)
            CK(cuMemFree(g->d.bf));
        CK(cuMemAlloc(&g->d.bf, (size_t)(c->bfmask + 1) / 8));
        g->bfw = (c->bfmask + 1) / 64;
    }
    GNode *b = malloc((size_t)c->nn * sizeof(GNode));
    if (!b)
        DIE("out of memory");
    for (int i = 0; i < c->nn; i++) {
        const Node *q = &c->nd[i];
        b[i].s = q->v.s;
        b[i].e = GFLAG(c, q);
        b[i].prev = q->alive ? q->prev : -2;
        b[i].next = q->alive ? q->next : -2;
    }
    CK(cuMemcpyHtoD(g->d.nd, b, (size_t)c->nn * sizeof(GNode)));
    free(b);
    CK(cuMemcpyHtoD(g->d.tab, H->t, (size_t)(H->mask + 1) * sizeof(Slot)));
    CK(cuMemcpyHtoD(g->d.nx, H->next, (size_t)H->n * 4));
    CK(cuMemcpyHtoD(g->d.vl, H->val, (size_t)H->n * 4));
    CK(cuMemcpyHtoD(g->d.bf, c->bf, (size_t)(c->bfmask + 1) / 8));
    g->d.mask = H->mask;
    g->d.bfmask = c->bfmask;
    g->entsync = H->n;
    g->ntn = g->nts = g->ntb = g->nte = 0;
    memset(g->dirty, 0, (size_t)c->ncap);
    g->full = 0;
    g->nfull++;
    g->t_full += wall() - t0;
}
/* writes the patch records to the command buffer; returns the number of words and the argument block of ts_patch */
static i64 gm_patches(Ctx *c, int *pa) {
    GM *g = c->G;
    const HTab *H = &c->H;
    u64 *w = g->hc;
    i64 m = 0;
    for (int q = 0; q < g->ntn; q++) {
        int id = g->tn[q];
        const Node *x = &c->nd[id];
        g->dirty[id] = 0;
        w[m++] = (u64)id;
        w[m++] = x->v.s;
        w[m++] = GFLAG(c, x);
        w[m++] = x->alive ? (u64)(u32)x->prev | (u64)(u32)x->next << 32 : (u64)(u32)-2 | (u64)(u32)-2 << 32;
    }
    for (int q = 0; q < g->nts; q++) {
        u64 i = g->ts[q];
        w[m++] = i;
        w[m++] = H->t[i].key;
        w[m++] = (u64)(u32)H->t[i].head;
    }
    int nent = (int)(H->n - g->entsync);
    for (int q = 0; q < nent; q++)
        w[m++] = (u64)(u32)H->next[g->entsync + q] | (u64)(u32)H->val[g->entsync + q] << 32;
    for (int q = 0; q < g->ntb; q++) {
        w[m++] = g->tb[q];
        w[m++] = c->bf[g->tb[q]];
    }
    for (int q = 0; q < g->nte; q++) {
        int e = g->te[q];
        w[m++] = (u64)e;
        w[m++] = (u64)(u32)H->next[e] | (u64)(u32)H->val[e] << 32;
    }
    pa[0] = g->ntn;
    pa[1] = g->nts;
    pa[2] = nent;
    pa[3] = g->ntb;
    pa[4] = (int)g->entsync;
    pa[5] = g->nte;
    g->entsync = H->n;
    g->ntn = g->nts = g->ntb = g->nte = 0;
    return m;
}
/* one exchange with the card: upload `up` command words, apply the patches, run kernel fn over nthr GPU threads,
   read `dn` words back from word `at` */
static void gm_exchange(Ctx *c, i64 up, const int *pa, void *fn, void **args, i64 nthr, i64 at, i64 dn) {
    GM *g = c->G;
    double t0 = wall(), t1, t2;
    int np = pa[0] + pa[1] + pa[2] + pa[3] + pa[5];
    DP pc = g->cmd;
    int a0 = pa[0], a1 = pa[1], a2 = pa[2], a3 = pa[3], a4 = pa[4], a5 = pa[5];
    i64 pw = 4 * (i64)a0 + 3 * (i64)a1 + a2 + 2 * (i64)a3 + 2 * (i64)a5;
    int nc = 0;
    DP dst = g->cmd + 8 * (u64)pw; /* pw: words of the patch records */
    void *parg[10] = {&g->d, &pc, &a0, &a1, &a2, &a3, &a4, &a5, &dst, &nc};
    if (g->map) { /* ts_patch reads the mapped buffer and copies the rest of the command to the card; ts_copy brings the answers */
        pc = g->map;
        nc = (int)(up - pw);
        DP rs = g->cmd + 8 * (u64)at, rd = g->map + 8 * (u64)at;
        int rn = (int)dn;
        void *carg[3] = {&rd, &rs, &rn};
        if (np + nc)
            CK(cuLaunchKernel(g_fpatch, (unsigned)((np + nc + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream,
                              parg, NULL));
        if (fn)
            CK(cuLaunchKernel(fn, (unsigned)((nthr + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, args, NULL));
        if (dn)
            CK(cuLaunchKernel(g_fcopy, (unsigned)((dn + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, carg,
                              NULL));
        CK(cuStreamSynchronize(g->stream));
        g->t_kern += wall() - t0;
    } else if (gpu_prof) {
        CK(cuMemcpyHtoD(g->cmd, g->hc, (size_t)up * 8));
        t1 = wall();
        if (np)
            CK(cuLaunchKernel(g_fpatch, (unsigned)((np + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, parg,
                              NULL));
        if (fn)
            CK(cuLaunchKernel(fn, (unsigned)((nthr + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, args, NULL));
        CK(cuStreamSynchronize(g->stream));
        t2 = wall();
        if (dn)
            CK(cuMemcpyDtoH(g->hc + at, g->cmd + 8 * (u64)at, (size_t)dn * 8));
        g->t_up += t1 - t0;
        g->t_kern += t2 - t1;
        g->t_down += wall() - t2;
    } else {
        CK(cuMemcpyHtoDAsync(g->cmd, g->hc, (size_t)up * 8, g->stream));
        if (np)
            CK(cuLaunchKernel(g_fpatch, (unsigned)((np + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, parg,
                              NULL));
        if (fn)
            CK(cuLaunchKernel(fn, (unsigned)((nthr + G_BLK - 1) / G_BLK), 1, 1, G_BLK, 1, 1, 0, g->stream, args, NULL));
        if (dn)
            CK(cuMemcpyDtoHAsync(g->hc + at, g->cmd + 8 * (u64)at, (size_t)dn * 8, g->stream));
        CK(cuStreamSynchronize(g->stream));
        g->t_kern += wall() - t0;
    }
}
/* too many changes noted and no launch in sight: send them */
static void gm_sync(Ctx *c) {
    int pa[6];
    double t0 = wall();
    i64 m = gm_patches(c, pa);
    c->G->t_build += wall() - t0;
    gm_exchange(c, m, pa, NULL, NULL, 0, 0, 0);
    c->G->nsync++;
}
static inline void gm_touch(Ctx *c, int id) {
    GM *g = c->G;
    if (id >= 0 && !g->dirty[id]) {
        g->dirty[id] = 1;
        g->tn[g->ntn++] = id;
    }
}
/* hooks of node_unlink and node_relink / node_insert_after / ctx_load */
static void gm_link(Ctx *c, int id) {
    GM *g = c->G;
    if (g->full)
        return;
    gm_touch(c, id);
    gm_touch(c, c->nd[id].prev);
    gm_touch(c, c->nd[id].next);
    if (g->ntn > G_TN - 8)
        gm_sync(c);
}
/* Hook: node id was inserted on the host.  Notes the node, its two neighbours and the index slots it changed,
   so that the mirror on the card gets them with the next command. */
static void gm_ins(Ctx *c, int id) {
    GM *g = c->G;
    if (g->full)
        return;
    const Ev *x = &c->nd[id].v;
    const HTab *H = &c->H;
    gm_touch(c, id);
    gm_touch(c, c->nd[id].prev);
    gm_touch(c, c->nd[id].next);
    /* the keys of index_add: all of them, also those the kernels never look up, because a slot that is taken on the
       host and empty on the card would end a probe too early */
    u64 k[2 * (KLEV + 1) + 4];
    int nk = 0;
    for (int j = 0; j <= KLEV; j++) {
        k[nk++] = HKEY(x->e & HMASK[h - j], j, 0);
        k[nk++] = HKEY(x->s >> (4 * j), j, 1);
    }
    for (int z = 0; z < nk; z++)
        g->tb[g->ntb++] = (BFH(k[z]) & c->bfmask) >> 6;
    if (use_split) {
        k[nk++] = HKEY(x->s, 0, 2);
        k[nk++] = HKEY(x->s >> 4, 1, 2);
        k[nk++] = HKEY(x->e, 0, 3);
        k[nk++] = HKEY(x->e & HMASK[h - 1], 1, 3);
    }
    for (int z = 0; z < nk; z++) {
        u64 i = hmix(k[z]) & H->mask;
        while (H->t[i].key != k[z])
            i = (i + 1) & H->mask;
        g->ts[g->nts++] = i;
    }
    if (g->nts > G_TS - 16 || g->ntn > G_TN - 8)
        gm_sync(c);
}
static void gm_reset(Ctx *c) {
    c->G->full = 1;
}
/* hook of index_del: the head of slot i (p < 0) or the link of entry p has changed */
static void gm_del(Ctx *c, u64 i, int p) {
    GM *g = c->G;
    if (g->full)
        return;
    if (p < 0)
        g->ts[g->nts++] = i;
    else
        g->te[g->nte++] = p;
    if (g->nts > G_TS - 16 || g->nte > G_TS - 16)
        gm_sync(c);
}
/* candidates of one cut: the best (value, node) */
static int ins_one(const Ctx *c, const Trail *T, i64 o, u64 amp, u64 *bfx, i64 *bd) {
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    u64 S = oS_t(T, o), E = oE_t(T, o);
    int D = oD(o), ba = -1;
    *bfx = ~0ULL;
    for (int k = 0; k < 2 * (KLEV + 1); k++) {
        int j = k >> 1;
        u64 key = (k & 1) ? HKEY(E & HMASK[h - j], j, 1) : HKEY(S >> (4 * j), j, 0);
        if (!bf_has(c, key))
            continue;
        for (int e = h_get(H, key); e >= 0; e = H->next[e]) {
            int x = H->val[e], a, b2;
            if (!nd[x].alive)
                continue;
            if (!(k & 1)) {
                a = x;
                b2 = nd[x].next;
            } else {
                b2 = x;
                a = nd[x].prev;
            }
            if (a < 0 || b2 < 0)
                continue;
            i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - jdist(&nd[a].v, &nd[b2].v);
            u64 fx = VFIX(d) + (amp ? (nz16(c->nzit, (u64)o, (u64)a) * amp) >> 16 : 0);
            if (fx < *bfx || (fx == *bfx && a < ba)) {
                *bfx = fx;
                *bd = d;
                ba = a;
            }
        }
    }
    return ba;
}
/* best_insertion of the big trails among pend[0 .. np): the answers go to G->ins[q], G->has[q] says which are there */
static void gm_round(Ctx *c, const u32 *pend, i64 np, double noise) {
    GM *g = c->G;
    int nl = 0;
    double t0 = wall(), t1;
    for (i64 q = 0; q < np; q++) {
        g->has[q] = 0;
        if (TR[pend[q]].ohi - TR[pend[q]].olo > gpu_min)
            g->lst[nl++] = (int)q;
    }
    if (!nl)
        return;
    if (g->full)
        gm_full(c);
    u64 amp = NZAMP(noise), itk = c->nzit;
    for (int pass = 0; nl > 0; pass++) {
        t1 = wall();
        int pa[6];
        i64 m0 = gm_patches(c, pa), tot = 0, xo = 4 * (i64)nl + 1;
        u64 *w = g->hc + m0;
        for (int z = 0; z < nl; z++) {
            u32 t = pend[g->lst[z]];
            i64 x0 = xo;
            if (c->nskp)
                for (int e = g->xhead[t]; e >= 0; e = g->xnext[e])
                    if (skp_has(c, g->xr[e]))
                        w[xo++] = (u64)g->xo[e];
            w[z] = (u64)tot;
            w[nl + 1 + z] = (u64)TR[t].olo;
            w[2 * nl + 1 + z] = (u64)x0 | (u64)(xo - x0) << 32;
            w[3 * nl + 1 + z] = ~0ULL;
            tot += TR[t].ohi - TR[t].olo;
            if (m0 + xo > G_CMD - 64)
                DIE("gpu: command buffer too small");
        }
        w[nl] = (u64)tot;
        DP pc = g->cmd + 8 * (u64)m0;
        int ntr = nl;
        void *args[5] = {&g->d, &pc, &ntr, &itk, &amp};
        g->t_build += wall() - t1;
        gm_exchange(c, m0 + xo, pa, g_fprobe, args, tot, m0 + 3 * nl + 1, nl);
        g->nprobe++;
        g->nopen += tot;
        if (pass)
            g->nretry++;
        t1 = wall();
        int nl2 = 0;
        for (int z = 0; z < nl; z++) {
            int q = g->lst[z];
            u32 t = pend[q];
            const Trail *T = &TR[t];
            u64 r = w[3 * nl + 1 + z];
            if (r == ~0ULL) {
                g->ncpu++;
                continue;
            } /* no candidate at all: left to the host */
            i64 o = T->olo + (i64)(r & 0xFFFFFFFFFFULL);
            if (OP[o].g1 && c->nskp) {
                i64 rk = oSK_t(T, o);
                if (skp_has(c, rk)) { /* its window is skipped elsewhere already: remember the cut and ask again */
                    if (g->nx == g->xcap) {
                        g->xcap = g->xcap ? g->xcap * 2 : 256;
                        g->xnext = realloc(g->xnext, g->xcap * sizeof(int));
                        g->xo = realloc(g->xo, g->xcap * 8);
                        g->xr = realloc(g->xr, g->xcap * 8);
                    }
                    g->xo[g->nx] = o;
                    g->xr[g->nx] = rk;
                    g->xnext[g->nx] = g->xhead[t];
                    g->xhead[t] = g->nx++;
                    g->lst[nl2++] = q;
                    continue;
                }
            }
            Ins bi;
            u64 fx;
            bi.opt = o;
            bi.wide = 0;
            bi.after = ins_one(c, T, o, amp, &fx, &bi.delta);
            if (bi.after < 0 || fx != r >> 40)
                DIE("gpu: the card and the host disagree (trail %u opening %lld: %llx / %llx)", t, o,
                    (unsigned long long)(r >> 40), (unsigned long long)fx);
            bi.val = (double)fx / 65536.0 - 64.0;
            g->ins[q] = bi;
            g->has[q] = 1;
            if (gpu_check) {
                Ins ref = best_insertion(c, t, noise); /* --gpucheck: the whole answer against the host */
                if (ref.opt != bi.opt || ref.after != bi.after || ref.val != bi.val || ref.delta != bi.delta)
                    DIE("gpu check: trail %u at iteration %lld: card (%lld, %d, %.6f), host (%lld, %d, %.6f)", t, c->it,
                        bi.opt, bi.after, bi.val, ref.opt, ref.after, ref.val);
            }
        }
        nl = nl2;
        g->t_post += wall() - t1;
    }
    g->nround++;
    g->t_all += wall() - t0;
}
/* related runs of the trails of nodes ids[0 .. m) (see rel_runs); returns -1 if the card gave too many answers */
static int gm_relt(Ctx *c, const int *ids, int m, int runcap, int *rel) {
    GM *g = c->G;
    double t0 = wall(), t1;
    if (g->full)
        gm_full(c);
    t1 = wall();
    int pa[6];
    i64 m0 = gm_patches(c, pa), tot = 0;
    u64 *w = g->hc + m0;
    if (m0 + 2 * (i64)m + 2 + G_OUT / 2 > G_CMD - 64)
        DIE("gpu: command buffer too small");
    for (int z = 0; z < m; z++) {
        const Trail *T = &TR[c->nd[ids[z]].v.t];
        w[z] = (u64)tot;
        w[m + 1 + z] = (u64)T->olo;
        tot += T->ohi - T->olo;
    }
    w[m] = (u64)tot;
    w[2 * m + 1] = 0;
    if (++g->gen == 0) {
        CK(cuMemsetD32(g->d.stamp, 0, (size_t)g->ndcap * 2));
        g->gen = 1;
    }
    DP pc = g->cmd + 8 * (u64)m0;
    int ntr = m, cap = G_OUT;
    u32 gen = g->gen;
    void *args[5] = {&g->d, &pc, &ntr, &gen, &cap};
    enum { FIRST = 1024 }; /* answers fetched with the count */
    g->t_build += wall() - t1;
    gm_exchange(c, m0 + 2 * (i64)m + 2, pa, g_frelt, args, tot, m0 + 2 * m + 1, 1 + FIRST / 2);
    const int *out = (const int *)(w + 2 * m + 1);
    int cnt = out[0];
    out += 2;
    g->nrelt++;
    g->nopen += tot;
    g->nans += cnt;
    if (cnt > G_OUT) {
        g->t_all += wall() - t0;
        return -1;
    }
    if (cnt > FIRST) {
        t1 = wall();
        CK(cuMemcpyDtoH(w + 2 * m + 2 + FIRST / 2, pc + 8 * (u64)(2 * m + 2 + FIRST / 2),
                        (size_t)(cnt - FIRST + 1) / 2 * 8));
        g->t_down += wall() - t1;
    }
    t1 = wall();
    rel_begin(c);
    for (int q = 0; q < cnt; q++)
        rel_hit(c, out[q] >> 1, out[q] & 1, ids[0], runcap);
    int nrel = rel_end(c, rel);
    g->t_post += wall() - t1;
    g->t_all += wall() - t0;
    return nrel;
}
/* Prints what a thread did on the card, at the end of the search. */
static void gm_report(const Ctx *c, double tsearch) {
    const GM *g = c->G;
    double it = (double)(c->it ? c->it : 1), k = 1e3 / it;
#pragma omp critical(gbest)
    {
        printf(
            "gpu thread %d: %.1f iterations/s; %lld rounds, %lld probe launches (%lld repeated for a skip opening), %lld related-runs launches (%.0f answers each), %.1f M openings; %lld mirror loads, %lld extra uploads, %lld trails left to the CPU\n",
            c->tid, c->it / tsearch, g->nround, g->nprobe, g->nretry, g->nrelt,
            (double)g->nans / (g->nrelt ? g->nrelt : 1), g->nopen / 1e6, g->nfull, g->nsync, g->ncpu);
        if (gpu_prof)
            printf(
                "gpu thread %d: ms per iteration: total %.3f = command buffer %.3f + upload %.3f + kernels %.3f + read-back %.3f + check on the host %.3f + mirror loads %.3f + everything else on the CPU %.3f\n",
                c->tid, tsearch * k, g->t_build * k, g->t_up * k, g->t_kern * k, g->t_down * k, g->t_post * k,
                g->t_full * k, (tsearch - g->t_build - g->t_up - g->t_kern - g->t_down - g->t_post - g->t_full) * k);
        else
            printf(
                "gpu thread %d: ms per iteration: total %.3f = command buffer %.3f + exchanges with the card %.3f + check on the host %.3f + mirror loads %.3f + everything else on the CPU %.3f\n",
                c->tid, tsearch * k, g->t_build * k, g->t_kern * k, g->t_post * k, g->t_full * k,
                (tsearch - g->t_build - g->t_kern - g->t_post - g->t_full) * k);
        fflush(stdout);
    }
}

/* The runs related to the trails of the nodes ids[0 .. m-1] (see the comment above): on the card if these
   trails have more than gpu_min cuts, else on the host.  Writes the runs to rel and returns their number. */
static int rel_runs(Ctx *c, const int *ids, int m, int runcap, int *rel) {
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    enum { BATCH = 16 };
    if (c->G) {
        GM *g_ = c->G;
        i64 no = 0;
        for (int i = 0; i < m; i++)
            no += TR[nd[ids[i]].v.t].ohi - TR[nd[ids[i]].v.t].olo;
        if (no > gpu_min) {
            int r = gm_relt(c, ids, m, runcap, rel);
            if (r >= 0 && !gpu_check)
                return r;
            if (r >= 0) { /* --gpucheck: the same question to the host */
                int *g1 = malloc((size_t)(r + 1) * sizeof(int));
                memcpy(g1, rel, (size_t)r * sizeof(int));
                c->G = NULL;
                memset(c->rst, 0, (size_t)c->rstcap * 3 * sizeof(u32));
                int r2 = rel_runs(c, ids, m, runcap, rel);
                c->G = g_;
                if (r2 != r || memcmp(g1, rel, (size_t)r * sizeof(int)))
                    DIE("gpu check: related runs differ at iteration %lld (%d / %d)", c->it, r, r2);
                free(g1);
                return r;
            }
        }
    }
    rel_begin(c);
    for (int i = 0; i < m; i++) {
        const Trail *T = &TR[nd[ids[i]].v.t];
        for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
            int nb = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
            u64 key[BATCH][4], bit[BATCH][4];
            for (int q = 0; q < nb; q++) {
                u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
                key[q][0] = HKEY(S, 0, 0);
                key[q][1] = HKEY(E, 0, 1);
                key[q][2] = HKEY(S >> 4, 1, 0);
                key[q][3] = HKEY(E & HMASK[h - 1], 1, 1);
                for (int k = 0; k < 4; k++) {
                    bit[q][k] = BFH(key[q][k]) & c->bfmask;
                    __builtin_prefetch(&c->bf[bit[q][k] >> 6]);
                }
            }
            for (int q = 0; q < nb; q++)
                for (int k = 0; k < 4; k++) {
                    if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1))
                        continue;
                    for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e])
                        if (nd[H->val[e]].alive)
                            rel_hit(c, H->val[e], k & 1, ids[0], runcap);
                }
        }
    }
    return rel_end(c, rel);
}

/* ---------- what the sequence looks like: cuts by kind, joins by cost, runs (maximal chains of joins of cost <= 1) */
static void print_stats(const Ev *ev, i64 N) {
    i64 g2 = 0, g1 = 0, skips = 0, segs = 0, pieces = 0, hist[19] = {0}, runs = 1, inter = 0, inrun = 0, extra = 0;
    for (i64 i = 0; i < N; i++) {
        if (wide && is_g1(&ev[i]))
            g1++; /* a whole trail from a gap-1 cut is not counted as a segment */
        else if (ev[i].kind == EV_SEG)
            segs++;
        else if (ev[i].kind == EV_PIECE)
            pieces++;
        else {
            int g = OP[ev[i].a].g;
            if (OP[ev[i].a].g1)
                skips++;
            else if (g == 2)
                g2++;
            else if (g == 1)
                g1++;
        }
        if (i + 1 < N) {
            int d = jdist(&ev[i], &ev[i + 1]);
            hist[d + 2]++;
            if (d >= 2) {
                runs++;
                inter += d;
            } else
                inrun += d;
        }
    }
    i64 sumR = 0;
    for (i64 t = 0; t < NT; t++)
        sumR += TR[t].R;
    extra = seq_length(ev, N) - h - sumR - inter - inrun;
    printf(
        "stats: events %lld (unchanged pieces %lld, segments %lld), gap-2 openings %lld, gap-1 openings %lld, duplicate-skip openings %lld, opening cost %lld" NL,
        N, pieces, segs, g2, g1, skips, extra);
    printf("stats: runs %lld, join cost between runs %lld, joins inside runs cost %lld; joins by cost:", runs, inter,
           inrun);
    for (int d = -2; d <= h; d++)
        if (hist[d + 2])
            printf(" %d:%lld", d, hist[d + 2]);
    printf(NL);
    fflush(stdout);
}

/* ==================== own part: the fixed-order pass in both models (cw_run) ==================== */
/* ---------- cluster optimisation (co_run of recut.c, here for the whole sequence and for
   both models): for a fixed order of the events, the best cuts of all trails at once.
   Shortest path through layers, one per event: cost[p] = D(p) + min over the states o of the previous event of
   cost[o] + join(E(o), S(p)).  The minimum is not taken over pairs: for k = hw..1 a table holds the cheapest o for
   every suffix of length k of E(o) (a hash table, for k <= 3 an array) and prefix_k(S(p)) is looked up; only o with
   cost[o] - min < k can beat the join without overlap.  Costs are kept relative to the minimum of their layer (one
   byte per state) and the cuts are recovered backwards without back-pointers.
   hw = h and the states of a layer are the cuts of its trail (narrow model: exactly co's pass), or, with --wide,
   hw = n - 1 (a join of overlap k costs h - k, down to -2; the pass counts hw - k, which differs by a constant) and a
   layer has extra states: the gap-1 cuts that can make a tight join with the event before or after it in the
   order (cw_extras).  A gap-1 cut without a tight join is never generated.
   One state only: segments, pieces of chained trails and of the open path.  An unchanged piece that is a whole closed
   trail is the cut `start 0` of that trail and is free like any other.
   Skip cuts: an event may only take the skip it already uses (--co); with --co-skip every skip is
   allowed and the pass is repeated with bans while two events skip the same window. */
typedef struct {
    u64 key;
    u32 gen, val;
} CWSlot;
typedef struct {
    CWSlot *t;
    u64 cap;
    u32 gen;
    u64 *S, *E, *Ep;
    int *mv;
    i64 wcap;         /* current layer: start words, end words, cheapest way in; Ep: end words of the previous layer */
    unsigned char *d; /* direct tables for k = 1, 2, 3 */
    unsigned char *rel;
    i64 rcap; /* cost of every cut relative to the minimum of its layer; 255: not allowed */
    unsigned char *relx, *wr, *wp;
    i64 xcap,
        *offx; /* wide: the same for the gap-1 states, 4 bits each (15: not needed); working copies of two layers */
    i64 *off, *lmin, *cur,
        lcap; /* per layer: offset into rel (offx: into relx), minimum cost, current state (-1: one state only) */
    i64 *ban;
    int nban, bancap;      /* cw_skip = 1: (event, window) pairs that are not allowed */
    i64 nfree, nopt, maxm; /* statistics of the last pass: free events, their states, largest layer */
    u64 *gb;
    i64 *tbit, ngx;
    u32 *gs;
    i64 gscap;
    double
        tx; /* wide: the gap-1 states, one bit per letter of every trail (trail t from bit tbit[t]); their number; those of one layer; seconds to find them */
} CW;
static int cw_skip = 0, LTH = 1; /* LTH: threads for cw_extras */
static i64 cw_it = 0;            /* --coit N: the pass on the current sequence of a thread every N iterations */
static int
    cw_g1 = 1,
    cw_itg1 =
        -1; /* --g1 M (--coit-g1 M for the passes of --coit; default: the same): which gap-1 states the wide pass gets: 0 tight partners, 1 (default) and 2 also chains of gap-1 pieces, 3 all (see cw_extras) */
static inline void cw_put(CW *q, u64 mask, u64 key, u32 val) {
    u64 i = hmix(key) & mask;
    while (q->t[i].gen == q->gen) {
        if (q->t[i].key == key) {
            if (val < q->t[i].val)
                q->t[i].val = val;
            return;
        }
        i = (i + 1) & mask;
    }
    q->t[i].key = key;
    q->t[i].gen = q->gen;
    q->t[i].val = val;
}
/* As co_get of recut.c, in the table of the wide pass. */
static inline int cw_get(const CW *q, u64 mask, u64 key) {
    u64 i = hmix(key) & mask;
    while (q->t[i].gen == q->gen) {
        if (q->t[i].key == key)
            return (int)q->t[i].val;
        i = (i + 1) & mask;
    }
    return -1;
}
/* is there a permutation window at cyclic position pos */
static inline int win_at(const Trail *T, i64 pos) {
    i64 R = T->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    int used = 0;
    for (int k = 0; k < n; k++) {
        used |= 1 << T->c[pos];
        if (++pos == R)
            pos = 0;
    }
    return used == (1 << n) - 1;
}
/* the state an event is: its option; -2 - start for a whole trail written from a gap-1 cut (wide); -1: one state only */
static i64 cw_cur(const Ev *x) {
    if (x->kind == EV_OPT)
        return x->a;
    if (wide && is_g1(x))
        return win_at(&TR[x->t], x->a) && win_at(&TR[x->t], x->a - 1) ? -2 - x->a : -1;
    if (x->kind != EV_PIECE)
        return -1;
    const Trail *T = &TR[x->t];
    if (T->fixed || T->c != W + PS[x->a])
        return -1;
    for (i64 o = T->ohi - 1; o >= T->olo; o--)
        if (!OP[o].start && !OP[o].g1)
            return (x->l == T->R + h + oD(o) && x->s == oS_t(T, o) && x->e == oE_t(T, o)) ? o : -1;
    return -1;
}
/* As co_skip_ok of recut.c: may event i take cut o, which drops an occurrence? */
static inline int cw_skip_ok(const CW *q, const Ev *x, i64 i, const Trail *T, i64 o, int anyskip) {
    i64 r = oSK_t(T, o);
    if (!anyskip)
        return r == x->skip;
    for (int k = 0; k < q->nban; k++)
        if (q->ban[2 * k] == i && q->ban[2 * k + 1] == r)
            return 0;
    return 1;
}
/* 15: a state that no shortest path needs */
static inline int cw_nib(const unsigned char *b, i64 z) {
    int v = (b[z >> 1] >> (4 * (z & 1))) & 15;
    return v == 15 ? 255 : v;
}
static inline int cw_dist(u64 e, u64 s, int hw) {
    for (int k = hw; k >= 1; k--)
        if ((e & HMASK[k]) == (s >> (4 * (hw - k))))
            return hw - k;
    return hw;
}

/* ----- wide: where can a gap-1 cut make a tight join?  Windows are handled as packed words of n letters.  The
   windows of a trail come in visits: a run of rotations of one permutation (gap 1 between them), entered and left by
   a gap of 2 or 3, so the plain cuts of a trail are exactly the starts of its visits and the option table lists
   them.  A visit table of a trail maps the class of a visit (its rotation that starts with symbol 0) to the visit;
   any permutation is then found in the trail with one probe.  The partners of a window a = a0 a1 v that ends an
   event: v a1 a0 (weight-2 step, overlap n - 2), and its rotations by 1 and 2 (overlap n - 1, n - 2). */
/* class, start, place of symbol 0 in the first window, number of windows */
typedef struct {
    u64 key;
    u32 st;
    unsigned char zf, m;
} VSlot;
typedef struct {
    VSlot *t;
    u64 cap, mask;
    i64 *pl;
    i64 plcap, np;
} VT;
/* the first k letters go to the end, 0 <= k < n */
static inline u64 pk_rotl(u64 p, int k) {
    return k ? ((p << (4 * k)) | (p >> (4 * (n - k)))) & HMASK[n] : p;
}
static inline int pk_zero(u64 p) {
    for (int k = 0; k < n; k++)
        if (!((p >> (4 * (n - 1 - k))) & 15))
            return k;
    return 0;
}
/* a0 a1 v -> v a1 a0 */
static inline u64 pk_w2(u64 p) {
    u64 a0 = p >> (4 * (n - 1)), a1 = (p >> (4 * (n - 2))) & 15;
    return ((p << 8) & HMASK[n]) | (a1 << 4) | a0;
}
/* v y x -> x y v */
static inline u64 pk_w2inv(u64 p) {
    u64 x = p & 15, y = (p >> 4) & 15;
    return (x << (4 * (n - 1))) | (y << (4 * (n - 2))) | (p >> 8);
}
/* The window of n letters of a trail at cyclic position pos, packed. */
static inline u64 pk_cyc(const Trail *T, i64 pos) {
    i64 R = T->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    u64 v = 0;
    for (int k = 0; k < n; k++) {
        v = (v << 4) | T->c[pos];
        if (++pos == R)
            pos = 0;
    }
    return v;
}
/* the window that ends with the n - 1 letters we (front = 1) or starts with them (front = 0); 0 if they are not n - 1 different letters */
static inline int pk_complete(u64 w, int front, u64 *p) {
    int used = 0;
    for (int k = 0; k < n - 1; k++)
        used |= 1 << ((w >> (4 * k)) & 15);
    if (__builtin_popcount(used) != n - 1)
        return 0;
    u64 miss = (u64)__builtin_ctz(~used);
    *p = front ? (miss << (4 * (n - 1))) | w : (w << 4) | miss;
    return 1;
}
/* The visit table of trail T: its plain cuts, hashed by the class of rotations of the window they start, so
   that any permutation is found in the trail with one probe. */
static void vt_build(VT *v, const Trail *T) {
    i64 R = T->R;
    v->np = 0;
    if (T->ohi - T->olo > v->plcap) {
        v->plcap = T->ohi - T->olo + 1024;
        free(v->pl);
        v->pl = malloc((size_t)v->plcap * 8);
    }
    for (i64 o = T->olo; o < T->ohi; o++)
        if (!OP[o].g1)
            v->pl[v->np++] = o;
    u64 need = 64;
    while (need < 2 * (u64)v->np + 16)
        need <<= 1;
    if (need > v->cap) {
        free(v->t);
        v->t = malloc(need * sizeof(VSlot));
        v->cap = need;
        if (!v->t || !v->pl)
            DIE("out of memory");
    }
    v->mask = need - 1;
    for (u64 i = 0; i < need; i++)
        v->t[i].key = ~0ULL;
    for (i64 z = 0; z < v->np; z++) {
        i64 o = v->pl[z], o2 = v->pl[z + 1 < v->np ? z + 1 : 0], s = OP[o].start;
        i64 m = (((i64)OP[o2].start - OP[o2].g - s) % R + R) % R + 1;
        if (m > n + 1)
            m = n + 1;
        u64 p = pk_cyc(T, s);
        int zf = pk_zero(p);
        u64 key = pk_rotl(p, zf), i = hmix(key) & v->mask;
        while (v->t[i].key != ~0ULL)
            i = (i + 1) & v->mask;
        v->t[i].key = key;
        v->t[i].st = (u32)s;
        v->t[i].zf = (unsigned char)zf;
        v->t[i].m = (unsigned char)m;
    }
}
/* Is this key in the table of v? */
static inline int vt_has(const VT *v, u64 key) {
    for (u64 i = hmix(key) & v->mask; v->t[i].key != ~0ULL; i = (i + 1) & v->mask)
        if (v->t[i].key == key)
            return 1;
    return 0;
}
/* the window p in the trail of v: its position, its number k in its visit and the m windows of the visit; -1 if it is not there */
static inline i64 vt_find(const VT *v, const Trail *T, u64 p, int *k, int *m) {
    int z = pk_zero(p);
    u64 key = pk_rotl(p, z);
    for (u64 i = hmix(key) & v->mask; v->t[i].key != ~0ULL; i = (i + 1) & v->mask)
        if (v->t[i].key == key) {
            int kk = v->t[i].zf - z;
            if (kk < 0)
                kk += n;
            if (kk < v->t[i].m) {
                *k = kk;
                *m = v->t[i].m;
                return (v->t[i].st + kk) % T->R;
            }
        }
    return -1;
}
/* the gap-1 states of every layer: the gap-1 cut an event already is, and the gap-1 cuts of its trail next to a
   window that has a partner window in the neighbouring event (a fixed neighbour has one end window; of a free
   neighbour every window can end / start its piece).  They are kept as one bit per letter of the trails (a free
   event is the only event of its trail), set by all threads at once. */
/* the bits of trail t in the bitmap gb as starts, in order: (*buf)[0 .. returned number) */
static i64 cw_bits(const u64 *gb, i64 b0, i64 R, u32 **buf, i64 *cap) {
    i64 b1 = b0 + R, m = 0;
    for (i64 w = b0 >> 6; w <= (b1 - 1) >> 6; w++) {
        u64 x = gb[w];
        if (!x)
            continue;
        if (w == b0 >> 6)
            x &= ~0ULL << (b0 & 63);
        if (w == (b1 - 1) >> 6 && (b1 & 63))
            x &= ~0ULL >> (64 - (b1 & 63));
        for (; x; x &= x - 1) {
            if (m == *cap) {
                *cap = *cap ? 2 * *cap : 4096;
                *buf = realloc(*buf, (size_t)*cap * 4);
                if (!*buf)
                    DIE("out of memory");
            }
            (*buf)[m++] = (u32)((w << 6) + __builtin_ctzll(x) - b0);
        }
    }
    return m;
}
#define CW_BIT(t, st)                                                            \
    do {                                                                         \
        u64 b_ = (u64)(q->tbit[t] + (st));                                       \
        __atomic_fetch_or(&q->gb[b_ >> 6], 1ULL << (b_ & 63), __ATOMIC_RELAXED); \
    } while (0)
/* pair of events (i, i + 1), both free: the gap-1 states (bitmap src) of one of them offer the gap-1 cuts of the other
   that join them with overlap h.  dir 0: from event i to i + 1; 1: from i + 1 to i.  Returns the number of new states. */
static i64 cw_spread(CW *q, const Ev *ev, const i64 *c0, i64 i, int dir, const u64 *src, VT *vb, u32 **gs, i64 *gcap) {
    static const unsigned char P6[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};
    if (c0[i] == -1 || c0[i + 1] == -1)
        return 0;
    u32 t = ev[dir ? i + 1 : i].t, u = ev[dir ? i : i + 1].t;
    const Trail *T = &TR[t], *U = &TR[u];
    int k, m;
    i64 ng = cw_bits(src, q->tbit[t], T->R, gs, gcap), added = 0;
    if (!ng)
        return 0;
    vt_build(vb, U);
    for (i64 y = 0; y < ng; y++) {
        u64 w = pk_cyc(T, dir ? (i64)(*gs)[y] : (i64)(*gs)[y] - 1),
            l3[3]; /* dir 0: the window that ends the piece; 1: the one that starts it */
        for (int c = 0; c < 3; c++)
            l3[c] = dir ? (w >> (4 * (2 - c))) & 15 : (w >> (4 * (n - 1 - c))) & 15;
        for (int c = 0; c < 6; c++) {
            u64 x3 = l3[P6[c][0]] << 8 | l3[P6[c][1]] << 4 | l3[P6[c][2]];
            u64 pw = dir ? (x3 << (4 * h)) | (w >> 12) : ((w & HMASK[h]) << 12) | x3;
            i64 pos = vt_find(vb, U, pw, &k, &m);
            if (pos < 0)
                continue;
            if (dir) {
                if (k >= m - 1)
                    continue;
                pos = (pos + 1) % U->R;
            } else if (k < 1)
                continue;
            u64 b_ = (u64)(q->tbit[u] + pos), bit = 1ULL << (b_ & 63);
            if (!(__atomic_fetch_or(&q->gb[b_ >> 6], bit, __ATOMIC_RELAXED) & bit))
                added++;
        }
    }
    return added;
}
/* Decides which cuts inside a 1-cycle the wide pass is offered (by g1mode: next to a possible tight join with
   the neighbour in the order, chains of such pieces, or all) and marks them, one bit per window of every trail. */
static void cw_extras(CW *q, const Ev *ev, i64 N, int g1mode) {
    double t0 = wall();
    q->ngx = 0;
    if (!wide)
        return;
    q->tbit = malloc((size_t)(NT + 1) * 8);
    i64 nbit = 0;
    for (i64 t = 0; t < NT; t++) {
        q->tbit[t] = nbit;
        nbit += TR[t].R;
    }
    q->gb = calloc((size_t)(nbit >> 6) + 2, 8);
    i64 *c0 = malloc((size_t)(N + 1) * 8);
    if (!q->tbit || !q->gb || !c0)
        DIE("out of memory");
#pragma omp parallel for num_threads(LTH) schedule(dynamic, 64)
    for (i64 i = 0; i < N; i++)
        c0[i] = cw_cur(&ev[i]);
#pragma omp parallel num_threads(LTH)
    {
        VT va, vb;
        memset(&va, 0, sizeof va);
        memset(&vb, 0, sizeof vb);
#pragma omp for schedule(dynamic, 4)
        for (i64 i = 0; i < N; i++) {
            i64 o0 = c0[i];
            if (o0 == -1)
                continue;
            u32 t = ev[i].t;
            const Trail *T = &TR[t];
            i64 R = T->R;
            int k, m;
            u64 p;
            if (o0 <= -2)
                CW_BIT(t, -2 - o0);
            if (g1mode == 3) { /* every gap-1 cut */
                i64 pv = -1, o1 = -1;
                for (i64 o = T->olo; o <= T->ohi; o++) {
                    i64 oo = o < T->ohi ? o : o1;
                    if (oo < 0 || OP[oo].g1)
                        continue;
                    if (o1 < 0)
                        o1 = o;
                    if (pv >= 0) {
                        i64 s = OP[pv].start, vm = (((i64)OP[oo].start - OP[oo].g - s) % R + R) % R + 1;
                        for (i64 j = 1; j < vm; j++)
                            CW_BIT(t, (s + j) % R);
                    }
                    pv = oo;
                }
                continue;
            }
            int fprev = i > 0 && c0[i - 1] == -1, fnext = i + 1 < N && c0[i + 1] == -1;
            if (fprev || fnext)
                vt_build(&va, T);
            if (fprev && pk_complete(WE(&ev[i - 1]), 1, &p)) { /* the event in front ends with the window p */
                u64 b[3] = {pk_rotl(p, 1), pk_w2(p), pk_rotl(p, 2)};
                for (int z = 0; z < 3; z++) {
                    i64 pos = vt_find(&va, T, b[z], &k, &m);
                    if (pos >= 0 && k >= 1)
                        CW_BIT(t, pos);
                }
            }
            if (fnext && pk_complete(WS(&ev[i + 1]), 0, &p)) { /* the event behind starts with the window p */
                u64 a[3] = {pk_rotl(p, n - 1), pk_w2inv(p), pk_rotl(p, n - 2)};
                for (int z = 0; z < 3; z++) {
                    i64 pos = vt_find(&va, T, a[z], &k, &m);
                    if (pos >= 0 && k < m - 1)
                        CW_BIT(t, (pos + 1) % R);
                }
            }
            if (i + 1 < N && !fnext) { /* a free event behind: every window of T against its visits */
                u32 u = ev[i + 1].t;
                const Trail *U = &TR[u];
                vt_build(&vb, U);
                i64 np = 0;
                for (i64 o = T->olo; o < T->ohi; o++)
                    if (!OP[o].g1)
                        np++;
                i64 o = T->olo;
                while (o < T->ohi && OP[o].g1)
                    o++;
                for (i64 z = 0; z < np; z++) {
                    i64 o2 = o + 1;
                    while (o2 < T->ohi && OP[o2].g1)
                        o2++;
                    if (o2 >= T->ohi) {
                        o2 = T->olo;
                        while (OP[o2].g1)
                            o2++;
                    }
                    i64 s = OP[o].start, vm = (((i64)OP[o2].start - OP[o2].g - s) % R + R) % R + 1;
                    if (vm > n + 1)
                        vm = n + 1;
                    u64 f = pk_cyc(T, s);
                    int same = vt_has(&vb, pk_rotl(f, pk_zero(f)));
                    for (int j = 0; j < vm; j++) {
                        u64 a = pk_rotl(f, j % n), b[3] = {pk_w2(a), pk_rotl(a, 1), pk_rotl(a, 2)};
                        for (int y = 0; y < (same ? 3 : 1); y++) {
                            i64 pos = vt_find(&vb, U, b[y], &k, &m);
                            if (pos < 0)
                                continue;
                            if (j < vm - 1)
                                CW_BIT(t, (s + j + 1) % R);
                            if (k >= 1)
                                CW_BIT(u, pos);
                        }
                    }
                    o = o2;
                }
            }
        }
        free(va.t);
        free(va.pl);
        free(vb.t);
        free(vb.pl);
    }
    /* --g1 1 / 2: also the gap-1 cuts that join with overlap h (cost 0) a gap-1 state of the neighbouring event that
       was found above (1: one step; 2: until nothing is added), i.e. chains of gap-1 pieces around a tight join */
    if (g1mode == 1) {
        size_t nw = (size_t)(nbit >> 6) + 2;
        u64 *src = malloc(nw * 8);
        if (!src)
            DIE("out of memory");
        memcpy(src, q->gb, nw * 8);
#pragma omp parallel num_threads(LTH)
        {
            VT vb;
            memset(&vb, 0, sizeof vb);
            u32 *gs = NULL;
            i64 gcap = 0;
#pragma omp for schedule(dynamic, 4)
            for (i64 z = 0; z < 2 * (N - 1); z++)
                cw_spread(q, ev, c0, z < N - 1 ? z : z - (N - 1), z >= N - 1, src, &vb, &gs, &gcap);
            free(vb.t);
            free(vb.pl);
            free(gs);
        }
        free(src);
    } else if (g1mode == 2) {
        VT vb;
        memset(&vb, 0, sizeof vb);
        i64 added = 1;
        for (int sweep = 0; added && sweep < 64; sweep++) {
            added = 0;
            for (i64 i = 0; i + 1 < N; i++)
                added += cw_spread(q, ev, c0, i, 0, q->gb, &vb, &q->gs, &q->gscap);
            for (i64 i = N - 2; i >= 0; i--)
                added += cw_spread(q, ev, c0, i, 1, q->gb, &vb, &q->gs, &q->gscap);
        }
        free(vb.t);
        free(vb.pl);
    }
    free(c0);
    i64 m = 0;
#pragma omp parallel for num_threads(LTH) reduction(+ : m)
    for (i64 z = 0; z < (nbit >> 6) + 1; z++)
        m += __builtin_popcountll(q->gb[z]);
    q->ngx = m;
    q->tx = wall() - t0;
}
/* the gap-1 states of trail t, in order of their starts: q->gs[0 .. returned number) */
static i64 cw_states(CW *q, u32 t) {
    return q->gb ? cw_bits(q->gb, q->tbit[t], TR[t].R, &q->gs, &q->gscap) : 0;
}

/* the events may change their state; returns the gain in letters */
static i64 cw_run(CW *q, Ev *ev, i64 N, int anyskip, int *nchg) {
    const int hw = wide ? n - 1 : h;
    if (N > q->lcap) {
        q->lcap = N + N / 2 + 64;
        q->off = realloc(q->off, q->lcap * 8);
        q->offx = realloc(q->offx, q->lcap * 8);
        q->lmin = realloc(q->lmin, q->lcap * 8);
        q->cur = realloc(q->cur, q->lcap * 8);
    }
    i64 roff = 0, xoff = 0, pm = 0, pmin = 0, oldc = 0;
    int pfree = 0;
    u64 pe = 0;
    q->nfree = q->nopt = q->maxm = 0;
    if (q->rcap < NO + 1) {
        q->rcap = NO + 1;
        q->rel = realloc(q->rel, (size_t)q->rcap);
    } /* one byte per cut, no more */
    if (q->xcap < q->ngx / 2 + 2) {
        q->xcap = q->ngx / 2 + 2;
        q->relx = realloc(q->relx, (size_t)q->xcap);
    } /* and half a byte per gap-1 state */
    if (!q->rel || !q->relx || !q->off || !q->offx || !q->lmin || !q->cur)
        DIE("out of memory");
#define CW_START(j) ((j) < m ? (i64)OP[T->olo + (j)].start : (i64)gs[(j) - m])
#define CW_GAP(j) ((j) < m ? (int)OP[T->olo + (j)].g : 1)
#define CW_S(j) (wide ? ww_cyc(T, CW_START(j)) : hw_cyc(T, CW_START(j)))
#define CW_E(j) (wide ? ww_cyc(T, CW_START(j) - CW_GAP(j) + 1) : hw_cyc(T, CW_START(j) - CW_GAP(j) + 3))
#define CW_XS(x) (wide ? WS(x) : (x)->s)
#define CW_XE(x) (wide ? WE(x) : (x)->e)
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 o0 = cw_cur(x);
        u64 xs = CW_XS(x);
        q->cur[i] = -1;
        q->off[i] = roff;
        q->offx[i] = xoff;
        if (i)
            oldc += cw_dist(CW_XE(&ev[i - 1]), xs, hw);
        if (o0 == -1) { /* one state */
            i64 cst = 0;
            if (i && !pfree)
                cst = pmin + cw_dist(pe, xs, hw);
            else if (i) {
                const unsigned char *prel = q->wp;
                int best = hw;
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < best) {
                        int v = prel[j] + cw_dist(q->Ep[j], xs, hw);
                        if (v < best)
                            best = v;
                    }
                cst = pmin + best;
            }
            q->lmin[i] = pmin = cst;
            pe = CW_XE(x);
            pfree = 0;
            continue;
        }
        const Trail *T = &TR[x->t];
        i64 m = T->ohi - T->olo, ng = cw_states(q, x->t), M = m + ng;
        const u32 *gs = q->gs;
        if (o0 >= 0) {
            q->cur[i] = o0 - T->olo;
            oldc += oD(o0);
        } else {
            i64 lo = 0, hi = ng - 1;
            while (lo < hi) {
                i64 z = (lo + hi) >> 1;
                if ((i64)gs[z] < -2 - o0)
                    lo = z + 1;
                else
                    hi = z;
            }
            if (!ng || (i64)gs[lo] != -2 - o0)
                DIE("internal error: cluster optimisation (gap-1 state of event %lld)", i);
            q->cur[i] = m + lo;
            oldc += 2;
        }
        if (M > q->wcap) {
            q->wcap = M + M / 2 + 64;
            q->S = realloc(q->S, q->wcap * 8);
            q->E = realloc(q->E, q->wcap * 8);
            q->Ep = realloc(q->Ep, q->wcap * 8);
            q->mv = realloc(q->mv, q->wcap * sizeof(int));
            q->wr = realloc(q->wr, q->wcap);
            q->wp = realloc(q->wp, q->wcap); /* wp keeps its content: a larger layer follows a smaller one */
        }
        if (roff + m > q->rcap || xoff + ng > 2 * (q->xcap - 1))
            DIE("internal error: cluster optimisation (more states than counted)");
        if (!q->d)
            q->d = malloc(16 + 256 + 4096);
        if (!q->S || !q->E || !q->Ep || !q->mv || !q->wr || !q->wp || !q->d)
            DIE("out of memory");
        unsigned char *rel = q->wr;
        const unsigned char *prel = q->wp;
        u64 *S = q->S, *E = q->E;
        int *mv = q->mv;
        for (i64 j = 0; j < M; j++) {
            if (j < m && OP[T->olo + j].g1 && !cw_skip_ok(q, x, i, T, T->olo + j, anyskip)) {
                rel[j] = 255;
                continue;
            }
            S[j] = CW_S(j);
            E[j] = CW_E(j);
            rel[j] = 0;
            mv[j] = !i ? 0 : !pfree ? cw_dist(pe, S[j], hw) : hw;
        }
        if (i && pfree) {
            u64 need = 16;
            while (need < 2 * (u64)pm)
                need <<= 1;
            if (need > q->cap) {
                free(q->t);
                q->t = calloc(need, sizeof(CWSlot));
                q->cap = need;
                q->gen = 0;
                if (!q->t)
                    DIE("out of memory");
            }
            u64 mask = need - 1;
            for (int k = hw; k >= 4; k--) {
                i64 cnt = 0;
                int sh = 4 * (hw - k);
                q->gen++;
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < k) {
                        cw_put(q, mask, q->Ep[j] & HMASK[k], prel[j]);
                        cnt++;
                    }
                if (!cnt)
                    break;
                for (i64 j = 0; j < M; j++) {
                    if (rel[j] == 255 || mv[j] <= hw - k)
                        continue;
                    int v = cw_get(q, mask, S[j] >> sh);
                    if (v >= 0 && v + hw - k < mv[j])
                        mv[j] = v + hw - k;
                }
            }
            /* k = 3, 2, 1: tables indexed by the word */
            unsigned char *d1 = q->d, *d2 = d1 + 16, *d3 = d2 + 256;
            int any = 0;
            memset(q->d, 255, 16 + 256 + 4096);
            for (i64 j = 0; j < pm; j++) {
                int r = prel[j];
                if (r >= 3)
                    continue;
                u64 e = q->Ep[j];
                any = 1;
                if (r < d3[e & 4095])
                    d3[e & 4095] = (unsigned char)r;
                if (r < 2 && r < d2[e & 255])
                    d2[e & 255] = (unsigned char)r;
                if (r < 1)
                    d1[e & 15] = 0;
            }
            if (any)
                for (i64 j = 0; j < M; j++) {
                    if (rel[j] == 255 || mv[j] <= hw - 3)
                        continue;
                    int v = d3[S[j] >> (4 * (hw - 3))];
                    if (v + hw - 3 < mv[j])
                        mv[j] = v + hw - 3;
                    if (mv[j] <= hw - 2)
                        continue;
                    v = d2[S[j] >> (4 * (hw - 2))];
                    if (v + hw - 2 < mv[j])
                        mv[j] = v + hw - 2;
                    if (mv[j] == hw && !d1[S[j] >> (4 * (hw - 1))])
                        mv[j] = hw - 1;
                }
        }
        int mn = 1 << 20;
        for (i64 j = 0; j < M; j++)
            if (rel[j] != 255) {
                mv[j] += 3 - CW_GAP(j);
                if (mv[j] < mn)
                    mn = mv[j];
            }
        for (i64 j = 0; j < M; j++)
            if (rel[j] != 255)
                rel[j] = (unsigned char)(mv[j] - mn);
        memcpy(q->rel + roff, rel,
               (size_t)m); /* kept for the way back: the cuts as they are, the gap-1 states in 4 bits */
        for (i64 j = m, z = xoff; j < M; j++, z++) {
            unsigned char v = rel[j] < 15 ? rel[j] : 15, *b = &q->relx[z >> 1];
            *b = z & 1 ? (unsigned char)((*b & 0x0f) | v << 4) : (unsigned char)((*b & 0xf0) | v);
        }
        q->lmin[i] = pmin = pmin + mn;
        pfree = 1;
        pm = M;
        roff += m;
        xoff += ng;
        q->wr = q->wp;
        q->wp = rel;
        q->E = q->Ep;
        q->Ep = E;
        q->nfree++;
        q->nopt += M;
        if (M > q->maxm)
            q->maxm = M;
    }
    /* backwards: the state of layer i that reaches the cost wanted by layer i+1 (the current one if it does) */
    i64 newc = q->lmin[N - 1], want = 0;
    u64 ns = 0;
    int chg = 0;
    for (i64 i = N - 1; i >= 0; i--) {
        i64 c0 = q->cur[i];
        Ev *x = &ev[i];
        if (c0 < 0) {
            if (i < N - 1 && q->lmin[i] + cw_dist(CW_XE(x), ns, hw) != want)
                DIE("internal error: cluster optimisation (event %lld)", i);
            ns = CW_XS(x);
            want = q->lmin[i];
            continue;
        }
        const Trail *T = &TR[x->t];
        const unsigned char *relp = q->rel + q->off[i];
        i64 m = T->ohi - T->olo, ng = cw_states(q, x->t), M = m + ng, pick = -1;
        const u32 *gs = q->gs;
        i64 tgt = i < N - 1 ? want : q->lmin[i];
#define rel(j) ((j) < m ? relp[j] : cw_nib(q->relx, q->offx[i] + (j) - m))
#define COV(j) (q->lmin[i] + rel(j) + (i < N - 1 ? cw_dist(CW_E(j), ns, hw) : 0))
        i64 room = tgt - q->lmin[i]; /* a state can reach the target only if its own cost leaves room for the join */
        if (rel(c0) != 255 && COV(c0) == tgt)
            pick = c0;
        for (int pass = 0; pass < 3 && pick < 0; pass++) /* plain cuts first, then gap-1 cuts, then skips */
            for (i64 j = pass == 1 ? m : 0; j < (pass == 1 ? M : m); j++)
                if (rel(j) <= room && (pass || !OP[T->olo + j].g1) && COV(j) == tgt) {
                    pick = j;
                    break;
                }
#undef COV
        if (pick < 0)
            DIE("internal error: cluster optimisation (event %lld)", i);
        if (pick != c0) {
            *x = pick < m ? make_event(T->olo + pick) : g1_event(x->t, gs[pick - m]);
            chg++;
        }
        ns = CW_S(pick);
        want = q->lmin[i] + rel(pick) - (3 - CW_GAP(pick));
#undef rel
    }
#undef CW_START
#undef CW_GAP
#undef CW_S
#undef CW_E
#undef CW_XS
#undef CW_XE
    if (nchg)
        *nchg = chg;
    return oldc - newc;
}
/* cw_skip = 1: bans for events that took a skip another event uses; returns the number of new bans */
static int cw_pair_cmp(const void *a, const void *b) {
    const i64 *x = a, *y = b;
    return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : x[1] < y[1] ? -1 : x[1] > y[1];
}
/* As co_clash of recut.c: bans for events that dropped an occurrence another event drops too. */
static int cw_clash(CW *q, const Ev *orig, const Ev *ev, i64 N) {
    i64 ns = 0, *sk = NULL;
    int added = 0;
    for (int pass = 0; pass < 2; pass++) {
        if (pass)
            sk = malloc((size_t)(ns + 1) * 16);
        ns = 0;
        for (i64 i = 0; i < N; i++)
            if (ev[i].skip >= 0) {
                if (pass) {
                    sk[2 * ns] = ev[i].skip;
                    sk[2 * ns + 1] = i;
                }
                ns++;
            }
    }
    qsort(sk, (size_t)ns, 16, cw_pair_cmp);
    for (i64 x = 0; x < ns;) {
        i64 y = x;
        while (y < ns && sk[2 * y] == sk[2 * x])
            y++;
        if (y - x > 1) {
            i64 keep = sk[2 * x + 1];
            for (i64 z = x; z < y; z++)
                if (orig[sk[2 * z + 1]].skip == sk[2 * x])
                    keep = sk[2 * z + 1];
            for (i64 z = x; z < y; z++)
                if (sk[2 * z + 1] != keep) {
                    if (q->nban == q->bancap) {
                        q->bancap = q->bancap ? q->bancap * 2 : 64;
                        q->ban = realloc(q->ban, (size_t)q->bancap * 16);
                    }
                    q->ban[2 * q->nban] = sk[2 * z + 1];
                    q->ban[2 * q->nban + 1] = sk[2 * x];
                    q->nban++;
                    added++;
                }
        }
        x = y;
    }
    free(sk);
    return added;
}
/* the whole sequence */
static void cw_full(Ev *ev, i64 N) {
    double t0 = wall();
    CW q;
    memset(&q, 0, sizeof q);
    Ev *orig = malloc((size_t)N * sizeof(Ev));
    memcpy(orig, ev, (size_t)N * sizeof(Ev));
    i64 l0 = seq_length(ev, N), l1;
    int chg, rounds = 0;
    cw_extras(&q, ev, N, cw_g1);
    if (wide) {
        printf(
            "cluster optimisation (wide): %lld gap-1 states offered (--g1 %d, found in %.1fs); %.0f MB for the costs of all states" NL,
            q.ngx, cw_g1, q.tx, (NO + q.ngx / 2) / 1e6);
        fflush(stdout);
    }
    for (;;) {
        i64 gain = cw_run(&q, ev, N, cw_skip, &chg);
        l1 = seq_length(ev, N);
        rounds++;
        if (l0 - l1 != gain)
            DIE("internal error: cluster optimisation promised %lld, got %lld", gain, l0 - l1);
        if (!cw_skip || !cw_clash(&q, orig, ev, N))
            break;
        memcpy(ev, orig, (size_t)N * sizeof(Ev));
    }
    i64 ng1 = 0, nt = 0;
    for (i64 i = 0; i < N; i++) {
        if (wide && is_g1(&ev[i]))
            ng1++;
        if (i + 1 < N && jdist(&ev[i], &ev[i + 1]) < 0)
            nt++;
    }
    printf(
        "cluster optimisation%s: %lld -> %lld (%d openings changed; %lld of %lld events free, %lld states, at most %lld per event, %d pass%s, %d bans, %.1fs)\n",
        wide ? " (wide)" : "", l0, l1, chg, q.nfree, N, q.nopt, q.maxm, rounds, rounds > 1 ? "es" : "", q.nban,
        wall() - t0);
    if (wide)
        printf("cluster optimisation (wide): the result has %lld gap-1 openings and %lld tight joins" NL, ng1, nt);
    fflush(stdout);
    free(orig);
    free(q.t);
    free(q.S);
    free(q.E);
    free(q.Ep);
    free(q.mv);
    free(q.d);
    free(q.rel);
    free(q.off);
    free(q.lmin);
    free(q.cur);
    free(q.ban);
    free(q.gb);
    free(q.tbit);
    free(q.gs);
    free(q.relx);
    free(q.wr);
    free(q.wp);
    free(q.offx);
}

/* ==================== own part: the wide model in the search ==================== */
/* ---------- wide model in the search.  The plain cuts are placed as before (joins on h letters; only the join
   that an insertion breaks is measured exactly), and on top of that the sequence itself says where a trail can make
   a tight join: the window that ends (starts) a node has three partner windows (rotation by 1, weight-2 step,
   rotation by 2), and if a partner lies in trail t, then t cut open in front of (behind) that window joins the node
   with n - 1 or n - 2 letters.  A node that is itself a gap-1 piece also offers its six partners at overlap h to
   gap-1 cuts (chains of gap-1 pieces).  Where a permutation lies is answered by a table over the classes of
   rotations (CYC: class -> the plain cut that starts its visit; 4 (n-1)! bytes), and the tight index TX of a
   search thread maps a trail to the nodes that have a partner in it, so best_insertion looks at these few nodes only. */
static u64 *CYX;
static i64 NCYX; /* CYX: further visits of a class, sorted (class << 32 | cut) */
/* rank of the class of p; *z: place of symbol 0 */
static inline u64 pk_class(u64 p, int *z) {
    *z = pk_zero(p);
    u64 c = pk_rotl(p, *z), r = 0;
    int used = 0;
    for (int k = 1; k < n; k++) {
        int v = (int)((c >> (4 * (n - 1 - k))) & 15) - 1;
        r += (u64)(v - __builtin_popcount(used & ((1 << v) - 1))) * fact[n - 1 - k];
        used |= 1 << v;
    }
    return r;
}
static int u64_cmp(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return x < y ? -1 : x > y;
}
/* The class table of the wide search: for every class of rotations the plain cut that starts its visit;
   further visits of a class go to the sorted list CYX.  4 (n-1)! bytes. */
static void cyc_build(void) {
    double t0 = wall();
    u64 nc = fact[n - 1];
    i64 cap = 0;
    int z;
    CYC = malloc((size_t)nc * 4);
    if (!CYC)
        DIE("out of memory for the class table");
    memset(CYC, 0xff, (size_t)nc * 4);
    for (i64 t = 0; t < NT; t++)
        for (i64 o = TR[t].olo; o < TR[t].ohi; o++)
            if (!OP[o].g1) {
                u64 c = pk_class(pk_cyc(&TR[t], OP[o].start), &z);
                if (CYC[c] == 0xffffffffu)
                    CYC[c] = (u32)o;
                else {
                    if (NCYX == cap) {
                        cap = cap ? 2 * cap : 4096;
                        CYX = realloc(CYX, (size_t)cap * 8);
                        if (!CYX)
                            DIE("out of memory");
                    }
                    CYX[NCYX++] = c << 32 | (u64)o;
                }
            }
    if (NO >> 32)
        DIE("the class table holds 32-bit openings");
    if (NCYX)
        qsort(CYX, (size_t)NCYX, 8, u64_cmp);
    u64 miss = 0;
    for (u64 c = 0; c < nc; c++)
        miss += CYC[c] == 0xffffffffu;
    printf(
        "wide: class table %.0f MB, %lld classes visited more than once, %llu classes without a plain opening (%.1fs)" NL,
        nc * 4 / 1e6, NCYX, (unsigned long long)miss, wall() - t0);
    fflush(stdout);
}
/* trail, position, cut of the visit and of the next visit, number in the visit, windows of the visit */
typedef struct {
    u32 t;
    i64 pos, o, o2;
    int k, m;
} PF;
/* the idx-th visit of the class of the window p: 0 if there is none; r->pos < 0 if p itself is not in that visit */
static int pm_find(u64 p, int idx, PF *r) {
    int z;
    u64 c = pk_class(p, &z);
    i64 o;
    if (!idx) {
        if (CYC[c] == 0xffffffffu)
            return 0;
        o = CYC[c];
    } else {
        i64 lo = 0, hi = NCYX;
        while (lo < hi) {
            i64 m = (lo + hi) >> 1;
            if (CYX[m] >> 32 < c)
                lo = m + 1;
            else
                hi = m;
        }
        lo += idx - 1;
        if (lo >= NCYX || CYX[lo] >> 32 != c)
            return 0;
        o = (i64)(CYX[lo] & 0xffffffffu);
    }
    u32 t = otrail(o);
    const Trail *T = &TR[t];
    i64 R = T->R, o2 = o + 1;
    while (o2 < T->ohi && OP[o2].g1)
        o2++;
    if (o2 >= T->ohi) {
        o2 = T->olo;
        while (OP[o2].g1)
            o2++;
    }
    i64 s = OP[o].start, m = (((i64)OP[o2].start - OP[o2].g - s) % R + R) % R + 1;
    if (m > n + 1)
        m = n + 1;
    int k = pk_zero(pk_cyc(T, s)) - z;
    if (k < 0)
        k += n;
    r->t = t;
    r->o = o;
    r->o2 = o2;
    r->k = k;
    r->m = (int)m;
    r->pos = k < m ? (s + k) % R : -1;
    return 1;
}
/* an cut of trail t: g = 1: the gap-1 cut in front of `start` (o = -1); else the plain cut o */
typedef struct {
    u32 t;
    i64 start, o;
    int g;
} WCand;
/* the cuts of other trails that node event x offers: side 0 = pieces that can follow x, side 1 = pieces that can precede it */
static int wc_list(const Ev *x, int side, WCand *out, int cap) {
    static const unsigned char P6[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};
    u64 w, pp[9], l3[3];
    int np = 3, nc = 0;
    if (x->l < n || !pk_complete(side ? WS(x) : WE(x), !side, &w))
        return 0;
    if (!side) {
        pp[0] = pk_rotl(w, 1);
        pp[1] = pk_w2(w);
        pp[2] = pk_rotl(w, 2);
    } else {
        pp[0] = pk_rotl(w, n - 1);
        pp[1] = pk_w2inv(w);
        pp[2] = pk_rotl(w, n - 2);
    }
    if (is_g1(x)) {
        for (int c = 0; c < 3; c++)
            l3[c] = side ? (w >> (4 * (2 - c))) & 15 : (w >> (4 * (n - 1 - c))) & 15;
        for (int c = 0; c < 6; c++) {
            u64 x3 = l3[P6[c][0]] << 8 | l3[P6[c][1]] << 4 | l3[P6[c][2]];
            pp[np++] = side ? (x3 << (4 * h)) | (w >> 12) : ((w & HMASK[h]) << 12) | x3;
        }
    }
    for (int z = 0; z < np; z++)
        for (int idx = 0; nc < cap; idx++) {
            PF r;
            if (!pm_find(pp[z], idx, &r))
                break;
            if (r.pos < 0 || r.t == x->t)
                continue;
            WCand *q = &out[nc];
            q->t = r.t;
            q->o = -1;
            q->g = 1;
            if (!side) {
                if (r.k >= 1)
                    q->start = r.pos;
                else if (z < 3) {
                    q->o = r.o;
                    q->g = OP[r.o].g;
                    q->start = OP[r.o].start;
                } else
                    continue;
            } else {
                if (r.k < r.m - 1)
                    q->start = (r.pos + 1) % TR[r.t].R;
                else if (z < 3) {
                    q->o = r.o2;
                    q->g = OP[r.o2].g;
                    q->start = OP[r.o2].start;
                } else
                    continue;
            }
            nc++;
        }
    return nc;
}
#define TXK 12 /* tight-index entries per node, at most */
static void tx_reset(Ctx *c) {
    if (c->txcap != c->ncap) {
        free(c->txk);
        c->txk = malloc((size_t)c->ncap * TXK * 4);
        c->txcap = c->ncap;
        if (!c->txk)
            DIE("out of memory");
    }
    h_reset(&c->TX, (i64)c->ncap * TXK + 64);
    for (int i = 0; i < c->nn; i++)
        tx_add(c, i);
}
/* Enters node id into the tight index: for each trail that holds a partner window of its first or last
   window, a link from that trail to the node (at most TXK per node). */
static void tx_add(Ctx *c, int id) {
    u32 *key = c->txk + (size_t)id * TXK;
    int nk = 0;
    WCand cd[24];
    for (int side = 0; side < 2; side++) {
        int nc = wc_list(&c->nd[id].v, side, cd, 24);
        for (int z = 0; z < nc && nk < TXK; z++) {
            u32 k = cd[z].t * 2 + side;
            int dup = 0;
            for (int y = 0; y < nk; y++)
                dup |= key[y] == k;
            if (!dup) {
                key[nk++] = k;
                h_add(&c->TX, k, id);
            }
        }
    }
    while (nk < TXK)
        key[nk++] = 0xffffffffu;
}
/* Takes node id out of the tight index. */
static void tx_del(Ctx *c, int id) {
    u32 *key = c->txk + (size_t)id * TXK;
    HTab *H = &c->TX;
    for (int y = 0; y < TXK && key[y] != 0xffffffffu; y++) {
        u64 i = hmix(key[y]) & H->mask;
        while (H->t[i].key != key[y])
            i = (i + 1) & H->mask;
        int p = -1, e = H->t[i].head;
        while (H->val[e] != id) {
            p = e;
            e = H->next[e];
        }
        if (p < 0)
            H->t[i].head = H->next[e];
        else
            H->next[p] = H->next[e];
    }
}
/* best insertion of trail t in the wide model: `best` is the answer for the plain cuts (host or card); the
   cuts that the tight index offers are measured exactly on n - 1 letters and win if they are cheaper.
   The result has opt <= -2 for a gap-1 cut: the piece starts at -2 - opt. */
static Ins wide_ins(Ctx *c, u32 t, double noise, Ins best) {
    if (!wide || !CYC)
        return best;
    const Node *nd = c->nd;
    const Trail *T = &TR[t];
    u64 amp = NZAMP(noise), bfx = ~0ULL, bkey = 0;
    Ins w = best;
    WCand cd[24];
    for (int side = 0; side < 2; side++)
        for (int e = h_get(&c->TX, (u64)t * 2 + side); e >= 0; e = c->TX.next[e]) {
            int x = c->TX.val[e];
            if (!nd[x].alive)
                continue;
            int a = side ? nd[x].prev : x, b2 = side ? x : nd[x].next;
            if (a < 0 || b2 < 0)
                continue;
            int nc = wc_list(&nd[x].v, side, cd, 24);
            for (int z = 0; z < nc; z++) {
                if (cd[z].t != t)
                    continue;
                i64 st = cd[z].start;
                int g = cd[z].g;
                i64 d = wdist(WE(&nd[a].v), ww_cyc(T, st)) + 3 - g + wdist(ww_cyc(T, st - g + 1), WS(&nd[b2].v)) -
                        jdist(&nd[a].v, &nd[b2].v);
                u64 key = cd[z].o < 0 ? 1ULL << 40 | (u64)st : (u64)cd[z].o;
                u64 fx = VFIX(d) + (amp ? (nz16(c->nzit, key, (u64)a) * amp) >> 16 : 0);
                c->wst[0]++;
                if (fx < bfx || (fx == bfx && (key < bkey || (key == bkey && a < w.after)))) {
                    bfx = fx;
                    bkey = key;
                    w.delta = d;
                    w.after = a;
                    w.opt = cd[z].o < 0 ? -2 - st : cd[z].o;
                }
            }
        }
    if (bfx == ~0ULL)
        return best;
    w.val = (double)bfx / 65536.0 - 64.0;
    w.wide = 1;
    return w.val < best.val ? w : best;
}

/* ==================== shared base again: the search loop, the loader, main ==================== */
/* ---------- shared best sequence */
static Ev *G_ev;
static i64 G_N, G_len;
static int G_dirty;
static double G_t0, G_last_ck, G_last_log;
static i64 G_it[256];
/* One search thread.  Until the time or the iteration limit: choose trails to remove, take them out, put each
   back (greedy order or random order, with or without noise), accept or undo by the annealing rule.  A new best
   sequence goes to the shared copy G_ev under the lock gbest; odd threads adopt the shared best at sync time. */
static void search(Ctx *c, const Ev *init_ev, i64 initN, const char *outplan) {
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->nzk = hmix(seed * 1000003ULL + (u64)c->tid * 7919ULL + 0x632BE59BD9B4E019ULL);
    c->rem = calloc((size_t)NT + 1, 1);
    c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    c->thead = malloc(((size_t)NT + 1) * sizeof(int));
    c->rth = malloc(((size_t)NT + 1) * 2 * sizeof(int));
    if (use_gpu)
        gm_attach(c);
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c);
    c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    double ts0 = wall();
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        c->nzit = hmix(c->nzk + (u64)c->it);
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
        }
        if (cw_it > 0 && c->it % cw_it == 0) { /* cluster optimisation of the current sequence */
            i64 m = ctx_export(c, c->tmp), g = 0;
            CW q;
            memset(&q, 0, sizeof q);
            int chg = 0;
            u64 oh = 0;
            for (i64 z = 0; z < m; z++)
                oh = hmix(oh ^ c->tmp[z].t) + (u64)c->tmp[z].kind;
            if (oh != c->cohash || c->cur != c->colen) {
                double t1 = wall();
                cw_extras(&q, c->tmp, m, cw_itg1 < 0 ? cw_g1 : cw_itg1);
                g = cw_run(&q, c->tmp, m, 0, &chg);
                c->wst[4]++;
                c->cosec += wall() - t1;
            }
            c->cohash = oh;
            c->colen = c->cur - g;
            free(q.t);
            free(q.S);
            free(q.E);
            free(q.Ep);
            free(q.mv);
            free(q.d);
            free(q.rel);
            free(q.off);
            free(q.lmin);
            free(q.cur);
            free(q.gb);
            free(q.tbit);
            free(q.gs);
            free(q.relx);
            free(q.wr);
            free(q.wp);
            free(q.offx);
            if (g > 0) {
                ctx_load(c, c->tmp, m);
                c->cur -= g;
                c->wst[3]++;
                if (c->cur != ctx_length(c))
                    DIE("internal error: cluster optimisation in the search");
                if (c->cur < c->best_len) {
                    c->best_len = c->cur;
#pragma omp critical(gbest)
                    if (c->cur < G_len) {
                        printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, cluster optimisation, %d openings)\n",
                               wall() - G_t0, G_len, c->cur, c->tid, c->it, chg);
                        fflush(stdout);
                        G_N = ctx_export(c, G_ev);
                        G_len = c->cur;
                        G_dirty = 1;
                    }
                }
            }
        }
        nd = c->nd;
        double frac = (wall() - G_t0) / tlimit, temp = tf * T0 * (1 - frac) + 0.05;
#if defined(TS_CHECK) && TS_CHECK > 1
        seq_check(c);
#endif
        int *order = c->order, *cand = c->cand, *rel = c->rel;
        i64 N = c->N, ncand = c->ncand;
#define EVT(i) (nd[order[i]].v)
#define RS(r) ((r) ? cand[(r) - 1] + 1 : 0) /* run r: positions RS(r) .. RE(r) */
#define RE(r) ((r) < ncand ? cand[r] : (int)N - 1)
        int k = (int)rndint(c, 1, kmax);
        i64 nrem = 0;
        double mode = rndu(c);
#define REMOVE(tt)                          \
    do {                                    \
        u32 t_ = (tt);                      \
        if (!c->rem[t_] && !TR[t_].fixed) { \
            c->rem[t_] = 1;                 \
            c->pend[nrem++] = t_;           \
        }                                   \
    } while (0)
        if (mode < prel) {
            /* a run plus one or two runs whose end / start words are within one step of an cut of its trails */
            int nrun = (int)ncand + 1, X = -1;
            if (rndu(c) < 0.7) {
                for (int tries = 0; tries < 50; tries++) {
                    int r = (int)rndn(c, nrun);
                    if (RE(r) - RS(r) + 1 <= 5) {
                        X = r;
                        break;
                    }
                }
            }
            if (X < 0)
                X = (int)rndn(c, nrun);
            i64 xlen = RE(X) - RS(X) + 1;
            if (xlen > runcap) { /* long run: only a window of it */
                i64 lo = RS(X) + rndn(c, xlen - k + 1 > 0 ? xlen - k + 1 : 1);
                for (i64 i = lo; i <= RE(X) && i < lo + k; i++)
                    REMOVE(EVT(i).t);
            } else {
                i64 nopt = 0;
                for (int i = RS(X); i <= RE(X); i++)
                    nopt += TR[EVT(i).t].ohi - TR[EVT(i).t].olo;
                int nrel = nopt <= 600000 ? rel_runs(c, order + RS(X), (int)xlen, runcap, rel) : 0;
                for (int i = RS(X); i <= RE(X); i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), id = rel[z];
                    rel[z] = rel[--nrel];
                    for (;; id = nd[id].next) {
                        REMOVE(nd[id].v.t);
                        if (nd[id].next < 0 || jdist(&nd[id].v, &nd[nd[id].next].v) >= 2)
                            break;
                    }
                }
            }
        } else if (mode < 0.5 + prel / 2) {
            i64 j = ncand ? cand[rndn(c, ncand)] : rndn(c, N - 1);
            i64 lo = j - rndint(c, 0, k);
            if (lo < 0)
                lo = 0;
            for (i64 i = lo; i < N && i < lo + k; i++)
                REMOVE(EVT(i).t);
        } else if (mode < 0.75) {
            for (int q = 0; q < k; q++)
                REMOVE(EVT(rndn(c, N)).t);
        } else {
            int segs = (int)rndint(c, 2, 3), len = k / 2 > 1 ? k / 2 : 1;
            for (int q = 0; q < segs; q++) {
                i64 j = rndn(c, N);
                for (i64 i = j; i < N && i < j + len; i++)
                    REMOVE(EVT(i).t);
            }
        }
        i64 nbig = 0;
        {
            double bp = bigp;
            i64 m = 0;
            for (i64 q = 0; q < nrem; q++) {
                u32 t_ = c->pend[q];
                int big = TR[t_].ohi - TR[t_].olo > splitmax;
                if (big && bp < 1.0 && rndu(c) >= bp) {
                    c->rem[t_] = 0;
                    continue;
                }
                nbig += big;
                c->pend[m++] = t_;
            }
            nrem = m;
        }
        if (!nrem)
            continue;
        if (!nbig && focus > 0 && rndu(c) < focus) {
            for (i64 q = 0; q < nrem; q++)
                c->rem[c->pend[q]] = 0;
            continue;
        }
        /* destroy: the nodes of the removed trails, in the order of the sequence */
        c->nremlog = c->ninslog = 0;
        c->relabeled = 0;
        int nn0 = c->nn, nrk = 0;
        i64 dl = 0; /* dl: change of the length */
        for (i64 q = 0; q < nrem; q++) {
            u32 t_ = c->pend[q];
            c->rem[t_] = 0;
            c->rth[2 * q] = (int)t_;
            c->rth[2 * q + 1] = c->thead[t_];
            for (int id = c->thead[t_]; id >= 0; id = c->tnx[id]) {
                if (nrk == c->rkcap) {
                    c->rkcap = c->rkcap ? c->rkcap * 2 : 256;
                    c->rk = realloc(c->rk, (size_t)c->rkcap * sizeof(i64));
                }
                c->rk[nrk++] = (seq_pos(c, id, N) << 32) | id;
            }
            c->thead[t_] = -1;
        }
        qsort(c->rk, (size_t)nrk, sizeof(i64), i64_cmp);
        for (int q = 0; q < nrk; q++) {
            int id = (int)(c->rk[q] & 0xffffffff);
            dl -= node_len(c, id);
            if (nd[id].v.skip >= 0)
                skp_del(c, nd[id].v.skip);
            node_unlink(c, id);
            c->remlog[c->nremlog++] = id;
        }
        int nskp0 = c->nskp;
        int accept = 0;
        i64 nl = 0;
        if (c->N >= 3) {
            /* repair */
            for (i64 q = nrem - 1; q > 0; q--) {
                i64 z = rndn(c, q + 1);
                u32 x = c->pend[q];
                c->pend[q] = c->pend[z];
                c->pend[z] = x;
            }
            int greedy = rndu(c) < 0.5;
            double noise = rndu(c) < 0.5 ? 0.0 : 0.6;
            i64 np = nrem;
            while (np > 0) {
#define BEST_INS(q) \
    wide_ins(c, c->pend[q], noise, c->G && c->G->has[q] ? c->G->ins[q] : best_insertion(c, c->pend[q], noise))
                if (c->G)
                    gm_round(c, c->pend, greedy ? np : 1, noise); /* the big trails of this round, in one launch */
                i64 pick = 0;
                Ins bi = BEST_INS(0);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) {
                        Ins x = BEST_INS(q);
                        double rr = rndu(c);
                        if (x.val < bi.val || (x.val == bi.val && rr < br)) {
                            br = rr;
                            bi = x;
                            pick = q;
                        }
                    }
                }
                u32 t = c->pend[pick];
                Split sp;
                sp.ok = 0;
                if (use_split && TR[t].ohi - TR[t].olo <= splitmax)
                    sp = best_split(c, t, 400);
                if (sp.ok && (double)sp.delta < bi.val) {
                    Ev e1, e2;
                    seg_events(sp.c1, sp.c2, &e1, &e2);
                    dl += node_len(c, node_insert_after(c, c->nd[sp.i].prev, &e1));
                    dl += node_len(c, node_insert_after(c, sp.jm, &e2));
                } else {
                    Ev x = bi.opt <= -2 ? g1_event(t, -2 - bi.opt) : make_event(bi.opt);
                    if (bi.wide) {
                        c->wst[1]++;
                        c->wst[2] += bi.opt <= -2;
                    }
                    dl += node_len(c, node_insert_after(c, bi.after, &x));
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                }
                c->pend[pick] = c->pend[--np];
            }
            nl = c->cur + dl;
#if defined(TS_CHECK) && TS_CHECK > 1
            if (nl != ctx_length(c))
                DIE("check: length %lld, by differences %lld at it %lld", ctx_length(c), nl, c->it);
#endif
            i64 d = nl - c->cur;
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
        }
        if (accept) {
            c->cur = nl;
            c->acc++;
            for (int q = 0; q < c->nremlog; q++)
                index_del(c, c->remlog[q]);
            if (c->relabeled)
                seq_build(c);
            else
                seq_patch(c, N, nn0);
            if (nl < c->best_len) {
                c->best_len = nl;
#pragma omp critical(gbest)
                if (nl < G_len) {
                    printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, removed %lld trails, %lld big)\n",
                           wall() - G_t0, G_len, nl, c->tid, c->it, nrem, nbig);
                    fflush(stdout);
                    G_N = ctx_export(c, G_ev);
                    G_len = nl;
                    G_dirty = 1;
                }
            }
        } else {
            for (int q = c->ninslog - 1; q >= 0; q--) {
                node_unlink(c, c->inslog[q]);
                index_del(c, c->inslog[q]);
            }
            for (int q = c->nremlog - 1; q >= 0; q--)
                node_relink(c, c->remlog[q]);
            if (c->relabeled)
                relabel(c);
            for (i64 q = 0; q < nrem; q++)
                c->thead[c->rth[2 * q]] = c->rth[2 * q + 1];
            c->nskp = nskp0;
            for (int q = 0; q < c->nremlog; q++)
                if (nd[c->remlog[q]].v.skip >= 0)
                    skp_add(c, nd[c->remlog[q]].v.skip);
        }
        c->trh = hmix(c->trh ^ (u64)nl ^ ((u64)accept << 62));
        if ((c->it & 63) == 0) {
            double tn = wall();
            if (tn - last_sync > sync_sec || (c->tid == 0 && tn - G_last_log > 20)) {
                int adopt = 0;
                i64 an = 0;
#pragma omp critical(gbest)
                {
                    G_it[c->tid] = c->it;
                    if (tn - last_sync > sync_sec && (c->tid & 1) && G_len < c->best_len) {
                        memcpy(c->tmp, G_ev, (size_t)G_N * sizeof(Ev));
                        an = G_N;
                        adopt = 1;
                        c->best_len = G_len;
                        c->cur = G_len;
                    }
                    if (c->tid == 0) {
                        if (G_dirty && tn - G_last_ck > ckpt_sec) {
                            write_plan(G_ev, G_N, outplan);
                            G_last_ck = tn;
                            G_dirty = 0;
                        }
                        if (tn - G_last_log > 20) {
                            i64 tot = 0;
                            for (int q = 0; q < NTHR; q++)
                                tot += G_it[q];
                            printf("it %lld t=%.0fs best %lld (thread 0: cur %lld)\n", tot, tn - G_t0, G_len, c->cur);
                            fflush(stdout);
                            G_last_log = tn;
                        }
                    }
                }
                if (tn - last_sync > sync_sec)
                    last_sync = tn;
                if (adopt)
                    ctx_load(c, c->tmp, an);
            }
        }
    }
#pragma omp critical(gbest)
    G_it[c->tid] = c->it;
    if (c->G)
        gm_report(c, wall() - ts0);
    if (wide || cw_it)
#pragma omp critical(gbest)
    {
        printf(
            "thread %d: %lld passes of --coit (%.0fs), %lld with a gain; wide: %lld offered openings measured, %lld insertions won by them (%lld gap-1 cuts)" NL,
            c->tid, c->wst[4], c->cosec, c->wst[3], c->wst[0], c->wst[1], c->wst[2]);
        fflush(stdout);
    }
#ifdef TS_CHECK
    {
        u64 hsh = 0;
        for (int id = c->first; id >= 0; id = c->nd[id].next) {
            const Ev *x = &c->nd[id].v;
            hsh = hmix(hsh ^ ((u64)x->kind << 60) ^ ((u64)x->t << 36) ^ (u64)x->a) + (u64)x->l;
        }
#pragma omp critical(gbest)
        {
            printf(
                "STATE it %lld cur %lld best %lld acc %lld N %lld seq %016llx rng %016llx %016llx %016llx %016llx" NL,
                c->it, c->cur, c->best_len, c->acc, c->N, hsh, c->rs[0], c->rs[1], c->rs[2], c->rs[3]);
            fflush(stdout);
        }
    }
#endif
    if (NTHR == 1)
        printf("history checksum %016llx (%lld accepted, current length %lld); %.1f iterations/s\n",
               (unsigned long long)c->trh, c->acc, c->cur, c->it / (wall() - ts0));
}

/* ---------- loading */
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
/* window positions (in order) of a cyclic word; returns their number */
static i64 trail_windows(const Trail *T, i64 *wp) {
    i64 R = T->R, m = 0;
    int cnt[16] = {0}, distinct = 0;
    if (T->fixed) { /* open path: no wrap-around */
        i64 len = R + h;
        for (i64 i = 0; i < len; i++) {
            if (cnt[T->c[i]]++ == 0)
                distinct++;
            if (i >= n) {
                if (--cnt[T->c[i - n]] == 0)
                    distinct--;
            }
            if (i >= n - 1 && distinct == n)
                wp[m++] = i - n + 1;
        }
        return m;
    }
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

/* cuts of trail t in window order; writes them to out (if not NULL) and returns their number */
static i64 trail_options(i64 t, i64 *wp, const u64 *dupb, Opt *out, i64 *hist, i64 *shist) {
    if (TR[t].fixed)
        return 0;
    i64 R = TR[t].R, m = trail_windows(&TR[t], wp), k = 0;
    for (i64 i = 0; i < m && m >= 2; i++) {
        i64 i1 = i + 1 == m ? 0 : i + 1, i2 = i1 + 1 == m ? 0 : i1 + 1;
        i64 g = (wp[i1] - wp[i] + R) % R;
        if (g >= 2) {
            if (g > 3)
                DIE("gap %lld inside a trail", g);
            if (out) {
                out[k].start = (u32)wp[i1];
                out[k].g = (unsigned char)g;
                out[k].g1 = 0;
                hist[3 - g + 3]++;
            }
            k++;
        }
        if (use_skip && m >= 3) {
            u64 r = rank_cyc(&TR[t], wp[i1]);
            if ((dupb[r >> 6] >> (r & 63)) & 1) {
                i64 g2 = g + (wp[i2] - wp[i1] + R) % R;
                if (g2 >= 2) {
                    if (out) {
                        out[k].start = (u32)wp[i2];
                        out[k].g = (unsigned char)g2;
                        out[k].g1 = (unsigned char)g;
                        hist[3 - g2 + 3]++;
                        shist[3 - g2 + 3]++;
                    }
                    k++;
                }
            }
        }
    }
    return k;
}

/* Reads the options, loads the base word, splits it into pieces and closed trails, builds the table of cuts,
   loads the plan, runs the passes that were asked for and the search, and writes the plan and the word. */
int main(int argc, char **argv) {
    if (argc < 3)
        DIE("usage: trailsearch WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip] [--nosplit] [--plan-in FILE] [--ckpt SEC] [--iters N] [--threads T] [--sync SEC] [--wide] [--co] [--co-skip] [--coit N] [--g1 M]");
    const char *plan_in = NULL;
    int cw_first = 0;
    for (int a = 3; a < argc; a++) {
        if (!strcmp(argv[a], "--time") && a + 1 < argc)
            tlimit = atof(argv[++a]);
        else if (!strcmp(argv[a], "--seed") && a + 1 < argc)
            seed = strtoull(argv[++a], 0, 10);
        else if (!strcmp(argv[a], "--kmax") && a + 1 < argc)
            kmax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--T0") && a + 1 < argc)
            T0 = atof(argv[++a]);
        else if (!strcmp(argv[a], "--ckpt") && a + 1 < argc)
            ckpt_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--iters") && a + 1 < argc)
            maxit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--plan-in") && a + 1 < argc)
            plan_in = argv[++a];
        else if (!strcmp(argv[a], "--threads") && a + 1 < argc)
            NTHR = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--sync") && a + 1 < argc)
            sync_sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--bigp") && a + 1 < argc)
            bigp = atof(argv[++a]);
        else if (!strcmp(argv[a], "--focus") && a + 1 < argc)
            focus = atof(argv[++a]);
        else if (!strcmp(argv[a], "--gpu"))
            use_gpu = 1;
        else if (!strcmp(argv[a], "--gpuprof")) {
            gpu_prof = 1;
            gpu_map = 0;
        } else if (!strcmp(argv[a], "--gpucopy"))
            gpu_map = 0;
        else if (!strcmp(argv[a], "--gpucheck"))
            gpu_check = 1;
        else if (!strcmp(argv[a], "--gpumin") && a + 1 < argc)
            gpu_min = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--ptx") && a + 1 < argc)
            ptx_path = argv[++a];
        else if (!strcmp(argv[a], "--wide"))
            wide = 1;
        else if (!strcmp(argv[a], "--g1") && a + 1 < argc)
            cw_g1 = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--coit-g1") && a + 1 < argc)
            cw_itg1 = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--co"))
            cw_first = 1;
        else if (!strcmp(argv[a], "--coit") && a + 1 < argc)
            cw_it = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--co-skip"))
            cw_first = cw_skip = 1;
        else if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--nosplit"))
            use_split = 0;
        else
            DIE("unknown option %s", argv[a]);
    }
    if (NTHR < 1 || NTHR > 256)
        DIE("1 to 256 threads");
    double t00 = wall();
    W = load_word(argv[1], &L);
    int mx = 0;
    for (i64 i = 0; i < L; i++)
        if (W[i] > mx)
            mx = W[i];
    n = mx + 1;
    h = n - 3;
    if (n < 6 || n > 13)
        DIE("6 to 13 symbols");
    for (int k = 0; k <= 16; k++)
        HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    /* permutation windows and pieces (split at gaps >= 4) */
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
        printf("n=%d L=%lld perm windows %lld pieces %lld (%.1fs)\n", n, L, nw, NP, wall() - t00);
        fflush(stdout);
    }
    /* trails: closed pieces, chains of open pieces, single pieces written from a gap-2 / gap-1 cut */
    char *closed = calloc((size_t)NP, 1);
    i64 *trail_of_piece = malloc(NP * 8);
    for (i64 k = 0; k < NP; k++)
        trail_of_piece[k] = -1;
    TR = calloc((size_t)NP + 1, sizeof(Trail));
    NT = 0;
    i64 nclosed = 0, nopen = 0;
    for (i64 k = 0; k < NP; k++)
        if (closes(k, 0)) {
            closed[k] = 1;
            nclosed++;
            trail_of_piece[k] = NT;
            TR[NT].c = W + PS[k];
            TR[NT].R = PL[k] - h;
            NT++;
        }
    i64 nlinear = 0;
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
        /* phase 0 starts at the pieces nothing leads to (open paths), phase 1 takes the cycles */
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
                if (ex) { /* a whole trail written from a gap-2 or gap-1 cut */
                    closed[k] = 1;
                    nclosed++;
                    trail_of_piece[k] = NT;
                    TR[NT].c = W + PS[k];
                    TR[NT].R = PL[k] - h - ex;
                    NT++;
                    continue;
                }
                i64 R = 0;
                for (i64 b = 0; b < nc; b++)
                    R += PL[chain[b]] - h;
                unsigned char *c = malloc((size_t)R + h + 16);
                i64 q = 0;
                for (i64 b = 0; b < nc; b++) {
                    memcpy(c + q, W + PS[chain[b]], (size_t)(PL[chain[b]] - h));
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
    i64 sumR = 0, maxR = 0;
    for (i64 t = 0; t < NT; t++) {
        sumR += TR[t].R;
        if (TR[t].R > maxR)
            maxR = TR[t].R;
    }
    printf("trails %lld (closed pieces %lld, chained open pieces %lld), sum R %lld\n", NT, nclosed, nopen, sumR);
    if (nlinear)
        printf("%lld pieces form an open path that is not a closed trail; they stay where they are\n", nlinear);
    fflush(stdout);
    /* duplicate windows, then the cuts of every trail (parallel over trails) */
    u64 NF = fact[n];
    u64 *seenb = calloc((size_t)(NF >> 6) + 1, 8), *dupb = calloc((size_t)(NF >> 6) + 1, 8);
    if (!seenb || !dupb)
        DIE("out of memory");
    int LT = NTHR > 8 ? NTHR : 8;
    if (LT > omp_get_max_threads())
        LT = omp_get_max_threads();
    LTH = LT;
    i64 nwin = 0;
#pragma omp parallel num_threads(LT) reduction(+ : nwin)
    {
        i64 *wp = malloc((size_t)(maxR + 8) * 8);
        if (!wp)
            DIE("out of memory");
#pragma omp for schedule(dynamic, 8)
        for (i64 t = 0; t < NT; t++) {
            i64 m = trail_windows(&TR[t], wp);
            nwin += m;
            for (i64 i = 0; i < m; i++) {
                u64 r = TR[t].fixed ? rank_lin(TR[t].c + wp[i]) : rank_cyc(&TR[t], wp[i]), bit = 1ULL << (r & 63);
                u64 old = __atomic_fetch_or(&seenb[r >> 6], bit, __ATOMIC_RELAXED);
                if (old & bit)
                    __atomic_fetch_or(&dupb[r >> 6], bit, __ATOMIC_RELAXED);
            }
        }
        free(wp);
    }
    {
        u64 dcount = 0, scount = 0;
        for (u64 i = 0; i <= (NF >> 6); i++) {
            scount += __builtin_popcountll(seenb[i]);
            dcount += __builtin_popcountll(dupb[i]);
        }
        printf("trail windows %lld distinct %llu (n! check: %s), duplicated %llu (%.1fs)\n", nwin, scount,
               scount == NF ? "True" : "False", dcount, wall() - t00);
        fflush(stdout);
        if (scount != NF)
            DIE("the trails do not contain every permutation (%llu missing): the model cannot be used on this word",
                (unsigned long long)(NF - scount));
        free(seenb);
    }
    /* A window may be skipped only if its permutation really occurs twice in the word.  The cyclic word of a trail
       can contain a window that the word itself does not have (a piece cut open across a duplicate window), so the
       duplicates are counted again on the word and the two sets are intersected. */
    {
        u64 *ws = calloc((size_t)(NF >> 6) + 1, 8), *wd = calloc((size_t)(NF >> 6) + 1, 8);
        if (!ws || !wd)
            DIE("out of memory");
        i64 nwin_word = L - n + 1;
#pragma omp parallel num_threads(LT)
        {
            int tid = omp_get_thread_num(), nt = omp_get_num_threads();
            i64 a = nwin_word * tid / nt, b = nwin_word * (tid + 1) / nt;
            int cnt[16] = {0}, distinct = 0;
            for (i64 i = a; i < a + n - 1 && i < L; i++)
                if (cnt[W[i]]++ == 0)
                    distinct++;
            for (i64 p = a; p < b; p++) {
                if (cnt[W[p + n - 1]]++ == 0)
                    distinct++;
                if (distinct == n) {
                    u64 r = rank_lin(W + p), bit = 1ULL << (r & 63);
                    u64 old = __atomic_fetch_or(&ws[r >> 6], bit, __ATOMIC_RELAXED);
                    if (old & bit)
                        __atomic_fetch_or(&wd[r >> 6], bit, __ATOMIC_RELAXED);
                }
                if (--cnt[W[p]] == 0)
                    distinct--;
            }
        }
        u64 before = 0, after = 0;
        for (u64 i = 0; i <= (NF >> 6); i++) {
            before += __builtin_popcountll(dupb[i]);
            dupb[i] &= wd[i];
            after += __builtin_popcountll(dupb[i]);
        }
        if (before != after) {
            printf(
                "%llu duplicated windows exist only in the cyclic words, not in the word: they will not be skipped" NL,
                (unsigned long long)(before - after));
            fflush(stdout);
        }
        free(ws);
        free(wd);
    }
    {
        i64 hist[8] = {0}, shist[8] = {0};
        i64 *ocnt = calloc((size_t)NT + 1, 8);
        for (int pass = 0; pass < 2; pass++) {
#pragma omp parallel num_threads(LT)
            {
                i64 *wp = malloc((size_t)(maxR + 8) * 8), lh[8] = {0}, lsh[8] = {0};
                if (!wp)
                    DIE("out of memory");
#pragma omp for schedule(dynamic, 8)
                for (i64 t = 0; t < NT; t++) {
                    i64 k = trail_options(t, wp, dupb, pass ? OP + TR[t].olo : NULL, lh, lsh);
                    if (!pass)
                        ocnt[t] = k;
                    else if (k != ocnt[t])
                        DIE("internal error: option count");
                }
                free(wp);
#pragma omp critical
                for (int d = 0; d < 8; d++) {
                    hist[d] += lh[d];
                    shist[d] += lsh[d];
                }
            }
            if (!pass) {
                NO = 0;
                for (i64 t = 0; t < NT; t++) {
                    TR[t].olo = NO;
                    NO += ocnt[t];
                    TR[t].ohi = NO;
                }
                OP = malloc((size_t)(NO + 1) * sizeof(Opt));
                if (!OP)
                    DIE("out of memory for %lld options", NO);
            }
        }
        free(ocnt);
        printf("options %lld by extra cost {", NO);
        for (int d = 0; d < 8; d++)
            if (hist[d])
                printf(" %d: %lld", d - 3, hist[d]);
        printf(" }; dup-skip options {");
        for (int d = 0; d < 8; d++)
            if (shist[d])
                printf(" %d: %lld", d - 3, shist[d]);
        printf(" } (%.1fs)\n", wall() - t00);
        fflush(stdout);
    }
    free(dupb);
    /* current sequence */
    i64 cap = NP * 2 + 1024;
    Ev *ev = malloc(cap * sizeof(Ev));
    i64 N = 0;
    if (!plan_in) {
        for (i64 k = 0; k < NP; k++)
            ev[N++] = piece_event(k, trail_of_piece[k]);
        i64 L0 = seq_length(ev, N);
        printf("model length of the input sequence: %lld (word %lld)\n", L0, L);
        fflush(stdout);
        if (L0 != L)
            DIE("the model does not reproduce the word");
    } else {
        FILE *f = fopen(plan_in, "r");
        if (!f)
            DIE("cannot open %s", plan_in);
        char tag[32];
        int pn;
        i64 pL, pN;
        if (fscanf(f, "%31s %d %lld %lld", tag, &pn, &pL, &pN) != 4 || pn != n || pL != L)
            DIE("plan does not match the word");
        for (i64 q = 0; q < pN; q++) {
            char c[4];
            if (fscanf(f, "%3s", c) != 1)
                DIE("bad plan");
            Ev x;
            if (c[0] == 'P') {
                i64 k;
                if (fscanf(f, "%lld", &k) != 1 || k < 0 || k >= NP)
                    DIE("bad plan");
                x = piece_event(k, trail_of_piece[k]);
            } else if (c[0] == 'O') {
                u32 t, st;
                int g, g1;
                if (fscanf(f, "%u %u %d %d", &t, &st, &g, &g1) != 4 || t >= NT)
                    DIE("bad plan");
                i64 o = -1;
                for (i64 z = TR[t].olo; z < TR[t].ohi; z++)
                    if (OP[z].start == st && OP[z].g == g && OP[z].g1 == g1) {
                        o = z;
                        break;
                    }
                if (o < 0)
                    DIE("plan option not found");
                x = make_event(o);
            } else {
                u32 t;
                i64 st, l;
                if (fscanf(f, "%u %lld %lld", &t, &st, &l) != 3 || t >= NT || (wide && l < n))
                    DIE("bad plan");
                x = seg_event(t, st, l);
            }
            if (N + 2 >= cap) {
                cap *= 2;
                ev = realloc(ev, cap * sizeof(Ev));
            }
            ev[N++] = x;
        }
        fclose(f);
        if (!wide) {
            i64 g = 0;
            for (i64 q = 0; q < N; q++)
                g += is_g1(&ev[q]);
            if (g)
                printf(
                    "warning: the plan has %lld whole trails written from gap-1 cuts: it belongs to the wide model, load it with --wide" NL,
                    g);
        }
        printf("model length of the plan: %lld (%lld events)\n", seq_length(ev, N), N);
        fflush(stdout);
    }
    if (cw_first)
        cw_full(ev, N);
    /* ---------- destroy / repair search */
    char outplan[4096];
    snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
    memcpy(G_ev, ev, (size_t)N * sizeof(Ev));
    G_N = N;
    G_len = seq_length(ev, N);
    if (wide && tlimit > 0 && maxit != 0)
        cyc_build();
    if (cw_it > 0)
        omp_set_max_active_levels(2); /* the passes inside the search threads use the loading threads */
    if (use_gpu)
        use_gpu = gpu_init(argv[0], LT);
    G_t0 = G_last_ck = G_last_log = wall();
    if (!(wide && tlimit <= 0)) /* a wide pass alone needs no search context */
#pragma omp parallel num_threads(NTHR)
    {
        Ctx *c = calloc(1, sizeof(Ctx));
        c->tid = omp_get_thread_num();
        search(c, ev, N, outplan);
    }
    i64 tot = 0;
    for (int q = 0; q < NTHR; q++)
        tot += G_it[q];
    printf("LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, G_len);
    fflush(stdout);
    if (tot > 0 && cw_first) {
        cw_full(G_ev, G_N);
        G_len = seq_length(G_ev, G_N);
    }
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
