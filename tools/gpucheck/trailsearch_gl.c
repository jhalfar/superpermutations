/* trailsearch_gl.c = trailsearch_fast.c (trailsearch with --set, --setpar, --write-better-only and a faster load)
   + option --gpuload: the word pass, the trail
   windows, the plan check and the coverage check of the written word run on the card (tsgl.cu -> tsgl.ptx next to
   the program; build: gcc -O2 -mpopcnt -fopenmp -o trailsearch_gl trailsearch_gl.c -lm).  Without --gpuload it is
   trailsearch_fast.  With it the pieces, duplicate windows, cuts, plans and words are the same (see README.md).

   trailsearch.c - local search over the closed trails of a word of Jay Pantone's construction, and the program
   that rebuilds a word from a plan.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   What it does.  The input word is split into its closed trails (cyclic words of length R_T).  A word of the same
   trails is a sequence of pieces: every trail is written once, cut open at one of its cuts, and consecutive pieces
   are joined with the largest overlap of their ends.  Cutting trail T between the consecutive permutation windows
   p_i and p_i+1, which lie g letters apart, writes a piece of R_T + n - g letters that starts with the first
   h = n - 3 letters of p_i+1 (S) and ends with the last h letters of p_i (E).  Joining piece A to piece B costs
   d(E_A, S_B) = h minus the largest overlap of the two h-words.  The length of the word is
       L = h + sum of R_T + sum of the costs of the cuts (3 - g) + sum of d over the joins.
   The search removes a few trails from the sequence and puts each back at its best place with its best cut, and
   accepts the result by the rule of simulated annealing.  A small trail may also be put back as two segments around
   a block of other pieces.  If a permutation occurs twice in the trails, a cut may drop one of the two occurrences.

   The best sequence is written as OUT.txt and as a plan, OUT.txt.plan: one line per piece (P k: piece k of the input
   word as it is; O t start g g1: trail t cut at offset start with gap g, g1 > 0 if an occurrence is dropped;
   S t start len: len letters of trail t from offset start).  A plan refers to the word it was made from.

   Checks.  A plan read with --plan-in is used only if every permutation of the input word lies inside one of its
   events.  A permutation that only forms across a join (word2plan: "NOT safe to search from") is lost when the join
   changes, so such a plan is refused with exit code 4 if the run can change the sequence (--time > 0); with
   --time 0 alone the word of the plan is only rebuilt, with a warning.  Every word is checked while it is written:
   if it has fewer distinct permutations than the input word, it is kept as OUT.txt.rejected, OUT.txt and
   OUT.txt.plan are not written, and the exit code is 4.

   Build:  gcc -O2 -mpopcnt -fopenmp -o trailsearch trailsearch.c -lm
   Rebuild a word from a plan (no search):
           trailsearch BASE.txt OUT.txt --plan-in PLAN --time 0
   Search: trailsearch BASE.txt OUT.txt [--plan-in PLAN] --time SEC --seed S --kmax 10 --T0 0.3 --threads T
                       --sync 120 [--focus 0.9]

   Options.
     --time SEC     seconds of search (default 600; 0: only load, write the word and the plan)
     --iters N      stop after N iterations per thread (one thread and a very large --time make a run repeatable:
                    the temperature depends on the clock only through --time)
     --seed S       random seed
     --kmax K       at most K trails are removed in one iteration (default 6; I used 8 to 12)
     --T0 TEMP      start temperature in letters (default 1.5; I used 0.3 to 0.6); it falls linearly with the time
     --threads T    T independent searches on the shared model with temperatures 0.5 to 1.5 times TEMP
     --sync SEC     every SEC seconds the odd-numbered threads restart from the best sequence found so far
     --focus P      a trail is big if it has more than 3000 cuts (--bigcuts); with probability P an iteration that
                    would move no big trail is skipped (0.8 to 0.9 for n = 12 and n = 13, where only big trails
                    ever gave a gain)
     --bigp P       a big trail stays in the removal set only with probability P
     --plan-in F    start from plan F instead of the input word as it is
     --ckpt SEC     the plan of the best sequence is written every SEC seconds (default 600)
     --noskip       no cut drops an occurrence;  --nosplit  no trail is written as two segments
   Limits (these were constants; the defaults are the old values and give the same words):
     --splitmax C   only a trail with at most C cuts may be written as two segments (default 3000)
     --split-cands M  at most M free cuts of the trail are tried as the inner cut of a split (default 400)
     --split-pairs M  of the (block start, block end) pairs of a split, the M cheapest are tried (default 64)
     --bigcuts C    a trail with more than C cuts is big, for --focus, --bigp and the related-run step
                    (default 3000)
     --runcap R     a run of more than R events is never removed as a whole, only a window of it
                    (default 0: 2 kmax + 2)
     --relmax M     runs related to the removed run are looked for only if its trails have at most M cuts
                    in all (default 600000)
     --mincut G     cuts at steps of weight >= G are offered (default 2; with 1 also the cuts inside a
                    1-cycle, 2 letters each, which multiplies the number of cuts by about 8)
     --gpuload      (trailsearch_gl) the bitmap passes of the load on the card; about 2.6 GB on it at n = 13

   Memory and time.  A cut is stored in 6 bytes and its words are read from the trail when they are needed.
   n = 11: 2,800 trails, 3.7 million cuts, 90 MB with one search thread, loads in 3 seconds.  n = 12: 25,200
   trails, 40 million cuts, 0.8 GB for a rebuild, loads in 13 seconds on 8 threads.  n = 13: 252,000 trails,
   482 million cuts, about 11 GB and 0.45 GB more per search thread, loads in about 5 minutes.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.

   Where the parts start.  Each part begins with a comment line of dashes, in this order: h-words; trails; options
   (the table of cuts); events; output (word and plan); hash multimap; one search thread (nodes, index, loading a
   sequence); what the search keeps about the sequence between iterations; best insertion of a trail; insertion
   as two segments; statistics; the shared best sequence and the search loop; loading the word; main.
   recut.c, relocate.c, segins.c, trailsearch_gpu.c and recut_wide.c are copies of this file with parts added.
   What is said here about the model, the plan and the search holds for all of them.

   This file replaces the first published version of trailsearch.c.  It is the same search (same random numbers and
   the same sequence after every iteration, so the same command with one thread writes the same plan) and about four
   times faster, by these changes:
     * the runs related to a removed trail are found through the index (mark_near) instead of a table over all runs;
     * the greedy repair keeps, per pending trail, the list of places it looked at (Vis, VC) and patches it after
       each insertion (vc_update) instead of scanning again; the removal step records these lists (vc_get);
     * best_split caches the end words and stops early;
     * an h-word is packed with one 8-byte load (pack8);
     * a node that is dead for good leaves the index (h_del, index_del, Node.ent);
     * the arrays that describe the sequence are kept between iterations and patched after an accepted move
       (seq_build, seq_patch), and the length is kept by differences.
   What a change to this file must keep if the search is to stay identical:
     * a new index entry goes to the head of its chain and h_del keeps the order of the others;
     * index_del uses the keys of index_add in the same order; H.n is never reduced, so rebuilds happen when they did;
     * order / cand, the trail chains (thead, tnx) and skp describe the sequence between iterations: seq_build after
       every load, seq_patch after an accepted move; a rejected move must restore the list, the chains and skp
       exactly, and every node that enters the list must go through node_insert_after (-DTS_CHECK=2 checks all of
       it and the length at every iteration);
     * visit lists live for one iteration and never see index_del or ctx_load. */
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
#include "gp_cuda.h" /* --gpuload */
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
#define NL "\n"
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

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
#if defined(__BYTE_ORDER__) && __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
/* 8 symbols packed with one 8-byte load (all buffers have 16 spare bytes at the end) */
static inline u64 pack8(const unsigned char *p) {
    u64 x;
    memcpy(&x, p, 8);
    x = __builtin_bswap64(x) & 0x0F0F0F0F0F0F0F0FULL;
    x = (x | (x >> 4)) & 0x00FF00FF00FF00FFULL;
    x = (x | (x >> 8)) & 0x0000FFFF0000FFFFULL;
    return (x | (x >> 16)) & 0xFFFFFFFFULL;
}
static inline u64 hw_lin(const unsigned char *p) {
    return h <= 8 ? pack8(p) >> (4 * (8 - h)) : (pack8(p) << (4 * (h - 8))) | (pack8(p + h - 8) & HMASK[h - 8]);
}
#else
static inline u64 hw_lin(const unsigned char *p) {
    u64 v = 0;
    for (int k = 0; k < h; k++)
        v = (v << 4) | p[k];
    return v;
}
#endif
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
} Ev;
/* EV_PIECE: a = piece index.  EV_OPT: a = option.  EV_SEG: a = start offset in the trail, l letters. */
static i64 *PS, *PL;
static i64 NP; /* pieces of the input word */

/* Length of the word of a sequence: the letters of all events minus the overlaps at the joins. */
static i64 seq_length(const Ev *ev, i64 N) {
    i64 len = 0;
    for (i64 i = 0; i < N; i++)
        len += ev[i].l;
    for (i64 i = 0; i + 1 < N; i++)
        len -= h - dist(ev[i].e, ev[i + 1].s);
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
    return x;
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
    e2->kind = EV_SEG;
    e2->t = t;
    e2->s = oS(c2);
    e2->e = oE(c1);
    e2->l = l2;
    e2->a = st2;
    e2->skip = -1;
}

/* ---------- coverage: the permutations a word really contains, as a bitmap of n! bits indexed by rank.  The model
   keeps a permutation only if it lies inside an event; one that only forms across a join is lost when the join
   changes.  So a plan is checked when it is loaded (plan_check) and every word while it is written (write_word). */
static int NTHR;
static i64 base_perms; /* distinct permutations of the input word: no word written may have fewer */
static int prof; /* --prof: phase times on stderr */
static double prof_last;
static double wall(void);
static void PROF(const char *s) {
    if (prof) {
        double t = wall();
        fprintf(stderr, "[prof] %-34s %8.2f s\n", s, t - prof_last);
        fflush(stderr);
        prof_last = t;
    }
}
/* fast: the bitmaps of n! bits (0.78 GB at n = 13) do not fit in the caches, and one atomic operation per window
   waits for its cache line.  So ranks go into a small buffer, the bitmap word of each is prefetched when the rank is
   computed, and the atomic operations run when the buffer is full.  The bits set are the same, so every count is
   the same as before.  dup != NULL: a bit that was already set in seen is also set in dup. */
#define PFB 32
typedef struct {
    u64 r[PFB];
    int k;
} RBuf;
static inline void rb_flush(RBuf *q, u64 *seen, u64 *dup) {
    for (int i = 0; i < q->k; i++) {
        u64 r = q->r[i], bit = 1ULL << (r & 63);
        if (dup) {
            u64 old = __atomic_fetch_or(&seen[r >> 6], bit, __ATOMIC_RELAXED);
            if (old & bit)
                __atomic_fetch_or(&dup[r >> 6], bit, __ATOMIC_RELAXED);
        } else
            __atomic_fetch_or(&seen[r >> 6], bit, __ATOMIC_RELAXED);
    }
    q->k = 0;
}
static inline void rb_push(RBuf *q, u64 r, u64 *seen, u64 *dup) {
    __builtin_prefetch(&seen[r >> 6], 1, 3);
    q->r[q->k++] = r;
    if (q->k == PFB)
        rb_flush(q, seen, dup);
}
/* rank of the n letters at p for a constant NN (the compiler unrolls the loop); same value as rank_lin */
static inline __attribute__((always_inline)) u64 rank_k(const unsigned char *p, const int NN) {
    u64 r = 0;
    int used = 0;
    for (int k = 0; k < NN; k++) {
        int c = p[k];
        r += (u64)(c - __builtin_popcount(used & ((1 << c) - 1))) * fact[NN - 1 - k];
        used |= 1 << c;
    }
    return r;
}
/* marks the permutation windows of the letters p[0 .. len) (windows that start at 0 .. len - n).  A window is a
   permutation iff its n letters are different: `start` is the first position of the longest run of different
   letters that ends at i (the same windows as the letter counts of the first version). */
static inline __attribute__((always_inline)) void windows_k(const unsigned char *p, i64 len, u64 *seen, u64 *dup,
                                                            const int NN) {
    RBuf q;
    q.k = 0;
    i64 last[16], start = 0;
    for (int c = 0; c < 16; c++)
        last[c] = -1;
    for (i64 i = 0; i < len; i++) {
        int c = p[i];
        if (last[c] >= start)
            start = last[c] + 1;
        last[c] = i;
        if (i - start + 1 >= NN)
            rb_push(&q, rank_k(p + i - NN + 1, NN), seen, dup);
    }
    rb_flush(&q, seen, dup);
}
static void windows_add(const unsigned char *p, i64 len, u64 *seen, u64 *dup) {
    switch (n) {
    case 6: windows_k(p, len, seen, dup, 6); break;
    case 7: windows_k(p, len, seen, dup, 7); break;
    case 8: windows_k(p, len, seen, dup, 8); break;
    case 9: windows_k(p, len, seen, dup, 9); break;
    case 10: windows_k(p, len, seen, dup, 10); break;
    case 11: windows_k(p, len, seen, dup, 11); break;
    case 12: windows_k(p, len, seen, dup, 12); break;
    default: windows_k(p, len, seen, dup, 13); break;
    }
}
/* fast: rank_lin and rank_cyc with the loop unrolled for the n of the word (same values) */
static inline u64 rank_sw(const unsigned char *p) {
    switch (n) {
    case 6: return rank_k(p, 6);
    case 7: return rank_k(p, 7);
    case 8: return rank_k(p, 8);
    case 9: return rank_k(p, 9);
    case 10: return rank_k(p, 10);
    case 11: return rank_k(p, 11);
    case 12: return rank_k(p, 12);
    default: return rank_k(p, 13);
    }
}
static inline u64 rank_cyc_sw(const Trail *t, i64 pos) {
    i64 R = t->R;
    pos %= R;
    if (pos < 0)
        pos += R;
    return pos + n <= R ? rank_sw(t->c + pos) : rank_cyc(t, pos);
}
static u64 *cov_alloc(void) {
    u64 *b = calloc((size_t)((fact[n] + 63) / 64), 8);
    if (!b)
        DIE("out of memory (a bitmap of %llu bits for the coverage check)", (unsigned long long)fact[n]);
    return b;
}
static i64 cov_count(const u64 *b) {
    i64 s = 0, m = (i64)((fact[n] + 63) / 64);
    for (i64 i = 0; i < m; i++)
        s += __builtin_popcountll(b[i]);
    return s;
}
/* letter r of event x, as write_word writes it */
static inline unsigned char ev_letter(const Ev *x, i64 r) {
    if (x->kind == EV_PIECE)
        return W[PS[x->a] + r];
    const Trail *t = &TR[x->t];
    i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a;
    return t->c[(st + r) % t->R];
}
/* fast: letters r0 .. r0 + len - 1 of event x (the letters ev_letter gives), copied in blocks */
static void ev_copy(const Ev *x, i64 r0, i64 len, unsigned char *buf) {
    if (x->kind == EV_PIECE) {
        memcpy(buf, W + PS[x->a] + r0, (size_t)len);
        return;
    }
    const Trail *t = &TR[x->t];
    i64 st = x->kind == EV_OPT ? (i64)OP[x->a].start : x->a;
    i64 pos = (st + r0) % t->R;
    while (len > 0) {
        i64 m = t->R - pos;
        if (m > len)
            m = len;
        memcpy(buf, t->c + pos, (size_t)m);
        buf += m;
        len -= m;
        pos = 0;
    }
}
/* marks the permutations in the windows of the word p[0 .. len), in blocks of 64 K letters on NTHR threads */
static void cover_add(const unsigned char *p, i64 len, u64 *b) {
    const i64 CH = 1 << 16;
    i64 nch = (len + CH - 1) / CH;
#pragma omp parallel for schedule(dynamic, 16) num_threads(NTHR)
    for (i64 k = 0; k < nch; k++) {
        i64 a = k * CH, e = (k + 1) * CH + n - 1;
        if (e > len)
            e = len;
        windows_add(p + a, e - a, b, NULL);
    }
}
/* ---------- --gpuload: the bitmap passes of the load on the card (kernels tsgl.cu ->
   tsgl.ptx next to the program).  The word pass, the trail windows, the plan check and the coverage check of the word
   written are the same computations as above, so pieces, duplicate windows, plans and words are the same.  The card
   holds the n!-bit tables and one buffer of GL_CAP letters (one byte each); the host passes the letters through it
   part by part (the word in ranges, the trails and events as runs of letters), so the card adds about 2.6 GB at
   n = 13 and the host about 0.3 GB, while the host's own tables of the passes (1.6 GB at n = 13) are not made. */
static int gpuload;
static void *k_wpass, *k_segwin, *k_rawwin, *k_and;
#define GL_CAP ((u64)256 << 20)
static DP gl_dbuf;            /* GL_CAP + 64 letters on the card */
static unsigned char *gl_hbuf; /* GL_CAP + 64 letters on the host (page-locked) */
static DP gWD;                /* the permutations the word has twice (word pass -> trail windows) */
static void gl_init(const char *argv0) {
    gp_init_ptx(argv0, "tsgl.ptx");
    k_wpass = gp_fn("wpass"); k_segwin = gp_fn("segwin"); k_rawwin = gp_fn("rawwin"); k_and = gp_fn("andbits");
    gl_dbuf = gp_alloc((size_t)GL_CAP + 64, 0);
    if (cMemHostAlloc((void **)&gl_hbuf, (size_t)GL_CAP + 64, 0)) {
        gl_hbuf = malloc((size_t)GL_CAP + 64);
        if (!gl_hbuf) DIE("out of memory");
    }
}
static u64 gl_words(void) { return (u64)((fact[n] >> 6) + 1) * 2; }   /* 32-bit words of an n!-bit table */
static int cmpu64(const void *x, const void *y) { u64 a = *(const u64 *)x, b = *(const u64 *)y; return a < b ? -1 : a > b; }
static unsigned gl_blocks(u64 nthreads_windows, int S, int bt) { return (unsigned)((nthreads_windows + (u64)bt * S - 1) / ((u64)bt * S)); }

/* word pass: base_perms, wd kept on the card (gWD), the pieces PS/PL/NP; returns the number of permutation windows */
static i64 gl_word_pass(void) {
    u64 nw32 = gl_words();
    DP ws = gp_alloc(nw32 * 4, 1); gWD = gp_alloc(nw32 * 4, 1);
    const u64 cap = 1ULL << 23; DP st = gp_alloc(cap * 8, 0), en = gp_alloc(cap * 8, 0), stats = gp_alloc(32, 1);
    u64 Lu = (u64)L, nwin = L >= n ? (u64)L - n + 1 : 0, capv = cap; int S = 32, bt = 256, nn = n;
    const u64 step = GL_CAP - (u64)n - 16;   /* windows per part; the part holds 3 letters before and n + 2 after */
    for (u64 w0 = 0; w0 < nwin; w0 += step) {
        u64 w1 = w0 + step < nwin ? w0 + step : nwin;
        u64 gbase = w0 >= 3 ? w0 - 3 : 0, gend = w1 + 3 + n - 1 < Lu ? w1 + 3 + n - 1 : Lu;
        CK(cHtoD(gl_dbuf, W + gbase, (size_t)(gend - gbase)));
        void *args[] = { &gl_dbuf, &gbase, &Lu, &nn, &S, &w0, &w1, &ws, &gWD, &stats, &st, &en, &capv };
        gp_launch(k_wpass, gl_blocks(w1 - w0, S, bt), bt, 0, args);
        CK(cCtxSync());
    }
    u64 s3[3]; CK(cDtoH(s3, stats, 24));
    if (s3[1] > cap || s3[2] > cap) DIE("--gpuload: more than %llu pieces", (unsigned long long)cap);
    if (s3[1] != s3[2]) DIE("--gpuload: internal error (piece starts %llu, ends %llu)", (unsigned long long)s3[1], (unsigned long long)s3[2]);
    if (!s3[1]) DIE("no permutation in the word");
    u64 K = s3[1], *hs = malloc(K * 8), *he = malloc(K * 8);
    CK(cDtoH(hs, st, K * 8)); CK(cDtoH(he, en, K * 8));
    qsort(hs, K, 8, cmpu64); qsort(he, K, 8, cmpu64);
    NP = (i64)K; PS = malloc((size_t)K * 8 + 8); PL = malloc((size_t)K * 8 + 8);
    for (u64 k = 0; k < K; k++) {
        if (he[k] < hs[k] || (k + 1 < K && he[k] >= hs[k + 1])) DIE("--gpuload: internal error (pieces)");
        PS[k] = (i64)hs[k]; PL[k] = (i64)he[k] + n - (i64)hs[k];
    }
    free(hs); free(he);
    base_perms = (i64)gp_popcount(ws, nw32);
    CK(cMemFree(ws)); CK(cMemFree(st)); CK(cMemFree(en)); CK(cMemFree(stats));
    return (i64)s3[0];
}

/* runs of letters through the buffer: a run of len letters (fetched by a callback) gives its len - n + 1 windows;
   a run longer than the free room is cut into parts that overlap by n - 1 letters, so its windows are counted once */
typedef void (*gl_fetch)(const void *ctx, i64 a, i64 len, unsigned char *dst);
typedef struct { u64 used; i64 ne, cap; u64 *EB, *EP; DP bits, dup, stats; } GlRuns;
static void gl_runs_flush(GlRuns *r) {
    if (!r->ne) return;
    DP dEB = gp_alloc((size_t)r->ne * 8 + 8, 0), dEP = gp_alloc((size_t)(r->ne + 1) * 8, 0);
    CK(cHtoD(gl_dbuf, gl_hbuf, (size_t)r->used));
    CK(cHtoD(dEB, r->EB, (size_t)r->ne * 8)); CK(cHtoD(dEP, r->EP, (size_t)(r->ne + 1) * 8));
    u64 NE = (u64)r->ne, Wtot = r->EP[r->ne]; int nn = n, S = 32, bt = 256;
    void *args[] = { &gl_dbuf, &dEB, &dEP, &NE, &Wtot, &nn, &S, &r->bits, &r->dup, &r->stats };
    if (Wtot) gp_launch(k_segwin, gl_blocks(Wtot, S, bt), bt, 0, args);
    CK(cCtxSync());
    CK(cMemFree(dEB)); CK(cMemFree(dEP));
    r->used = 0; r->ne = 0; r->EP[0] = 0;
}
static void gl_runs_add(GlRuns *r, gl_fetch f, const void *ctx, i64 len) {
    i64 a = 0;
    while (a + n <= len) {
        if (GL_CAP - r->used < (u64)n + 64) gl_runs_flush(r);
        i64 room = (i64)(GL_CAP - r->used), take = len - a < room ? len - a : room;
        f(ctx, a, take, gl_hbuf + r->used);
        if (r->ne + 2 >= r->cap) {
            r->cap = r->cap ? 2 * r->cap : 4096;
            r->EB = realloc(r->EB, (size_t)r->cap * 8); r->EP = realloc(r->EP, (size_t)(r->cap + 1) * 8);
        }
        r->EB[r->ne] = r->used; r->EP[r->ne + 1] = r->EP[r->ne] + (u64)(take - n + 1); r->ne++;
        r->used += (u64)take;
        if (a + take >= len) break;
        a += take - (n - 1);
    }
}
static void gl_runs_init(GlRuns *r, DP bits, DP dup, DP stats) {
    memset(r, 0, sizeof *r); r->bits = bits; r->dup = dup; r->stats = stats;
    r->cap = 4096; r->EB = malloc((size_t)r->cap * 8); r->EP = malloc((size_t)(r->cap + 1) * 8); r->EP[0] = 0;
}
static void gl_runs_free(GlRuns *r) { free(r->EB); free(r->EP); }
/* the letters of a trail as trail_windows reads them: a closed trail is its cyclic word, written out as its R
   letters and then its first n - 1 letters again (R windows); a fixed one is its R + h letters */
static void gl_fetch_trail(const void *ctx, i64 a, i64 len, unsigned char *dst) {
    const Trail *T = ctx;
    if (T->fixed) { memcpy(dst, T->c + a, (size_t)len); return; }
    i64 R = T->R;
    while (len > 0) {
        i64 p = a % R, m = R - p < len ? R - p : len;
        memcpy(dst, T->c + p, (size_t)m);
        dst += m; a += m; len -= m;
    }
}
static void gl_fetch_event(const void *ctx, i64 a, i64 len, unsigned char *dst) { ev_copy((const Ev *)ctx, a, len, dst); }

/* trail windows: seen / dup on the card; returns the number of permutation windows, sets *scount (distinct),
   *dcount (duplicated) and *after (duplicated and twice in the word), and the host table dupb (= dup & wd) */
static i64 gl_trail_windows(u64 *dupb, u64 *scount, u64 *dcount, u64 *after) {
    u64 nw32 = gl_words();
    DP seen = gp_alloc(nw32 * 4, 1), dup = gp_alloc(nw32 * 4, 1), stats = gp_alloc(8, 1);
    GlRuns r; gl_runs_init(&r, seen, dup, stats);
    for (i64 t = 0; t < NT; t++)
        gl_runs_add(&r, gl_fetch_trail, &TR[t], TR[t].fixed ? TR[t].R + h : TR[t].R + n - 1);
    gl_runs_flush(&r); gl_runs_free(&r);
    u64 nwin; CK(cDtoH(&nwin, stats, 8));
    *scount = gp_popcount(seen, nw32); *dcount = gp_popcount(dup, nw32);
    { void *args[] = { &dup, &gWD, &nw32 }; gp_launch(k_and, 4096, 256, 0, args); CK(cCtxSync()); }
    *after = gp_popcount(dup, nw32);
    CK(cDtoH(dupb, dup, nw32 * 4));
    CK(cMemFree(seen)); CK(cMemFree(dup)); CK(cMemFree(gWD)); CK(cMemFree(stats));
    gWD = 0;
    return (i64)nwin;
}
/* plan check on the card: the number of distinct permutations inside the events */
static i64 gl_inside(const Ev *ev, i64 N) {
    u64 nw32 = gl_words(), z = 0;
    DP bits = gp_alloc(nw32 * 4, 1);
    GlRuns r; gl_runs_init(&r, bits, z, z);
    for (i64 i = 0; i < N; i++) gl_runs_add(&r, gl_fetch_event, &ev[i], ev[i].l);
    gl_runs_flush(&r); gl_runs_free(&r);
    i64 inside = (i64)gp_popcount(bits, nw32);
    CK(cMemFree(bits));
    return inside;
}
/* frees the card's buffers (after the plan check: the search needs no card) */
static void gl_release(void) {
    if (gl_dbuf) CK(cMemFree(gl_dbuf));
    gl_dbuf = 0;
}
/* coverage of the word written: a card table and a staging buffer for the blocks of write_word */
static DP gl_wbits, gl_wstg;
static void gl_cover_add(const unsigned char *p, i64 len) {
    if (len < n) return;
    CK(cHtoD(gl_wstg, p, (size_t)len));
    u64 nwin = (u64)(len - n + 1); int nn = n, S = 32, bt = 256;
    void *args[] = { &gl_wstg, &nwin, &nn, &S, &gl_wbits };
    gp_launch(k_rawwin, gl_blocks(nwin, S, bt), bt, 0, args);
}
/* Checks that every permutation of the input word lies inside one event of the loaded plan.  A plan that word2plan
   calls "NOT safe to search from" fails this (windows that lie in a join, segments trimmed at a tight junction).
   refuse: the run can change joins, so it stops with exit code 4; otherwise (a rebuild) only a warning.
   fast: the events are cut into blocks of 64 K windows, so that a long event does not keep one thread busy alone,
   and the letters of a block are copied out of the trail at once instead of one modulo per letter. */
static void plan_check(const Ev *ev, i64 N, int refuse) {
    i64 inside = 0, inside_gpu = -1;
    if (gpuload) /* gpuload: the same windows on the card (TSGL_DEBUG: also on the processor, both counts printed) */
        inside = inside_gpu = gl_inside(ev, N);
    if (!gpuload || getenv("TSGL_DEBUG")) {
    u64 *b = cov_alloc();
    const i64 CH = 1 << 16;
    i64 nb = 0;
    for (i64 i = 0; i < N; i++)
        nb += (ev[i].l + CH - 1) / CH;
    i64 *bi = malloc((size_t)(nb + 1) * 8), *br = malloc((size_t)(nb + 1) * 8);
    nb = 0;
    for (i64 i = 0; i < N; i++)
        for (i64 r0 = 0; r0 < ev[i].l; r0 += CH) {
            bi[nb] = i;
            br[nb++] = r0;
        }
#pragma omp parallel num_threads(NTHR)
    {
        unsigned char *buf = malloc((size_t)CH + 64);
#pragma omp for schedule(dynamic, 16)
        for (i64 k = 0; k < nb; k++) {
            const Ev *x = &ev[bi[k]];
            i64 e = br[k] + CH + n - 1;
            if (e > x->l)
                e = x->l;
            ev_copy(x, br[k], e - br[k], buf);
            windows_add(buf, e - br[k], b, NULL);
        }
        free(buf);
    }
    free(bi);
    free(br);
    inside = cov_count(b);
    if (inside_gpu >= 0) fprintf(stderr, "TSGL_DEBUG: plan check inside: card %lld, processor %lld\n", inside_gpu, inside);
    free(b);
    }
    if (inside >= base_perms) {
        printf("plan check: every permutation of the input word lies inside an event\n");
        fflush(stdout);
        return;
    }
    fprintf(
        stderr,
        "%s: %lld of the %lld permutations of the input word lie only across joins of the plan, not inside an event; a search or pass would lose them.  Convert the word again with word2plan --rebase, or on a base word in the labelling of the word.\n",
        refuse ? "REFUSED" : "WARNING", base_perms - inside, base_perms);
    if (refuse)
        exit(4);
}

/* ---------- output */
/* Writes the word of the sequence.  It goes to path.part first, and the windows of every block of letters are
   checked as the block is written: if the word has fewer distinct permutations than the input word, it is kept as
   path.rejected, nothing is written to path, and the program stops with exit code 4. */
/* fast: returns 4 instead of stopping when the word is refused (the caller stops), and reports to fo */
static int write_word(const Ev *ev, i64 N, const char *path, i64 expect, FILE *fo) {
    char part[4200], rej[4200];
    snprintf(part, sizeof part, "%s.part", path);
    snprintf(rej, sizeof rej, "%s.rejected", path);
    FILE *f = fopen(part, "wb");
    if (!f)
        DIE("cannot write %s", part);
    size_t cap = gpuload ? (size_t)1 << 28 : (size_t)1 << 22, ob = 0; /* gpuload: larger blocks for the card */
    char *out = malloc(cap);
    u64 *bits = gpuload ? NULL : cov_alloc();
    if (gpuload) { gl_wbits = gp_alloc(gl_words() * 4, 1); gl_wstg = gp_alloc(cap + 64, 0); }
    unsigned char *nb =
        malloc(cap + 16); /* the letters of the block as numbers, after the last n - 1 of the one before */
    i64 nbo = 0;
    i64 total = 0;
    u64 tail = 0;
    double tw_io = 0, tw_cov = 0, tw_start = wall();
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
        for (i64 r = skip; r < x->l;) {
            /* fast: the letters of the event are copied in blocks (same letters as ev_letter, one by one) */
            i64 m = x->l - r;
            if (m > (i64)(cap - ob))
                m = (i64)(cap - ob);
            ev_copy(x, r, m, nb + nbo);
            for (i64 j = 0; j < m; j++)
                out[ob + j] = AL[nb[nbo + j]];
            nbo += m;
            ob += m;
            r += m;
            if (ob == cap) {
                double q0 = wall();
                fwrite(out, 1, ob, f);
                tw_io += wall() - q0;
                q0 = wall();
                ob = 0;
                if (gpuload) gl_cover_add(nb, nbo); else cover_add(nb, nbo, bits);
                tw_cov += wall() - q0;
                memmove(nb, nb + nbo - (n - 1), (size_t)n - 1);
                nbo = n - 1;
            }
        }
        total += x->l - skip;
        tail = x->e;
    }
    out[ob++] = '\n';
    fwrite(out, 1, ob, f);
    fclose(f);
    free(out);
    if (gpuload) gl_cover_add(nb, nbo); else cover_add(nb, nbo, bits);
    free(nb);
    i64 got = gpuload ? (i64)gp_popcount(gl_wbits, gl_words()) : cov_count(bits);
    if (gpuload) { CK(cMemFree(gl_wbits)); CK(cMemFree(gl_wstg)); }
    if (prof)
        fprintf(stderr, "[prof]   write_word: fwrite %.2f s, coverage %.2f s, all %.2f s\n", tw_io, tw_cov, wall() - tw_start);
    free(bits); /* NULL with gpuload */
    if (total != expect)
        DIE("internal error: wrote %lld letters, model says %lld", total, expect);
    if (got < base_perms) {
        remove(rej);
        rename(part, rej);
        fprintf(
            stderr,
            "REFUSED: the word of %lld letters has %lld distinct permutations, the input word %lld: %lld are missing.  It is not a superpermutation; it was not written to %s and is kept as %s.\n",
            total, got, base_perms, base_perms - got, path, rej);
        return 4;
    }
    remove(path);
    if (rename(part, path))
        DIE("cannot rename %s to %s", part, path);
    fprintf(fo, "coverage check: %lld distinct permutations, as in the input word\n", got);
    fflush(fo);
    return 0;
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
/* unlinks entry e of an existing key; the other entries keep their order */
static inline void h_del(HTab *H, u64 key, int e) {
    u64 i = hmix(key) & H->mask;
    while (H->t[i].key != key)
        i = (i + 1) & H->mask;
    int *p = &H->t[i].head;
    while (*p != e)
        p = &H->next[*p];
    *p = H->next[e];
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
static double bigp = 1.0;  /* probability of keeping a big trail (more than bigcuts cuts) in the removal set */
static double focus = 0.0; /* probability of skipping an iteration whose removal set has no big trail */
static int kmax = 6, use_skip = 1, use_split = 1, splitmax = 3000, NTHR = 1;
/* limits that were constants (same defaults): --splitmax (above), --split-cands, --split-pairs, --bigcuts,
   --runcap (0: 2 kmax + 2), --relmax; see the Options in the header of trailsearch.c */
static int bigcuts = 3000, splitcands = 400, splitpairs = 64, runcap_opt = 0;
static i64 relmax = 600000;
static int mincut = 2; /* --mincut G: cuts at steps of weight >= G (default 2) */
static u64 seed = 1;
static i64 maxit = -1;

/* ---------- one search thread: the sequence is a doubly linked list of nodes, so an insertion does not renumber
   anything and the hash index (word -> node) is only ever appended to; dead nodes are skipped at lookup and the
   index is rebuilt when it is mostly garbage.  A rejected move is undone by unlinking / relinking nodes. */
/* lab: order label (increasing along the list); ent: its first index entry */
typedef struct {
    Ev v;
    int prev, next, alive, ent;
    u64 lab;
} Node;
typedef struct {
    i64 c2;
    int i, jm;
    i64 cst;
} Pair;
/* visit list of a trail: every (option, key, node) that best_insertion looks at, in the order it looks at them,
   with its cost.  The greedy repair evaluates every pending trail again after each insertion; one insertion changes
   only the visits at the new node and at its two neighbours, so the list is patched and read again (vc_update). */
/* option - olo, node found by key k, cost */
typedef struct {
    u32 oo;
    int x;
    short d;
    unsigned char k;
} Vis;
/* sp / es: first / last h - KLEV symbols of S / E */
typedef struct {
    int ok;
    u32 t;
    Vis *v;
    i64 nv, vcap;
    u32 *sp, *es;
    i64 kcap;
} VC;
/* ok: 0 = empty, 1 = the visits with their costs, 2 = raw: all live nodes found by the keys, recorded before the
   destroy step (the removal selection scans the trails of the chosen run anyway); best_insertion drops what has
   gone since and adds the costs.  Lists belong to trails (vct: trail -> list + 1) for one iteration. */
typedef struct {
    int tid;
    struct Grp *g; /* fast: the set this thread searches for */
    u64 rs[4];
    Node *nd;
    int ncap, nn, first, last;
    i64 N;
    int relabeled;
    HTab H;
    u64 *bf, bfmask;  /* bf: one-hash Bloom filter over the keys of H */
    u32 *mk, mkstamp; /* mark_near: stamp << 2 | bits */
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
    u64 *wS, *wE;
    i64 wcap; /* best_split: S / E of the cuts of the trail */
    char *rem;
    u32 *pend;
    Ev *tmp;
    VC *vc;
    i64 nvc, nvu;
    int *vct;
    Vis *vtmp;
    i64 vtcap;
    i64 cur, best_len, it, acc;
} Ctx;

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
/* Enters node id into the index of the thread: for overlaps h down to h - KLEV the end of its end word and the
   beginning of its start word, and (with two-segment insertion on) the four keys best_split looks up.
   Sets the bits of the Bloom filter.  The keys and their order are what index_del relies on. */
static inline void index_add(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    c->nd[id].ent = (int)c->H.n;
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
/* a node that is dead for good leaves the index (same keys in the same order as index_add; H.n is not reduced, so the
   index is rebuilt at the same moments as without this), so the lists that best_insertion walks hold live nodes only */
static void index_del(Ctx *c, int id) {
    const Ev *x = &c->nd[id].v;
    int e = c->nd[id].ent;
    for (int j = 0; j <= KLEV; j++) {
        h_del(&c->H, HKEY(x->e & HMASK[h - j], j, 0), e++);
        h_del(&c->H, HKEY(x->s >> (4 * j), j, 1), e++);
    }
    if (use_split) {
        h_del(&c->H, HKEY(x->s, 0, 2), e);
        h_del(&c->H, HKEY(x->s >> 4, 1, 2), e + 1);
        h_del(&c->H, HKEY(x->e, 0, 3), e + 2);
        h_del(&c->H, HKEY(x->e & HMASK[h - 1], 1, 3), e + 3);
    }
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
        free(c->mk);
        c->mk = calloc((size_t)need, sizeof(u32));
        c->mkstamp = 0;
        if (!c->mk)
            DIE("out of memory");
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
    seq_build(c);
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
            len -= h - dist(q->v.e, c->nd[q->next].v.s);
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
    c->inslog[c->ninslog++] = id;
    c->N++;
    c->tnx[id] = c->thead[x->t];
    c->thead[x->t] = id;
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
        if (N && dist(nd[c->order[N - 1]].v.e, nd[id].v.s) >= 2)
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
        d -= h - dist(nd[a].v.e, x->v.s);
    if (b >= 0)
        d -= h - dist(x->v.e, nd[b].v.s);
    if (a >= 0 && b >= 0)
        d += h - dist(nd[a].v.e, nd[b].v.s);
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
            if (dist(nd[order[j]].v.e, nd[order[j + 1]].v.s) >= 2) {
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
        if (N && dist(nd[c->order[N - 1]].v.e, nd[id].v.s) >= 2) {
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

/* marks the nodes whose e (bit 1) or s (bit 2) is within one step of S or E of an cut of trail T */
static void mark_near(Ctx *c, const Trail *T) {
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    u32 st = c->mkstamp << 2;
    enum { BATCH = 16 };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 key[BATCH][4], bit[BATCH][4];
        for (int q = 0; q < m; q++) {
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
        for (int q = 0; q < m; q++)
            for (int k = 0; k < 4; k++) {
                if (!((c->bf[bit[q][k] >> 6] >> (bit[q][k] & 63)) & 1))
                    continue;
                for (int e = h_get(H, key[q][k]); e >= 0; e = H->next[e]) {
                    int x = H->val[e];
                    if (!nd[x].alive)
                        continue;
                    if ((c->mk[x] & ~3u) != st)
                        c->mk[x] = st;
                    c->mk[x] |= 1u << (k & 1);
                }
            }
    }
}

/* ---------- best insertion of trail t: insert after node `after` */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
} Ins;
/* Appends one visit (cut, key, node, cost) to a visit list. */
static inline void vis_add(VC *vc, i64 oo, int k, int x, i64 d) {
    if (vc->nv == vc->vcap) {
        vc->vcap = vc->vcap ? vc->vcap * 2 : 4096;
        vc->v = realloc(vc->v, (size_t)vc->vcap * sizeof(Vis));
    }
    Vis *p = &vc->v[vc->nv++];
    p->oo = (u32)oo;
    p->k = (unsigned char)k;
    p->x = x;
    p->d = (short)d;
}
/* the list of trail t; make: start one if there is none */
static VC *vc_get(Ctx *c, u32 t, int make) {
    if (c->vct[t])
        return &c->vc[c->vct[t] - 1];
    if (!make)
        return NULL;
    if (c->nvu == c->nvc) {
        i64 m = c->nvc ? 2 * c->nvc : 64;
        c->vc = realloc(c->vc, (size_t)m * sizeof(VC));
        memset(c->vc + c->nvc, 0, (size_t)(m - c->nvc) * sizeof(VC));
        c->nvc = m;
    }
    VC *vc = &c->vc[c->nvu++];
    vc->t = t;
    vc->ok = 0;
    c->vct[t] = (int)c->nvu;
    return vc;
}
/* vc != NULL: the visits are recorded in vc, or read from it if it is up to date (same result, same random numbers);
   raw: only record the nodes found (nothing is evaluated, no random numbers are used) */
static Ins best_insertion(Ctx *c, u32 t, double noise, VC *vc, int raw) {
    Ins best;
    best.val = 1e18;
    best.delta = 0;
    best.after = -1;
    best.opt = -1;
    const Trail *T = &TR[t];
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    if (vc && vc->ok == 2) {
        i64 m = 0, cur = -1;
        int skbad = 0;
        u64 S = 0, E = 0;
        for (i64 i = 0; i < vc->nv; i++) {
            Vis *p = &vc->v[i];
            int x = p->x, a, b2;
            i64 o = T->olo + p->oo;
            if (!nd[x].alive)
                continue;
            if (!(p->k & 1)) {
                a = x;
                b2 = nd[x].next;
            } else {
                b2 = x;
                a = nd[x].prev;
            }
            if (a < 0 || b2 < 0)
                continue;
            if ((i64)p->oo != cur) {
                cur = p->oo;
                skbad = OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o));
                S = oS_t(T, o);
                E = oE_t(T, o);
            }
            if (skbad)
                continue;
            p->d = (short)(dist(nd[a].v.e, S) + oD(o) + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s));
            vc->v[m++] = *p;
        }
        vc->nv = m;
        vc->ok = 1;
    }
    if (vc && vc->ok) {
        for (i64 i = 0; i < vc->nv; i++) {
            const Vis *p = &vc->v[i];
            double v = (double)p->d + (noise > 0 ? noise * rndu(c) : 0.0);
            if (v < best.val) {
                best.val = v;
                best.delta = p->d;
                best.after = (p->k & 1) ? nd[p->x].prev : p->x;
                best.opt = T->olo + p->oo;
            }
        }
        goto done;
    }
    if (vc) {
        vc->nv = 0;
        vc->ok = 1;
        if (T->ohi - T->olo > vc->kcap) {
            vc->kcap = T->ohi - T->olo + 1024;
            free(vc->sp);
            free(vc->es);
            vc->sp = malloc((size_t)vc->kcap * sizeof(u32));
            vc->es = malloc((size_t)vc->kcap * sizeof(u32));
        }
    }
    /* options are processed in batches so that the filter words of a whole batch are prefetched before they are tested */
    enum { BATCH = 16, NK = 2 * (KLEV + 1) };
    for (i64 o0 = T->olo; o0 < T->ohi; o0 += BATCH) {
        int m = (int)(T->ohi - o0 < BATCH ? T->ohi - o0 : BATCH);
        u64 Sb[BATCH], Eb[BATCH], key[BATCH][NK], bit[BATCH][NK];
        for (int q = 0; q < m; q++) {
            u64 S = oS_t(T, o0 + q), E = oE_t(T, o0 + q);
            Sb[q] = S;
            Eb[q] = E;
            if (vc) {
                vc->sp[o0 + q - T->olo] = (u32)(S >> (4 * KLEV));
                vc->es[o0 + q - T->olo] = (u32)(E & HMASK[h - KLEV]);
            }
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
                    if (raw) {
                        vis_add(vc, o - T->olo, k, x, 0);
                        continue;
                    }
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
                    i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s);
                    double v = (double)d + (noise > 0 ? noise * rndu(c) : 0.0);
                    if (v < best.val) {
                        best.val = v;
                        best.delta = d;
                        best.after = a;
                        best.opt = o;
                    }
                    if (vc)
                        vis_add(vc, o - T->olo, k, x, d);
                }
            }
        }
    }
    if (raw) {
        vc->ok = 2;
        return best;
    }
done:
    if (best.after < 0) { /* nothing overlaps: append with the cheapest cut */
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

/* node id has just been inserted: bring the lists of the pending trails pend[0 .. np-1] (except pick) up to date */
static void vc_update(Ctx *c, int id, i64 pick, i64 np) {
    const Node *nd = c->nd;
    const Ev *x = &nd[id].v;
    int a = nd[id].prev, b = nd[id].next;
    u32 ts[KLEV + 1], te[KLEV + 1]; /* a match at level j needs sp == ts[j] (kind 0) or es == te[j] (kind 1) */
    for (int j = 0; j <= KLEV; j++) {
        ts[j] = (u32)((x->e >> (4 * (KLEV - j))) & HMASK[h - KLEV]);
        te[j] = (u32)((x->s >> (4 * j)) & HMASK[h - KLEV]);
    }
    for (i64 q = 0; q < np; q++) {
        VC *vc = q == pick ? NULL : vc_get(c, c->pend[q], 0);
        if (!vc || !vc->ok)
            continue;
        int rawl = vc->ok == 2;
        if (b < 0 && !rawl) {
            vc->ok = 0;
            continue;
        } /* appended: the old last node becomes a position; scan again */
        const Trail *T = &TR[c->pend[q]];
        i64 no = T->ohi - T->olo, m = 0;
        /* the visits found through a (by its e) and through b (by its s) now have the new node on the other side;
           options that skip the window the new piece skips are no longer allowed */
        for (i64 i = 0; i < vc->nv && !rawl; i++) {
            Vis *p = &vc->v[i];
            i64 o = T->olo + p->oo;
            if (x->skip >= 0 && OP[o].g1 && oSK_t(T, o) == x->skip)
                continue;
            if ((p->x == a && !(p->k & 1)) || (p->x == b && (p->k & 1))) {
                u64 S = oS_t(T, o), E = oE_t(T, o), ea = (p->k & 1) ? x->e : nd[a].v.e,
                    sb = (p->k & 1) ? nd[b].v.s : x->s;
                p->d = (short)(dist(ea, S) + oD(o) + dist(E, sb) - dist(ea, sb));
            }
            vc->v[m++] = *p;
        }
        if (!rawl)
            vc->nv = m;
        /* visits at the new node: it is the newest entry of its keys, so it comes first among equal (option, key) */
        i64 nw = 0, i = 0;
        if (vc->nv + 2 * (KLEV + 1) * 64 > c->vtcap) {
            c->vtcap = 2 * vc->nv + 65536;
            free(c->vtmp);
            c->vtmp = malloc((size_t)c->vtcap * sizeof(Vis));
        }
        for (i64 o0 = 0; o0 < no; o0 += 64) {
            i64 o1 = o0 + 64 < no ? o0 + 64 : no;
            int hit = 0;
            for (i64 oo = o0; oo < o1; oo++) {
                u32 sp = vc->sp[oo], es = vc->es[oo];
                for (int j = 0; j <= KLEV; j++)
                    hit |= (sp == ts[j]) | (es == te[j]);
            }
            if (!hit)
                continue;
            for (i64 oo = o0; oo < o1; oo++) {
                u32 sp = vc->sp[oo], es = vc->es[oo];
                int any = 0;
                for (int j = 0; j <= KLEV; j++)
                    any |= (sp == ts[j]) | (es == te[j]);
                if (!any)
                    continue;
                i64 o = T->olo + oo;
                u64 S = oS_t(T, o), E = oE_t(T, o);
                int skchecked = 0;
                for (int k = 0; k < 2 * (KLEV + 1); k++) {
                    int j = k >> 1;
                    if (!(k & 1) ? (S >> (4 * j)) != (x->e & HMASK[h - j]) : (E & HMASK[h - j]) != (x->s >> (4 * j)))
                        continue;
                    if (!rawl && !skchecked) {
                        skchecked = 1;
                        if (OP[o].g1 && c->nskp && skp_has(c, oSK_t(T, o)))
                            break;
                    }
                    while (i < vc->nv && (vc->v[i].oo < (u32)oo || (vc->v[i].oo == (u32)oo && vc->v[i].k < k)))
                        c->vtmp[nw++] = vc->v[i++];
                    Vis *p = &c->vtmp[nw++];
                    p->oo = (u32)oo;
                    p->k = (unsigned char)k;
                    p->x = id;
                    p->d = 0;
                    if (!rawl) {
                        u64 ea = (k & 1) ? nd[a].v.e : x->e, sb = (k & 1) ? x->s : nd[b].v.s;
                        p->d = (short)(dist(ea, S) + oD(o) + dist(E, sb) - dist(ea, sb));
                    }
                }
            }
            if (nw + (vc->nv - i) + 2 * (KLEV + 1) * 64 > c->vtcap) {
                c->vtcap = 2 * (nw + vc->nv) + 65536;
                c->vtmp = realloc(c->vtmp, (size_t)c->vtcap * sizeof(Vis));
            }
        }
        if (!nw)
            continue;
        while (i < vc->nv)
            c->vtmp[nw++] = vc->v[i++];
        if (nw > vc->vcap) {
            vc->vcap = nw + nw / 2;
            free(vc->v);
            vc->v = malloc((size_t)vc->vcap * sizeof(Vis));
        }
        memcpy(vc->v, c->vtmp, (size_t)nw * sizeof(Vis));
        vc->nv = nw;
    }
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
                i64 cst = dvi + dist(nd[jm].v.e, v) - dist(nd[nd[i].prev].v.e, nd[i].v.s) -
                          dist(nd[jm].v.e, nd[nd[jm].next].v.s);
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
    if (np > splitpairs)
        np = splitpairs;
    i64 bd = 1LL << 40, bk = -1, bc1 = -1, no = T->ohi - T->olo, dmin = 1 << 20;
    if (no > c->wcap) {
        c->wcap = no + 1024;
        free(c->wS);
        free(c->wE);
        c->wS = malloc((size_t)c->wcap * 8);
        c->wE = malloc((size_t)c->wcap * 8);
    }
    for (i64 q = 0; q < no; q++) {
        c->wS[q] = oS_t(T, T->olo + q);
        c->wE[q] = oE_t(T, T->olo + q);
        if (oD(T->olo + q) < dmin)
            dmin = oD(T->olo + q);
    }
    for (i64 k = 0; k < np; k++) {
        if (c->pr[k].cst + dmin >= bd)
            break; /* pr is sorted by cst and an cut adds at least dmin */
        u64 ep = nd[nd[c->pr[k].i].prev].v.e, sn = nd[nd[c->pr[k].jm].next].v.s;
        for (i64 q = 0; q < no; q++) {
            i64 d = dist(ep, c->wS[q]) + oD(T->olo + q) + dist(c->wE[q], sn) + c->pr[k].cst;
            if (d < bd) {
                bd = d;
                bk = k;
                bc1 = T->olo + q;
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

/* ---------- what the sequence looks like: cuts by kind, joins by cost, runs (maximal chains of joins of cost <= 1) */
static void print_stats(const Ev *ev, i64 N, FILE *fo) { /* fast: to the log of the set */
    i64 g2 = 0, g1 = 0, skips = 0, segs = 0, pieces = 0, hist[17] = {0}, runs = 1, inter = 0, inrun = 0, extra = 0;
    for (i64 i = 0; i < N; i++) {
        if (ev[i].kind == EV_SEG)
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
            int d = dist(ev[i].e, ev[i + 1].s);
            hist[d]++;
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
    fprintf(fo, 
        "stats: events %lld (unchanged pieces %lld, segments %lld), gap-2 openings %lld, gap-1 openings %lld, duplicate-skip openings %lld, opening cost %lld" NL,
        N, pieces, segs, g2, g1, skips, extra);
    fprintf(fo, "stats: runs %lld, join cost between runs %lld, joins inside runs cost %lld; joins by cost:", runs, inter,
           inrun);
    for (int d = 0; d <= h; d++)
        if (hist[d])
            fprintf(fo, " %d:%lld", d, hist[d]);
    fprintf(fo, NL);
    fflush(fo);
}

/* fast: frees a search thread's memory, so that the sets of the next wave (--setpar) do not add to it */
static void ctx_free(Ctx *c) {
    void *p[] = {c->nd,   c->order, c->cand, c->tnx,  c->wk,  c->wc,   c->rel,   c->remlog, c->inslog,
                 c->tmp,  c->mk,    c->bf,   c->H.t,  c->H.next, c->H.val, c->thead, c->rth, c->rk,
                 c->iv,   c->skp,   c->vid,  c->pr,   c->Ib,  c->Jb,   c->wS,    c->wE,     c->rem,
                 c->pend, c->vct,   c->vtmp};
    for (size_t k = 0; k < sizeof p / sizeof p[0]; k++)
        free(p[k]);
    for (i64 q = 0; q < c->nvc; q++) {
        free(c->vc[q].v);
        free(c->vc[q].sp);
        free(c->vc[q].es);
    }
    free(c->vc);
    free(c);
}

/* ---------- shared best sequence
   fast: one per setting (Grp).  Without --set there is one setting, the options of the command line, and the run is
   the run of the first version.  With --set OUT:KMAX:T0:SEED (several times) the model is loaded once and every set
   is a search of its own on its own threads, as if it were a separate run with those options: its best sequence,
   start time, iteration counts, log (OUT.log) and outputs (OUT, OUT.plan). */
typedef struct Grp {
    Ev *ev;
    i64 N, len, len0;
    int dirty;
    double t0, last_ck, last_log;
    i64 it[256];
    int kmax, nthr;
    double T0;
    u64 seed;
    char out[4096], outplan[4200];
    FILE *log;
} Grp;
static double wall(void);

/* One search thread.  Until the time or the iteration limit: choose trails to remove, take them out, put each
   back (greedy order or random order, with or without noise), accept or undo by the annealing rule.  A new best
   sequence goes to the shared copy G_ev under the lock gbest; odd threads adopt the shared best at sync time. */
#define G_ev (g->ev)
#define G_N (g->N)
#define G_len (g->len)
#define G_dirty (g->dirty)
#define G_t0 (g->t0)
#define G_last_ck (g->last_ck)
#define G_last_log (g->last_log)
#define G_it (g->it)
static void search(Ctx *c, const Ev *init_ev, i64 initN) {
    Grp *g = c->g; /* fast: the settings of this thread's set shadow the global ones of the same name */
    const int kmax = g->kmax, NTHR = g->nthr;
    const double T0 = g->T0;
    const u64 seed = g->seed;
    const char *outplan = g->outplan;
    FILE *glog = g->log;
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->rem = calloc((size_t)NT + 1, 1);
    c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    c->vct = calloc((size_t)NT + 1, sizeof(int));
    c->thead = malloc(((size_t)NT + 1) * sizeof(int));
    c->rth = malloc(((size_t)NT + 1) * 2 * sizeof(int));
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c);
    c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = runcap_opt > 0 ? runcap_opt : 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
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
        for (i64 q = 0; q < c->nvu; q++)
            c->vct[c->vc[q].t] = 0;
        c->nvu = 0;
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
                int nrel = 0;
                if (nopt <= relmax) {
                    /* the index of the sequence already knows which nodes are within one step of an cut */
                    if (++c->mkstamp >> 30) {
                        memset(c->mk, 0, (size_t)c->ncap * sizeof(u32));
                        c->mkstamp = 1;
                    }
                    u32 st = c->mkstamp << 2;
                    for (int i = RS(X); i <= RE(X); i++) {
                        u32 t_ = EVT(i).t;
                        const Trail *T = &TR[t_];
                        if (T->fixed || c->vct[t_])
                            continue;
                        if (bigp < 0.5 && T->ohi - T->olo > bigcuts) {
                            mark_near(c, T);
                            continue;
                        } /* likely to be kept out of the removal set */
                        VC *vc = vc_get(c, t_, 1);
                        best_insertion(c, t_, 0.0, vc, 1); /* the full scan, kept for the repair step */
                        for (i64 q = 0; q < vc->nv; q++)
                            if (vc->v[q].k < 4) {
                                int x = vc->v[q].x;
                                if ((c->mk[x] & ~3u) != st)
                                    c->mk[x] = st;
                                c->mk[x] |= 1u << (vc->v[q].k & 1);
                            }
                    }
                    for (int r = 0; r < nrun; r++) {
                        if (r == X || RE(r) - RS(r) + 1 > runcap)
                            continue;
                        if (c->mk[order[RE(r)]] == (st | 1) || c->mk[order[RE(r)]] == (st | 3) ||
                            (c->mk[order[RS(r)]] & ~1u) == (st | 2))
                            rel[nrel++] = r;
                    }
                }
                for (int i = RS(X); i <= RE(X); i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), r = rel[z];
                    rel[z] = rel[--nrel];
                    for (int i = RS(r); i <= RE(r); i++)
                        REMOVE(EVT(i).t);
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
                int big = TR[t_].ohi - TR[t_].olo > bigcuts;
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
            int uvc = greedy && np > 1; /* new visit lists pay only if trails are evaluated more than once */
            while (np > 0) {
                i64 pick = 0;
                Ins bi = best_insertion(c, c->pend[0], noise, vc_get(c, c->pend[0], uvc), 0);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) {
                        Ins x = best_insertion(c, c->pend[q], noise, vc_get(c, c->pend[q], uvc), 0);
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
                    sp = best_split(c, t, splitcands);
                if (sp.ok && (double)sp.delta < bi.val) {
                    Ev e1, e2;
                    seg_events(sp.c1, sp.c2, &e1, &e2);
                    int id = node_insert_after(c, c->nd[sp.i].prev, &e1);
                    dl += node_len(c, id);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
                    id = node_insert_after(c, sp.jm, &e2);
                    dl += node_len(c, id);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
                } else {
                    Ev x = make_event(bi.opt);
                    int id = node_insert_after(c, bi.after, &x);
                    dl += node_len(c, id);
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                    if (c->nvu)
                        vc_update(c, id, pick, np);
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
            if (c->relabeled)
                seq_build(c);
            else
                seq_patch(c, N, nn0);
            for (int q = 0; q < c->nremlog; q++)
                index_del(c, c->remlog[q]);
            if (nl < c->best_len) {
                c->best_len = nl;
#pragma omp critical(gbest)
                if (nl < G_len) {
                    fprintf(glog, "t=%.0fs: best %lld -> %lld (thread %d, it %lld, removed %lld trails, %lld big)\n",
                           wall() - G_t0, G_len, nl, c->tid, c->it, nrem, nbig);
                    fflush(glog);
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
                            fprintf(glog, "it %lld t=%.0fs best %lld (thread 0: cur %lld)\n", tot, tn - G_t0, G_len, c->cur);
                            fflush(glog);
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
#ifdef TS_CHECK
    {
        u64 hsh = 0;
        for (int id = c->first; id >= 0; id = c->nd[id].next) {
            const Ev *x = &c->nd[id].v;
            hsh = hmix(hsh ^ ((u64)x->kind << 60) ^ ((u64)x->t << 36) ^ (u64)x->a) + (u64)x->l;
        }
#pragma omp critical(gbest)
        {
            fprintf(glog,
                "STATE it %lld cur %lld best %lld acc %lld N %lld seq %016llx rng %016llx %016llx %016llx %016llx" NL,
                c->it, c->cur, c->best_len, c->acc, c->N, hsh, c->rs[0], c->rs[1], c->rs[2], c->rs[3]);
            fflush(glog);
        }
    }
#endif
}

#undef G_ev
#undef G_N
#undef G_len
#undef G_dirty
#undef G_t0
#undef G_last_ck
#undef G_last_log
#undef G_it
/* ---------- loading */
/* fast: one thread's share of the word pass in main: windows a .. b - 1 of the word W */
typedef struct {
    i64 first, last, nw, nb, cap;
    i64 *bk; /* breaks: pairs (previous window, window) of consecutive permutation windows at distance >= 4 */
} WPart;
static inline __attribute__((always_inline)) void word_pass_k(i64 a, i64 b, u64 *ws, u64 *wd, WPart *z,
                                                              const int NN) {
    RBuf q;
    q.k = 0;
    i64 last[16], start = a, prev = -1, e = b + NN - 1;
    for (int c = 0; c < 16; c++)
        last[c] = -1;
    for (i64 i = a; i < e; i++) {
        int c = W[i];
        if (last[c] >= start)
            start = last[c] + 1;
        last[c] = i;
        if (i - start + 1 >= NN) {
            i64 p = i - NN + 1;
            z->nw++;
            rb_push(&q, rank_k(W + p, NN), ws, wd);
            if (prev < 0)
                z->first = p;
            else if (p - prev >= 4) {
                if (z->nb == z->cap) {
                    z->cap = z->cap ? 2 * z->cap : 1024;
                    z->bk = realloc(z->bk, (size_t)z->cap * 16);
                }
                z->bk[2 * z->nb] = prev;
                z->bk[2 * z->nb + 1] = p;
                z->nb++;
            }
            prev = p;
        }
    }
    rb_flush(&q, ws, wd);
    z->last = prev;
}
static void word_pass(i64 a, i64 b, u64 *ws, u64 *wd, WPart *z) {
    switch (n) {
    case 6: word_pass_k(a, b, ws, wd, z, 6); break;
    case 7: word_pass_k(a, b, ws, wd, z, 7); break;
    case 8: word_pass_k(a, b, ws, wd, z, 8); break;
    case 9: word_pass_k(a, b, ws, wd, z, 9); break;
    case 10: word_pass_k(a, b, ws, wd, z, 10); break;
    case 11: word_pass_k(a, b, ws, wd, z, 11); break;
    case 12: word_pass_k(a, b, ws, wd, z, 12); break;
    default: word_pass_k(a, b, ws, wd, z, 13); break;
    }
}
static int load_max; /* fast: the largest letter of the word, found by load_word */
static const char *setspec[64]; /* fast: --set OUT:KMAX:T0:SEED */
static int nsets, setpar, write_better;
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
    /* fast: mapped on NTHR threads, and the largest letter found at the same time (load_max) */
    int bad = 0, mx = 0;
#pragma omp parallel for schedule(static) num_threads(NTHR) reduction(| : bad) reduction(max : mx)
    for (i64 i = 0; i < got; i++) {
        int v = map[w[i]];
        bad |= v < 0;
        v &= 15;
        mx = v > mx ? v : mx;
        w[i] = (unsigned char)v;
    }
    if (bad)
        DIE("bad symbol in %s", path);
    load_max = mx;
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
/* fast: the first call (out == NULL, counting) also lists in *hv_ the windows i whose next window i + 1 is a
   duplicate permutation (ranks prefetched in blocks); the second call (writing) uses the list instead of ranking
   every window again. */
static i64 trail_options(i64 t, i64 *wp, const u64 *dupb, Opt *out, i64 *hist, i64 *shist, i64 **hv_, i64 *nh_) {
    if (TR[t].fixed)
        return 0;
    i64 R = TR[t].R, m = trail_windows(&TR[t], wp), k = 0;
    if (!out && use_skip && m >= 3) {
        u64 rr[32];
        i64 nh = 0, caph = 0, *hv = NULL;
        for (i64 i0 = 0; i0 < m; i0 += 32) {
            int kk = m - i0 < 32 ? (int)(m - i0) : 32;
            for (int j = 0; j < kk; j++) {
                i64 i1 = i0 + j + 1 == m ? 0 : i0 + j + 1;
                rr[j] = rank_cyc_sw(&TR[t], wp[i1]);
                __builtin_prefetch(&dupb[rr[j] >> 6], 0, 3);
            }
            for (int j = 0; j < kk; j++)
                if ((dupb[rr[j] >> 6] >> (rr[j] & 63)) & 1) {
                    if (nh == caph) {
                        caph = caph ? 2 * caph : 64;
                        hv = realloc(hv, (size_t)caph * 8);
                    }
                    hv[nh++] = i0 + j;
                }
        }
        *hv_ = hv;
        *nh_ = nh;
    }
    const i64 *hv = *hv_;
    i64 nh = *nh_, hp = 0;
    for (i64 i = 0; i < m && m >= 2; i++) {
        i64 i1 = i + 1 == m ? 0 : i + 1, i2 = i1 + 1 == m ? 0 : i1 + 1;
        i64 g = (wp[i1] - wp[i] + R) % R;
        if (g >= mincut) {
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
            if (hp < nh && hv[hp] == i) {
                hp++;
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
        DIE("usage: trailsearch WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip] [--nosplit] [--plan-in FILE] [--ckpt SEC] [--iters N] [--threads T] [--sync SEC] [--splitmax C] [--split-cands M] [--split-pairs M] [--bigcuts C] [--runcap R] [--relmax M] [--mincut G]");
    const char *plan_in = NULL;
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
        else if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--nosplit"))
            use_split = 0;
        else if (!strcmp(argv[a], "--splitmax") && a + 1 < argc)
            splitmax = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--split-cands") && a + 1 < argc)
            splitcands = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--split-pairs") && a + 1 < argc)
            splitpairs = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--bigcuts") && a + 1 < argc)
            bigcuts = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--runcap") && a + 1 < argc)
            runcap_opt = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--relmax") && a + 1 < argc)
            relmax = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--gpuload")) /* card load */
            gpuload = 1;
        else if (!strcmp(argv[a], "--prof"))
            prof = 1;
        else if (!strcmp(argv[a], "--set") && a + 1 < argc) {
            if (nsets == 64)
                DIE("at most 64 --set");
            setspec[nsets++] = argv[++a];
        } else if (!strcmp(argv[a], "--setpar") && a + 1 < argc)
            setpar = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--write-better-only"))
            write_better = 1;
        else if (!strcmp(argv[a], "--mincut") && a + 1 < argc)
            mincut = atoi(argv[++a]);
        else
            DIE("unknown option %s", argv[a]);
    }
    if (NTHR < 1 || NTHR > 256)
        DIE("1 to 256 threads");
    double t00 = wall();
    prof_last = t00;
    W = load_word(argv[1], &L);
    PROF("read and map the word");
    int mx = load_max;
    n = mx + 1;
    h = n - 3;
    if (n < 6 || n > 13)
        DIE("6 to 13 symbols");
    for (int k = 0; k <= 16; k++)
        HMASK[k] = k >= 16 ? ~0ULL : ((1ULL << (4 * k)) - 1);
    fact[0] = 1;
    for (int i = 1; i < 17; i++)
        fact[i] = fact[i - 1] * i;
    PROF("max letter");
    /* fast: one parallel pass over the word does three things the first version did in three passes: the bits of
       the permutations of the word (ws, whose count is base_perms, which the words written are checked against),
       the permutations it has twice (wd, used below for the duplicate windows) and the permutation windows that
       split the word into pieces (split at gaps >= 4).  Each thread scans one range of windows and lists its breaks
       (two consecutive permutation windows at distance >= 4); the ranges are then joined in order, which gives the
       pieces of the serial scan. */
    int LT = NTHR > 8 ? NTHR : 8;
    if (LT > omp_get_max_threads())
        LT = omp_get_max_threads();
    u64 *wd_word = gpuload ? NULL : calloc((size_t)(fact[n] >> 6) + 1, 8);
    if (gpuload) { /* gpuload: the same pass on the card; wd stays there until the trail windows */
        gl_init(argv[0]);
        i64 nw = gl_word_pass();
        PROF("word pass (coverage, duplicates, windows)");
        printf("n=%d L=%lld perm windows %lld pieces %lld (%.1fs)\n", n, L, nw, NP, wall() - t00);
        fflush(stdout);
    } else {
        u64 *ws = calloc((size_t)(fact[n] >> 6) + 1, 8);
        if (!ws || !wd_word)
            DIE("out of memory");
        i64 nwin_word = L - n + 1;
        WPart *wp_ = calloc((size_t)LT, sizeof(WPart));
        int ntp = 1;
#pragma omp parallel num_threads(LT)
        {
            int tid = omp_get_thread_num(), nt = omp_get_num_threads();
#pragma omp single
            ntp = nt;
            i64 a = nwin_word * tid / nt, b = nwin_word * (tid + 1) / nt;
            wp_[tid].first = wp_[tid].last = -1;
            if (b > a)
                word_pass(a, b, ws, wd_word, &wp_[tid]);
        }
        base_perms = cov_count(ws);
        free(ws);
        PROF("word pass (coverage, duplicates, windows)");
        i64 nw = 0, cap = 1 << 16, prev = -1, pstart = -1;
        PS = malloc(cap * 8);
        PL = malloc(cap * 8);
        NP = 0;
#define EMIT_PIECE(ps_, last_)                     \
    do {                                           \
        if (NP == cap) {                           \
            cap *= 2;                              \
            PS = realloc(PS, cap * 8);             \
            PL = realloc(PL, cap * 8);             \
        }                                          \
        PS[NP] = (ps_);                            \
        PL[NP] = (last_) + n - (ps_);              \
        NP++;                                      \
    } while (0)
        for (int q = 0; q < ntp; q++) {
            WPart *z = &wp_[q];
            nw += z->nw;
            if (z->first < 0)
                continue;
            if (prev < 0)
                pstart = z->first;
            else if (z->first - prev >= 4) {
                EMIT_PIECE(pstart, prev);
                pstart = z->first;
            }
            for (i64 j = 0; j < z->nb; j++) {
                EMIT_PIECE(pstart, z->bk[2 * j]);
                pstart = z->bk[2 * j + 1];
            }
            prev = z->last;
            free(z->bk);
        }
        free(wp_);
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
    PROF("pieces");
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
    PROF("trails");
    /* duplicate windows, then the cuts of every trail (parallel over trails) */
    u64 NF = fact[n];
    u64 *seenb = gpuload ? NULL : calloc((size_t)(NF >> 6) + 1, 8), *dupb = calloc((size_t)(NF >> 6) + 1, 8);
    if ((!gpuload && !seenb) || !dupb)
        DIE("out of memory");
    i64 nwin = 0;
    u64 gl_s = 0, gl_d = 0, gl_after = 0; /* gpuload: distinct, duplicated, duplicated also in the word */
    if (gpuload)
        nwin = gl_trail_windows(dupb, &gl_s, &gl_d, &gl_after);
    else {
#pragma omp parallel num_threads(LT) reduction(+ : nwin)
    {
        i64 *wp = malloc((size_t)(maxR + 8) * 8);
        if (!wp)
            DIE("out of memory");
        RBuf q; /* fast: prefetched ranks, see rb_push */
        q.k = 0;
#pragma omp for schedule(dynamic, 8)
        for (i64 t = 0; t < NT; t++) {
            i64 m = trail_windows(&TR[t], wp);
            nwin += m;
            for (i64 i = 0; i < m; i++)
                rb_push(&q, TR[t].fixed ? rank_sw(TR[t].c + wp[i]) : rank_cyc_sw(&TR[t], wp[i]), seenb, dupb);
        }
        rb_flush(&q, seenb, dupb);
        free(wp);
    }
    } /* gpuload */
    {
        u64 dcount = 0, scount = 0;
        if (gpuload) {
            scount = gl_s;
            dcount = gl_d;
        } else
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
    PROF("trail windows (seen, dup)");
    /* A window may be skipped only if its permutation really occurs twice in the word.  The cyclic word of a trail
       can contain a window that the word itself does not have (a piece cut open across a duplicate window), so the
       duplicates are counted again on the word and the two sets are intersected. */
    {
        u64 *wd = wd_word; /* fast: made by the word pass at the start */
        u64 before = 0, after = 0;
        if (gpuload) { /* intersected on the card */
            before = gl_d;
            after = gl_after;
        } else
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
        free(wd);
    }
    PROF("duplicates in the word");
    {
        i64 hist[8] = {0}, shist[8] = {0};
        i64 *ocnt = calloc((size_t)NT + 1, 8);
        i64 **hvs = calloc((size_t)NT + 1, sizeof(i64 *)), *nhs = calloc((size_t)NT + 1, 8); /* fast: duplicate lists */
        for (int pass = 0; pass < 2; pass++) {
#pragma omp parallel num_threads(LT)
            {
                i64 *wp = malloc((size_t)(maxR + 8) * 8), lh[8] = {0}, lsh[8] = {0};
                if (!wp)
                    DIE("out of memory");
#pragma omp for schedule(dynamic, 8)
                for (i64 t = 0; t < NT; t++) {
                    i64 k = trail_options(t, wp, dupb, pass ? OP + TR[t].olo : NULL, lh, lsh, &hvs[t], &nhs[t]);
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
            PROF(pass ? "options pass 1 (write)" : "options pass 0 (count)");
        }
        free(ocnt);
        for (i64 t = 0; t < NT; t++)
            free(hvs[t]);
        free(hvs);
        free(nhs);
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
                if (fscanf(f, "%u %lld %lld", &t, &st, &l) != 3 || t >= NT)
                    DIE("bad plan");
                x.kind = EV_SEG;
                x.t = t;
                x.a = st;
                x.l = l;
                x.s = hw_cyc(&TR[t], st);
                x.e = hw_cyc(&TR[t], st + l - h);
                x.skip = -1;
            }
            if (N + 2 >= cap) {
                cap *= 2;
                ev = realloc(ev, cap * sizeof(Ev));
            }
            ev[N++] = x;
        }
        fclose(f);
        printf("model length of the plan: %lld (%lld events)\n", seq_length(ev, N), N);
        fflush(stdout);
        PROF("read the plan");
        plan_check(ev, N, tlimit > 0);
        PROF("plan check");
    }
    if (gpuload) /* gpuload: the letters leave the card before the search (it needs no card) */
        gl_release();
    /* ---------- destroy / repair search (fast: one set, or several on one loaded model; see Grp) */
    int ns = nsets ? nsets : 1;
    Grp *GR = calloc((size_t)ns, sizeof(Grp));
    for (int s = 0; s < ns; s++) {
        Grp *g = &GR[s];
        if (nsets) {
            const char *sp = setspec[s], *c3 = strrchr(sp, ':');
            int k_;
            double t_;
            unsigned long long s_;
            const char *c2 = NULL, *c1 = NULL;
            if (c3)
                for (const char *q = c3 - 1; q >= sp; q--)
                    if (*q == ':') {
                        if (!c2)
                            c2 = q;
                        else {
                            c1 = q;
                            break;
                        }
                    }
            if (!c1 || sscanf(c1 + 1, "%d:%lf:%llu", &k_, &t_, &s_) != 3 || c1 - sp >= 4000 || c1 == sp)
                DIE("bad --set %s (OUT:KMAX:T0:SEED)", sp);
            memcpy(g->out, sp, (size_t)(c1 - sp));
            g->out[c1 - sp] = 0;
            g->kmax = k_;
            g->T0 = t_;
            g->seed = s_;
            char lp[4200];
            snprintf(lp, sizeof lp, "%s.log", g->out);
            g->log = fopen(lp, "w");
            if (!g->log)
                DIE("cannot write %s", lp);
        } else {
            snprintf(g->out, sizeof g->out, "%s", argv[2]);
            g->kmax = kmax;
            g->T0 = T0;
            g->seed = seed;
            g->log = stdout;
        }
        g->nthr = NTHR;
        snprintf(g->outplan, sizeof g->outplan, "%s.plan", g->out);
        g->ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
        if (!g->ev)
            DIE("out of memory");
        memcpy(g->ev, ev, (size_t)N * sizeof(Ev));
        g->N = N;
        g->len = g->len0 = seq_length(ev, N);
    }
    int spar = setpar > 0 && setpar < ns ? setpar : ns, rc = 0;
    for (int w0 = 0; w0 < ns; w0 += spar) {
        int w1 = w0 + spar < ns ? w0 + spar : ns, nth = (w1 - w0) * NTHR;
        double tw = wall();
        for (int s = w0; s < w1; s++)
            GR[s].t0 = GR[s].last_ck = GR[s].last_log = tw;
        if (nsets) {
            printf("sets %d to %d of %d: %d searches of %.0f s on %d threads each\n", w0 + 1, w1, ns, w1 - w0, tlimit,
                   NTHR);
            fflush(stdout);
        }
        Ctx **cs = calloc((size_t)nth, sizeof(Ctx *));
#pragma omp parallel num_threads(nth)
        {
            int id = omp_get_thread_num();
            Ctx *c = calloc(1, sizeof(Ctx));
            c->g = &GR[w0 + id / NTHR];
            c->tid = id % NTHR;
            search(c, ev, N);
            cs[id] = c;
        }
        for (int q = 0; q < nth; q++)
            if (cs[q])
                ctx_free(cs[q]);
        free(cs);
        PROF("search");
        for (int s = w0; s < w1; s++) {
            Grp *g = &GR[s];
            FILE *fo = g->log;
            i64 tot = 0;
            for (int q = 0; q < NTHR; q++)
                tot += g->it[q];
            fprintf(fo, "LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, g->len);
            fflush(fo);
            print_stats(g->ev, g->N, fo);
            PROF("stats");
            if (write_better && g->len >= g->len0)
                fprintf(fo, "word not written: no gain over the start (--write-better-only)\n");
            else if (write_word(g->ev, g->N, g->out, g->len, fo)) {
                if (!nsets)
                    exit(4); /* the word lacks a permutation: as in the first version */
                fprintf(fo, "REFUSED: the word lacks permutations; see the message on stderr\n");
                fclose(fo);
                printf("set %s: REFUSED (exit code 4 at the end)\n", g->out);
                rc = 4;
                continue;
            }
            PROF("write the word");
            write_plan(g->ev, g->N, g->outplan);
            PROF("write the plan");
            if (write_better && g->len >= g->len0)
                fprintf(fo, "wrote the plan %s, length %lld (%.0fs)\n", g->outplan, g->len, wall() - t00);
            else
                fprintf(fo, "wrote %s length %lld (%.0fs)\n", g->out, g->len, wall() - t00);
            fflush(fo);
            if (nsets) {
                fclose(fo);
                printf("set %s (kmax %d, T0 %g, seed %llu): best %lld\n", g->out, g->kmax, g->T0,
                       (unsigned long long)g->seed, g->len);
                fflush(stdout);
            }
        }
    }
    return rc;
}
