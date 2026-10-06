/* trailsearch_gpu.c - the search of trailsearch.c with the heavy part on an NVIDIA card, with block moves and
   with the fixed-order pass of recut.c kept up to date inside the search.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   What it does.  As trailsearch.c: remove a few closed trails from the sequence, put each back at its best place
   with its best cut, accept by the rule of simulated annealing.  Three things are added.
     1. --gpu.  Finding the best place of a big trail (thousands of cuts against the whole sequence) and the probe
        for related runs run on the card.  The card gives the same answers as the CPU code, so a run with one
        thread writes the same plan with and without --gpu.  The kernels are in kern.cu.
     2. Block moves (rule 6 of --ops).  A run of pieces, two runs, the head of a run or a window goes to its
        cheapest other place without being cut again.
     3. The fixed-order pass inside the search (--coit, --coinc, --coloc, --cosync) and moves judged after re-cutting
        (--reow, --reox).  Block moves alone and the pass alone found nothing on words that had been through the
        pass once; together they did (16 of 24 runs against 0 of 16 at n = 11).

   Build:  gcc -O2 -mpopcnt -fopenmp -o trailsearch_gpu trailsearch_gpu.c -lm          (Linux: add -ldl)
           nvcc -arch=sm_120 -ptx -o kern.ptx kern.cu                                  (once; see kern.cu)
   The program opens the CUDA driver library that comes with the display driver (nvcuda.dll or libcuda.so.1) when it
   starts, so the CUDA toolkit is needed only to compile kern.cu, and neither to build nor to run this file.
   Without --gpu it runs on the CPU alone.

   Use.  A search round as I ran it at n = 12 (20 minutes; n = 13: 60 minutes, --sync 300, --coit 200000):
     trailsearch_gpu BASE.txt OUT.txt --plan-in PLAN --time 1200 --seed S --threads 4 --kmax 14 --T0 0.6 --focus 0.8
                     --sync 120 --ckpt 120 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --coit 2000 --co-skip
                     --gpu --ptx kern.ptx
   With --reox --reorep in place of --coit N the search did better on a word fresh from the pass (n = 12, three
   seeds: 483 to 491 against 490 to 496 in the last three digits) and the same on later words.
   A short search at a constant high temperature whose end sequences are handed to the other passes (kick.sh):
     trailsearch_gpu BASE.txt OUT.txt --plan-in PLAN --threads 2 --time 100000 --iters 60000 --seed S --kmax 14
                     --T0 1.2 --focus 0.8 --sync 100000 --ties --ops 0.4,0.3,0.05,0.25,0,0,2 --blkfree --co-skip
                     --cosync --drift 1000 --gpu --ptx kern.ptx

   Options, beyond those of trailsearch.c.
   The card:
     --gpu            use the card;  --ptx FILE  the compiled kernels (default kern.ptx)
     --gpumin N       trails with more than N cuts go to the card (default 3000)
     --gpucheck       compare every answer of the card with the CPU code (slow; for testing a new card or driver)
     --gpuprof        time the stages;  --gpudepth D  at most D launches under way (default 2)
     --gpuold         one exchange per thread and repair round (three launches) instead of one launch per exchange
     --gpucopy        send the commands with copy calls instead of mapped host memory
   Search moves (all off by default; with them the CPU path and the GPU path still write the same plan):
     --ops w0,..,w7   weights of the removal rules (default 0.4,0.3,0.05,0.25,0,0,0,0):
                      0 related runs, 1 window at an expensive join, 2 random trails, 3 random segments,
                      4 windows at two or three (related) expensive joins, 5 worst removal, 6 block move,
                      7 one whole run of big trails.  Rules 4, 5 and 7 showed no benefit in my tests
     --blkfree        block moves are not counted as iterations
     --worstn M       rule 5 ranks all events if there are at most M (default 4096), else M random ones
     --ties           equal insertions are told apart by the noise hash in every iteration (without it only in the
                      iterations that add noise; the others take the smallest cut, then the smallest node).  No
                      measurable effect
     --opstats        per removal rule / k / removal size / repair mode: uses, accepted, shorter, new best, work
     --maxwork X      stop after X million cuts were tried (a clock that does not depend on the machine load)
   The fixed-order pass (the best cuts of all trails at once, for the order as it is):
     --co             once before the search (with --time 0: nothing else);  --co-skip  the same, and a cut may drop
                      either occurrence of a duplicated permutation
     --coit N         every N iterations of a thread on its current sequence, and on the best sequence when that has
                      changed since its last pass
     --coinc          the passes of --coit on the current sequence first compute only their gain, and only for the
                      part of the sequence that has changed since the last pass (one byte per cut and thread); the
                      cuts are computed when there is a gain
     --coloc          with --coit and --coinc: a pass with a gain re-cuts the pieces in place (backwards through the
                      kept costs) instead of running the full pass and loading the sequence again
     --cosync         the kept costs follow every accepted move (only the layers at the changed places and as far as
                      their costs change are computed), and what they gain is re-cut in place at once: every
                      accepted move is followed by the full pass on the new order.  Implies --coloc and --coinc;
                      --coit N then only checks the kept costs every N iterations
   With any of them the best sequence goes through the pass once more before it is written.
   Moves judged after re-cutting (see the section "local re-cutting"):
     --reow W         a move that makes the sequence longer by 1 .. D letters is judged by its length after the best
                      re-cutting of the pieces within W places of its new joins (block moves: the three joins; with
                      --reorep also ordinary repairs: the joins at the trails put back and at the places they left);
                      if it is accepted the re-cuts are made with it.  --reod D (default 2); --reocap M: no window
                      with more than M million cuts (default 4)
     --reox           with --cosync (which it switches on): such a move is judged by its length after the pass on
                      its whole new order instead (the kept costs are brought to the new order and taken back if the
                      move is rejected; given up after M million cuts)
   --drift D: every thread whose sequence at the end of the run is no more than D letters longer than the best one
   writes it to OUT.txt.driftT.plan (T: the thread).  The best sequence only changes when a shorter one is found, so
   a run that finds nothing hands back the plan it started from; the drift plans are where the threads have wandered.

   Checking a run.  The program prints a "history checksum" of all accepted moves.  Runs with one thread, the same
   options and a very large --time must print the same value on the CPU path, on the card and with --gpucheck.
   -DTS_CHECK=2 builds a version that verifies the kept arrays and every in-place pass at every iteration.

   Memory and speed (measured).  The host needs what trailsearch.c needs, plus 0.48 GB per thread at n = 13 for the
   kept costs of --coinc / --cosync.  The card holds 11 bytes per cut once (n = 13: 5.3 GB) and a mirror of the
   sequence per thread.  One thread, on a card shared with other jobs: about 7,000 iterations per second at n = 11
   and 2,600 to 4,400 at n = 12; the CPU path of the first version made 65 at n = 12.  One process with 4 threads
   is faster than two processes with 2 threads each.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.

   Layout of this file.  It is a copy of the present trailsearch.c with these parts added, marked by lines of equal
   signs: the removal rules and block moves, the card interface (two generations: one exchange per repair round, and
   one launch per exchange with chained repair rounds), the fixed-order pass with its incremental forms and the
   judging of moves after re-cutting.  The search loop itself is changed in many places, so this file cannot be
   read as "trailsearch.c plus one part" the way the pass files can. */
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
#define NL "\n"
#define DIE(...)                      \
    do {                              \
        fprintf(stderr, __VA_ARGS__); \
        fprintf(stderr, "\n");        \
        exit(1);                      \
    } while (0)

/* ==================== shared base (trailsearch.c): model, plan, index ==================== */
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

/* ---------- output */
static void write_word(const Ev *ev, i64 N, const char *path, i64 expect) {
    FILE *f = fopen(path, "wb");
    if (!f)
        DIE("cannot write %s", path);
    size_t cap = 1 << 22, ob = 0;
    char *out = malloc(cap);
    i64 total = 0;
    u64 tail = 0;
    for (i64 i = 0; i < N; i++) {
        const Ev *x = &ev[i];
        i64 skip = i ? h - dist(tail, x->s) : 0;
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
        tail = x->e;
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
#define NOPS \
    8 /* removal rules: 0 related runs, 1 window at an expensive join, 2 random, 3 random segments,
                       4 windows at several expensive joins, 5 worst removal, 6 block move (no re-cutting of the block),
                       7 one whole run of big trails */
static double opw[NOPS] = {0.4, 0.3, 0.05, 0.25, 0, 0, 0, 0};
static int ops_set = 0;
static int blkfree = 0;   /* --blkfree: block moves are not counted as iterations */
static int worstn = 4096; /* --worstn M: rule 5 ranks at most M events */
static int ties = 0;      /* --ties: equal insertions are told apart by the noise hash in every iteration */
static int opstats = 0;
static double maxwork = 0; /* --maxwork X: stop after X million cuts were tried */
static int co_skip = 0, coinc = 0;
static i64 coit = 0; /* cluster optimisation: see co_run and co_value */
static int reow = 0, reox = 0, reorep = 0, coloc = 0, cosync = 0;
static i64 reod = 2;
static double reocap = 4e6; /* local re-cutting */
static i64 drift =
    -1; /* --drift D: a thread that ends within D letters of the best sequence writes its own sequence as a plan */

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
    i64 cur, best_len, it, acc;
    u64 nzk, nzit; /* noise keys of the thread and of the iteration */
    i64 xit, lastper;
    double work; /* block moves not counted, iteration of the last periodic step; work: cuts tried */
    i64 os_n[NOPS], os_acc[NOPS], os_imp[NOPS], os_gain[NOPS], os_best[NOPS], ks_n[64], ks_imp[64], rs_n[8], rs_imp[8],
        gs_n[4], gs_imp[4], st_d[7];
    struct CI *ci;
    i64 ci_st[3]; /* --coinc: what is kept from pass to pass; passes, layers computed, cuts in them */
    double os_t[NOPS], os_w[NOPS], rs_w[8];
    i64 co_st[3];
    double co_sec; /* --opstats; cluster optimisation: passes, with a gain, letters */
    struct RO *ro;
    i64 ro_st[12];
    double ro_sec
        [2]; /* local re-cutting: work area; statistics (see ro_report); seconds in windows, in keeping the costs */
} Ctx;

typedef struct GM GM;
static void gm_link(Ctx *c, int id);
static void gm_ins(Ctx *c, int id);
static void gm_reset(Ctx *c);
static void gm_del(Ctx *c, u64 i, int p); /* GPU mirror hooks */
static void gm_round(Ctx *c, const u32 *pend, i64 np, int greedy, double noise);
static double wall(void);

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

/* ---------- best insertion of trail t: insert after node `after`.
   The best candidate is the smallest triple (value, cut, node), value = (delta + 64) * 65536 + noise bits.  The
   noise of a candidate is a hash of (iteration key, cut, node), not a draw from the thread's random stream, so the
   answer does not depend on the order in which the candidates are met (a GPU computes the same thing).
   The noise is smaller than one letter, so it only decides between candidates of equal delta, and it decides evenly
   (16 bits; equal hashes: the smallest cut, then the smallest node).  Without noise the smallest cut and node
   win.  --ties: an iteration without noise compares with noise of almost one letter too, but reports the plain delta
   as the value (FLAT), so the order of the repair and the comparison with a split stay those of a run without noise. */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
} Ins;
#define VFIX(d) ((u64)((d) + 64) << 16)
#define NZAMP(noise) ((u64)((noise) * 65536.0 + 0.5))
#define FLAT(noise) (ties && (noise) == 0)
#define AMP(noise) (FLAT(noise) ? 0xFFFFULL : NZAMP(noise))
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
    u64 bfx = ~0ULL, amp = AMP(noise);
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
                    i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s);
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
        best.val = FLAT(noise) ? (double)best.delta : (double)bfx / 65536.0 - 64.0;
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

/* ==================== own part: block moves (rule 6 of --ops) ==================== */
/* ---------- block move: the cheapest place (after which node, other than a0) for a block of events that starts with
   the word S and ends with E and is written as it is.  The places where one of the two new joins costs at most KLEV
   are looked up in the index as in best_insertion (the block itself is unlinked, so its nodes are dead here); the
   end of the sequence is a place too.  Equal places are told apart by a hash of (key, node), so the answer does not
   depend on the order of the index chains.  -1: no such place. */
static int blk_place(const Ctx *c, u64 S, u64 E, int a0, u64 key) {
    const Node *nd = c->nd;
    const HTab *H = &c->H;
    int at = -1;
    u64 bfx = ~0ULL;
    for (int k = 0; k < 2 * (KLEV + 1); k++) {
        int j = k >> 1;
        u64 hk = (k & 1) ? HKEY(E & HMASK[h - j], j, 1) : HKEY(S >> (4 * j), j, 0);
        if (!bf_has(c, hk))
            continue;
        for (int e = h_get(H, hk); e >= 0; e = H->next[e]) {
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
            if (a < 0 || a == a0)
                continue;
            i64 d = dist(nd[a].v.e, S) + (b2 >= 0 ? dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s) : 0);
            u64 fx = VFIX(d) + nz16(key, 0, (u64)a);
            if (fx < bfx || (fx == bfx && a < at)) {
                bfx = fx;
                at = a;
            }
        }
    }
    return at;
}

/* ==================== shared base: two-segment insertion, related runs ==================== */
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
        if (nd[x].next >= 0 && dist(nd[x].v.e, nd[nd[x].next].v.s) < 2)
            return; /* not the end of a run */
        while (nd[s].prev >= 0 && dist(nd[nd[s].prev].v.e, nd[s].v.s) < 2) {
            s = nd[s].prev;
            if (++len > runcap)
                return;
        }
    } else {
        if (nd[x].prev >= 0 && dist(nd[nd[x].prev].v.e, nd[x].v.s) < 2)
            return; /* not the start of a run */
        for (int y = x; nd[y].next >= 0 && dist(nd[y].v.e, nd[nd[y].next].v.s) < 2; y = nd[y].next)
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
/* ==================== own part: the card interface (--gpu) ==================== */
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
static int(CUAPI *cuLaunchCooperativeKernel)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned,
                                             unsigned, void *, void **);
static int(CUAPI *cuOccupancyMaxActiveBlocksPerMultiprocessor)(int *, void *, int, size_t),
    (CUAPI * cuDeviceGetAttribute)(int *, int, int);
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
typedef struct {
    DP nd, tab, nx, vl, bf;
    u64 mask, bfmask;
    DP oS, oE, oSh, oEh, oF, stamp;
    int h, pad;
} GDev;
/* touched nodes / slots per upload, command words, answers */
enum { G_TN = 1 << 14, G_TS = 1 << 15, G_CMD = 1 << 19, G_OUT = 1 << 16, G_BLK = 256 };
/* ts_batch (kern.cu): the header of a job (the last GJ_HW words of the command buffer), jobs per launch, trails and
   rounds per job, GPU threads per block, words of the log of a job */
enum {
    H_ND,
    H_TAB,
    H_NX,
    H_VL,
    H_BF,
    H_MASK,
    H_BFMASK,
    H_OS,
    H_OE,
    H_OSH,
    H_OEH,
    H_OF,
    H_STAMP,
    H_H,
    H_HC,
    H_DC,
    H_NNODE,
    H_NSLOT,
    H_NENT,
    H_NBF,
    H_ENTBASE,
    H_NTE,
    H_PW,
    H_NCOPY,
    H_KIND,
    H_NTR,
    H_GREEDY,
    H_RMAX,
    H_ITK,
    H_AMP,
    H_SHA,
    H_SHF,
    H_FLAT,
    H_SKPM,
    H_NN,
    H_NDCAP,
    H_RS,
    H_GEN = H_RS + 4,
    H_CAP,
    H_OUT,
    H_DONE,
    H_LO,
    H_TOT,
    H_PL0,
    H_PL1,
    H_FU0,
    H_FU1,
    H_INC,
    H_IAX,
    H_IEA,
    H_ISX,
    H_IEX,
    H_ISB,
    H_RES,
    H_NOVL,
    H_OUTN,
    GJ_HW = 64
};
enum { GJ_MAXJ = 16, GJ_MAXTR = 96, GJ_RMAX = 24, GJ_BT = 512, GJ_LOGW = GJ_RMAX * (GJ_MAXTR + 2) };
#if defined(__x86_64__) || defined(__i386__)
#define CPU_RELAX() __builtin_ia32_pause()
#else
#define CPU_RELAX() ((void)0)
#endif
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
    /* ts_batch: the job that waits for a launch (js: 1 posted, 2 in a launch, 3 answered, 4 the kernel gave up; its
       output word; its size; how its answers are packed), and the chain: the log of the rounds the card has answered
       ahead of the host (ch_n rounds, ch_r of them given to the host; ch_tr, ch_act, ch_nact: the trails and the order
       in which the card expects them in round ch_r; ch_xo, ch_xa, ch_xid: the insertion the card made after the last
       round given), the hooks called since the last round */
    int js, led, jsha, jshf;
    i64 jout, jwork;
    u64 *clog;
    int ch_live, ch_n, ch_r, ch_greedy, ch_ntr, ch_nact, ch_sha, ch_shf, ch_nn0, ch_xa, ch_xid, ch_act[GJ_MAXTR],
        hk_ins, hk_other;
    u32 ch_tr[GJ_MAXTR];
    i64 ch_it, ch_xo;
    u64 ch_amp;
    i64 nexch, nlead, nljobs, nserved, nback, nfail;
};
static int use_gpu = 0, gpu_prof = 0, gpu_check = 0;
static i64 gpu_min = 3000;
static const char *ptx_path = NULL;
static int gpu_map = 1;
static void *g_cu, *g_fpatch, *g_fprobe, *g_frelt, *g_fcopy;
static DP g_oS, g_oE, g_oSh, g_oEh, g_oF;
static double g_devmb;
/* ts_batch: on / off, the kernel, its stream, the table of job headers and the barrier words on the card, the tag of
   the next barrier, the blocks that fit on the card at once, the mirrors of all threads, the lock of the launch, the
   launches that are not answered yet */
static int gpu_batch = 1, gb_depth = 2;
static void *g_fbatch, *gb_stream;
static DP gb_tab, gb_bar;
static unsigned gb_base = 4096;
static int gb_nbmax, gb_n, gb_lock, gb_fl;
static GM *gb_all[256];

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
    *(void **)&cuLaunchCooperativeKernel = lib_sym(lib, "cuLaunchCooperativeKernel");
    *(void **)&cuDeviceGetAttribute = lib_sym(lib, "cuDeviceGetAttribute");
    *(void **)&cuOccupancyMaxActiveBlocksPerMultiprocessor =
        lib_sym(lib, "cuOccupancyMaxActiveBlocksPerMultiprocessor");
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
    if ((e = cuModuleLoadData(&mod, ptx)) || (e = cuModuleGetFunction(&g_fpatch, mod, "ts_patch")) ||
        (e = cuModuleGetFunction(&g_fprobe, mod, "ts_probe")) || (e = cuModuleGetFunction(&g_frelt, mod, "ts_relt")) ||
        (e = cuModuleGetFunction(&g_fcopy, mod, "ts_copy"))) {
        printf("gpu: the kernel file was not accepted by the driver (error %d); searching on the CPU\n", e);
        return 0;
    }
    /* ts_batch needs mapped host memory and a grid that is on the card as a whole (blocks per multiprocessor x multiprocessors) */
    {
        int occ = 0, sms = 0;
        if (gpu_batch && gpu_map && cuMemHostAlloc && cuMemHostGetDevicePointer &&
            cuOccupancyMaxActiveBlocksPerMultiprocessor && cuDeviceGetAttribute &&
            !cuModuleGetFunction(&g_fbatch, mod, "ts_batch") &&
            !cuOccupancyMaxActiveBlocksPerMultiprocessor(&occ, g_fbatch, GJ_BT, 0) &&
            !cuDeviceGetAttribute(&sms, 16, dev) && occ > 0 && sms > 0) {
            gb_nbmax = occ * sms;
            static const u32 zero[256];
            CK(cuMemAlloc(&gb_tab, GJ_MAXJ * GJ_HW * 8));
            CK(cuMemAlloc(&gb_bar, sizeof zero));
            CK(cuMemcpyHtoD(gb_bar, zero, sizeof zero));
            CK(cuStreamCreate(&gb_stream, 0));
        } else
            gpu_batch = 0;
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
    if (gpu_batch)
        printf(
            "gpu: one launch per exchange for all threads (up to %d blocks of %d GPU threads), up to %d rounds of a repair per exchange\n",
            gb_nbmax, GJ_BT, GJ_RMAX);
    else
        printf("gpu: one exchange per thread and round (%s)\n", gpu_map ? "three launches" : "copy calls");
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
        if (!g->map) {
            CK(cuMemAllocHost(&p, (size_t)G_CMD * 8));
            gpu_batch = 0;
        }
        g->hc = p;
        g->ch_it = -1;
        if (gb_n < 256) {
            gb_all[gb_n] = g;
            __atomic_store_n(&gb_n, gb_n + 1, __ATOMIC_RELEASE);
        } else
            gpu_batch = 0;
    }
    g->clog = malloc(GJ_LOGW * 8);
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
        b[i].e = q->v.e;
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
    g->ch_live = 0;
    g->ch_it = -1;
    g->nfull++;
    g->t_full += wall() - t0;
}
static inline void gm_touch(Ctx *c, int id) {
    GM *g = c->G;
    if (id >= 0 && !g->dirty[id]) {
        g->dirty[id] = 1;
        g->tn[g->ntn++] = id;
    }
}
/* A chain (ts_batch) has linked nodes into the mirror ahead of the host.  The insertions the host has not made itself
   (it took another way after a round, or the chain was not used up) are taken back: the two neighbours of such a node
   are noted as changed, so that the next upload brings the links of the host.  (The card adds no index entries.) */
static void gm_back(Ctx *c) {
    GM *g = c->G;
    if (!g->ch_live)
        return;
    g->ch_live = 0;
    g->ch_it = -1;
    for (int r = g->ch_r > 0 ? g->ch_r - 1 : 0; r < g->ch_n; r++) {
        const u64 *L = g->clog + (size_t)r * (g->ch_ntr + 2);
        if (L[0] & 255)
            continue;
        int a = (int)(u32)L[g->ch_ntr + 1], b = (int)(L[g->ch_ntr + 1] >> 32);
        if (a < c->nn)
            gm_touch(c, a);
        if (b < c->nn)
            gm_touch(c, b);
        g->nback++;
    }
}
/* writes the patch records to the command buffer; returns the number of words and the argument block of ts_patch */
static i64 gm_patches(Ctx *c, int *pa) {
    GM *g = c->G;
    const HTab *H = &c->H;
    u64 *w = g->hc;
    i64 m = 0;
    gm_back(c);
    for (int q = 0; q < g->ntn; q++) {
        int id = g->tn[q];
        const Node *x = &c->nd[id];
        g->dirty[id] = 0;
        w[m++] = (u64)id;
        w[m++] = x->v.s;
        w[m++] = x->v.e;
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
static u64 *gj_head(Ctx *c, const int *pa, i64 pw, i64 ncopy, int kind, i64 out);
static int gm_submit(Ctx *c);
/* too many changes noted and no launch in sight: send them */
static void gm_sync(Ctx *c) {
    GM *g = c->G;
    int pa[6];
    double t0 = wall();
    i64 m = gm_patches(c, pa);
    g->t_build += wall() - t0;
    g->nsync++;
    g->hk_other++;
    if (gpu_batch) {
        gj_head(c, pa, m, 0, 0, m);
        gm_submit(c);
    } /* if the kernel gave up the mirror is loaded again */
    else
        gm_exchange(c, m, pa, NULL, NULL, 0, 0, 0);
}
/* hooks of node_unlink and node_relink / node_insert_after / ctx_load */
static void gm_link(Ctx *c, int id) {
    GM *g = c->G;
    g->hk_other++;
    if (g->full)
        return;
    gm_touch(c, id);
    gm_touch(c, c->nd[id].prev);
    gm_touch(c, c->nd[id].next);
    if (g->ntn > G_TN - 64)
        gm_sync(c);
}
/* Hook: node id was inserted on the host.  Notes the node, its two neighbours and the index slots it changed,
   so that the mirror on the card gets them with the next command. */
static void gm_ins(Ctx *c, int id) {
    GM *g = c->G;
    g->hk_ins++;
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
    if (g->nts > G_TS - 16 || g->ntn > G_TN - 64)
        gm_sync(c);
}
static void gm_reset(Ctx *c) {
    c->G->full = 1;
    c->G->ch_live = 0;
    c->G->ch_it = -1;
}
/* hook of index_del: the head of slot i (p < 0) or the link of entry p has changed */
static void gm_del(Ctx *c, u64 i, int p) {
    GM *g = c->G;
    g->hk_other++;
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
            i64 d = dist(nd[a].v.e, S) + D + dist(E, nd[b2].v.s) - dist(nd[a].v.e, nd[b2].v.s);
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
/* best_insertion of the big trails among pend[0 .. np): the answers go to G->ins[q], G->has[q] says which are there
   (one exchange per round: --gpuold, --gpucopy, or after the batch kernel gave up) */
static void gm_round1(Ctx *c, const u32 *pend, i64 np, double noise) {
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
    u64 amp = AMP(noise), itk = c->nzit;
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
            bi.after = ins_one(c, T, o, amp, &fx, &bi.delta);
            if (bi.after < 0 || fx != r >> 40)
                DIE("gpu: the card and the host disagree (trail %u opening %lld: %llx / %llx)", t, o,
                    (unsigned long long)(r >> 40), (unsigned long long)fx);
            bi.val = FLAT(noise) ? (double)bi.delta : (double)fx / 65536.0 - 64.0;
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
static int gm_relt1(Ctx *c, const int *ids, int m, int runcap, int *rel) {
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

/* ---------- one launch per exchange (ts_batch in kern.cu).
   A thread writes its job (patches, command, header) to its command buffer and posts it.  A thread that finds
   fewer than gb_depth launches under way starts one for all jobs that are posted; every thread waits for the word
   the kernel sets in its command buffer when its job is answered.  So a job is one launch, not three per round, and
   on a card that is shared with other processes (where a launch that finds the card with somebody else waits for
   a whole turn) one turn serves the jobs of several threads. */
/* the caller holds gb_lock and has posted a job */
static void gb_launch(GM *me) {
    GM *jb[GJ_MAXJ];
    int J = 0, n = __atomic_load_n(&gb_n, __ATOMIC_ACQUIRE);
    i64 work = 0;
    struct {
        u64 hc[GJ_MAXJ];
    } b;
    __atomic_store_n(&me->js, 2, __ATOMIC_RELEASE);
    jb[J++] = me;
    for (int i = 0; i < n && J < GJ_MAXJ; i++) {
        GM *x = gb_all[i];
        if (x != me && __atomic_load_n(&x->js, __ATOMIC_ACQUIRE) == 1) {
            __atomic_store_n(&x->js, 2, __ATOMIC_RELEASE);
            jb[J++] = x;
        }
    }
    for (int j = 0; j < GJ_MAXJ; j++) {
        b.hc[j] = j < J ? jb[j]->map : 0;
        if (j < J)
            work += jb[j]->jwork;
    }
    unsigned nb = (unsigned)((work + GJ_BT - 1) / GJ_BT), base = gb_base;
    int hoff = G_CMD - GJ_HW;
    if (nb < 2)
        nb = 2;
    if (nb > (unsigned)gb_nbmax)
        nb = (unsigned)gb_nbmax;
    void *args[6] = {&b, &J, &gb_tab, &gb_bar, &base, &hoff};
    gb_base += 4096;
    if (!gb_base)
        gb_base = 4096; /* tag 0 is what the barrier words start with */
    if (cuLaunchCooperativeKernel)
        CK(cuLaunchCooperativeKernel(g_fbatch, nb, 1, 1, GJ_BT, 1, 1, 0, gb_stream, args));
    else
        CK(cuLaunchKernel(g_fbatch, nb, 1, 1, GJ_BT, 1, 1, 0, gb_stream, args, NULL));
    me->nlead++;
    me->nljobs += J;
    me->led = 1;
    __atomic_fetch_add(&gb_fl, 1, __ATOMIC_RELEASE);
}
/* Posts the job of this thread and waits for its answers.  The launch is not waited for with a driver call: the
   kernel sets a word in the command buffer when everything is delivered, so the launch lock is free again at once and
   a job that is posted a moment later goes into a launch of its own, queued behind the first: on a shared card both
   are then served in the same turn, and on a free card the second kernel starts when the first ends.  With two
   launches under way the jobs wait and share the next launch (measured: waiting for the first launch to end, so
   that more jobs share a kernel, is slower with 4 and with 8 threads, on a free and on a shared card).  Returns 0 if
   the kernel gave up (no answer for seconds; then the mirror has to be loaded again and the search goes on with the
   kernels of one exchange per round). */
static int gm_submit(Ctx *c) {
    GM *g = c->G;
    double t0 = wall();
    volatile u64 *done = (volatile u64 *)(g->hc + (G_CMD - GJ_HW) + H_DONE);
    int st = 3;
    g->hc[g->jout] = 0;
    __atomic_store_n(&g->js, 1, __ATOMIC_RELEASE);
    for (u64 spin = 1; !*done; spin++) {
        if (__atomic_load_n(&g->js, __ATOMIC_ACQUIRE) == 1 && __atomic_load_n(&gb_fl, __ATOMIC_RELAXED) < gb_depth &&
            !__atomic_load_n(&gb_lock, __ATOMIC_RELAXED) && !__atomic_exchange_n(&gb_lock, 1, __ATOMIC_ACQUIRE)) {
            if (__atomic_load_n(&g->js, __ATOMIC_ACQUIRE) == 1 && __atomic_load_n(&gb_fl, __ATOMIC_ACQUIRE) < gb_depth)
                gb_launch(g);
            __atomic_store_n(&gb_lock, 0, __ATOMIC_RELEASE);
        } else
            CPU_RELAX();
        if (!(spin & 0xFFFFF) && wall() - t0 > 3.0 && __atomic_load_n(&g->js, __ATOMIC_ACQUIRE) == 2) {
            while (__atomic_exchange_n(&gb_lock, 1, __ATOMIC_ACQUIRE))
                CPU_RELAX();
            CK(cuStreamSynchronize(gb_stream)); /* all launches are over now */
            if (!*done) {
                static const u32 zero[256];
                CK(cuMemcpyHtoD(gb_bar, zero, sizeof zero));
                st = 4;
            } /* a wait in the kernel ran out: the barrier words are not at a phase boundary */
            __atomic_store_n(&gb_lock, 0, __ATOMIC_RELEASE);
            if (st == 4)
                break;
        }
    }
    if (st == 3 && !g->hc[g->jout])
        st = 4;
    if (g->led) {
        g->led = 0;
        __atomic_fetch_sub(&gb_fl, 1, __ATOMIC_RELEASE);
    }
    __atomic_store_n(&g->js, 0, __ATOMIC_RELEASE);
    g->nexch++;
    g->t_kern += wall() - t0;
    if (st == 3)
        return 1;
    g->nfail++;
    g->full = 1;
    g->ch_live = 0;
    g->ch_it = -1;
#pragma omp critical(gbest)
    if (gpu_batch) {
        gpu_batch = 0;
        printf(
            "gpu: the batch kernel gave up (thread %d, iteration %lld); the mirrors are loaded again and the search goes on with one exchange per round\n",
            c->tid, c->it);
        fflush(stdout);
    }
    return 0;
}
/* the header of the job of this thread: pw words of patch records, then ncopy command words for the card; the card
   answers from word out on */
static u64 *gj_head(Ctx *c, const int *pa, i64 pw, i64 ncopy, int kind, i64 out) {
    GM *g = c->G;
    u64 *t = g->hc + (G_CMD - GJ_HW);
    memset(t, 0, GJ_HW * 8);
    memcpy(t, &g->d, sizeof(GDev));
    t[H_HC] = g->map;
    t[H_DC] = g->cmd;
    t[H_NNODE] = (u64)pa[0];
    t[H_NSLOT] = (u64)pa[1];
    t[H_NENT] = (u64)pa[2];
    t[H_NBF] = (u64)pa[3];
    t[H_ENTBASE] = (u64)pa[4];
    t[H_NTE] = (u64)pa[5];
    t[H_PW] = (u64)pw;
    t[H_NCOPY] = (u64)ncopy;
    t[H_KIND] = (u64)kind;
    t[H_OUT] = (u64)out;
    g->jout = out;
    g->jwork = (i64)pa[0] + pa[1] + pa[2] + pa[3] + pa[5] + ncopy + 2;
    return t;
}
/* The answers of the card for n trails are checked on the host and stored in G->ins / G->has: trail z is pend[pos[z]]
   (pos == NULL: pend[z]), its answer is res[slot[z]] (slot == NULL: res[z]), packed value << shf | cut << sha |
   node (sha == 0: value << 40 | cut).  A skip cut whose window is skipped already is remembered and the
   position of its trail is written to again[] (again may be pos); returns the number of such trails. */
static int gm_take(Ctx *c, const u32 *pend, const int *pos, int n, const u64 *res, const int *slot, int sha, int shf,
                   double noise, int *again) {
    GM *g = c->G;
    u64 amp = AMP(noise), mo = sha ? (1ULL << (shf - sha)) - 1 : 0xFFFFFFFFFFULL;
    int n2 = 0;
    for (int z = 0; z < n; z++) {
        int q = pos ? pos[z] : z;
        u32 t = pend[q];
        const Trail *T = &TR[t];
        u64 r = res[slot ? slot[z] : z];
        g->nopen += T->ohi - T->olo;
        if (r == ~0ULL) {
            g->ncpu++;
            continue;
        } /* no candidate at all: left to the host */
        i64 o = T->olo + (i64)((r >> sha) & mo);
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
                again[n2++] = q;
                continue;
            }
        }
        Ins bi;
        u64 fx;
        bi.opt = o;
        bi.after = ins_one(c, T, o, amp, &fx, &bi.delta);
        if (bi.after < 0 || fx != r >> shf || (sha && (u64)bi.after != (r & ((1ULL << sha) - 1))))
            DIE("gpu: the card and the host disagree (trail %u opening %lld: value %llx / %llx, node %lld / %d)", t, o,
                (unsigned long long)(r >> shf), (unsigned long long)fx,
                sha ? (long long)(r & ((1ULL << sha) - 1)) : -1LL, bi.after);
        bi.val = FLAT(noise) ? (double)bi.delta : (double)fx / 65536.0 - 64.0;
        g->ins[q] = bi;
        g->has[q] = 1;
        if (gpu_check) {
            Ins ref = best_insertion(c, t, noise); /* --gpucheck: the whole answer against the host */
            if (ref.opt != bi.opt || ref.after != bi.after || ref.val != bi.val || ref.delta != bi.delta)
                DIE("gpu check: trail %u at iteration %lld: card (%lld, %d, %.6f), host (%lld, %d, %.6f)", t, c->it,
                    bi.opt, bi.after, bi.val, ref.opt, ref.after, ref.val);
        }
    }
    return n2;
}
/* One probe job for the trails tr[0 .. ntr).  rmax > 1: a chain; the card goes on by itself for at most rmax rounds,
   as long as nothing but a best insertion is needed (kern.cu).  greedy: all trails are probed in every round and
   the best one is inserted (ties as on the host: the state of its random numbers travels with the job); otherwise
   one trail per round, in the order of tr.  flat: the best trail is the one with the smallest value without its
   noise bits (as the host compares them under --ties).  The answers are in the command buffer from word G->jout
   on: rounds, a spare word, and per round ntr + 2 words (head, answers by trail, neighbours of the inserted node).
   Returns 0 if the kernel gave up. */
static int gm_job(Ctx *c, const u32 *tr, int ntr, int greedy, int rmax, u64 amp, int flat) {
    GM *g = c->G;
    double t1 = wall();
    int pa[6];
    i64 pw = gm_patches(c, pa), tot = 0, mx = 1;
    u64 *w = g->hc + pw;
    i64 xo = 3 * (i64)ntr + 1, room = G_CMD - GJ_HW - 64 - 2 - (i64)rmax * (ntr + 3) - ntr;
    for (int z = 0; z < ntr; z++) {
        u32 t = tr[z];
        i64 x0 = xo, no = TR[t].ohi - TR[t].olo;
        if (no > mx)
            mx = no;
        if (pw + xo > room)
            DIE("gpu: command buffer too small");
        if (c->nskp)
            for (int e = g->xhead[t]; e >= 0; e = g->xnext[e])
                if (skp_has(c, g->xr[e])) {
                    w[xo++] = (u64)g->xo[e];
                    if (pw + xo > room)
                        DIE("gpu: command buffer too small");
                }
        w[z] = (u64)TR[t].olo;
        w[ntr + z] = (u64)tot;
        w[2 * ntr + 1 + z] = (u64)x0 | (u64)(xo - x0) << 32 | (u64)(use_split && no <= splitmax) << 63;
        tot += no;
    }
    w[2 * ntr] = (u64)tot;
    /* value (23 bits), cut and node in one word; if they do not fit, the node stays with the host and there is no chain */
    int ba = 1, bo = 1;
    while ((1LL << ba) < g->ndcap)
        ba++;
    while ((1LL << bo) < mx)
        bo++;
    if (23 + bo + ba > 64) {
        ba = 0;
        bo = 40;
        rmax = 1;
    }
    u64 *t = gj_head(c, pa, pw, xo, 1, pw + xo);
    t[H_NTR] = (u64)ntr;
    t[H_GREEDY] = (u64)greedy;
    t[H_RMAX] = (u64)rmax;
    t[H_ITK] = c->nzit;
    t[H_AMP] = amp;
    t[H_SHA] = (u64)ba;
    t[H_SHF] = (u64)(ba + bo);
    t[H_FLAT] = flat ? 16 : 0;
    t[H_SKPM] = c->nskp > 0;
    t[H_NN] = (u64)c->nn;
    t[H_NDCAP] = (u64)g->ndcap;
    for (int k = 0; k < 4; k++)
        t[H_RS + k] = c->rs[k];
    t[H_TOT] = greedy ? (u64)tot : w[ntr + 1];
    t[H_RES] = (u64)(pw + xo + 3);
    g->jsha = ba;
    g->jshf = ba + bo;
    g->jwork += tot + (i64)rmax * (ntr + 2) + ntr;
    g->t_build += wall() - t1;
    if (!gm_submit(c))
        return 0;
    g->nprobe++;
    return 1;
}
/* best_insertion of the trails of this round on the card: the answers go to G->ins[q], G->has[q] says which are there.
   np trails wait; greedy: the caller wants all of them and takes the best, otherwise it wants pend[0].  If the round
   has a trail with more than gpu_min cuts, a job goes to the card: the trails of this round and, where the card
   can go on alone, the rounds after it (a chain).  The rounds after the first are then answered from the log of the
   chain, provided the host has done exactly what the card did: one insertion, of the same cut after the same
   node, and nothing else (the hooks count), and the same trails wait in the same order. */
static void gm_round(Ctx *c, const u32 *pend, i64 np, int greedy, double noise) {
    GM *g = c->G;
    if (!gpu_batch) {
        gm_round1(c, pend, greedy ? np : 1, noise);
        return;
    }
    int m = greedy ? (int)np : 1, again = 0, fresh = 0, flat = FLAT(noise);
    const int *pos = NULL;
    double t0 = wall(), t1;
    u64 amp = AMP(noise);
    for (int q = 0; q < m; q++)
        g->has[q] = 0;
    int ok = g->ch_live && !g->full && g->ch_it == c->it && g->ch_amp == amp && g->ch_greedy == greedy && g->ch_r > 0 &&
             g->ch_r < g->ch_n && g->hk_ins == 1 && !g->hk_other;
    if (ok) {
        int id = c->nn - 1;
        const Node *x = &c->nd[id];
        ok = id == g->ch_xid && x->v.kind == EV_OPT && x->v.a == g->ch_xo && x->prev == g->ch_xa;
        if (ok && greedy) {
            ok = np == g->ch_nact;
            for (int k = 0; ok && k < np; k++)
                ok = pend[k] == g->ch_tr[g->ch_act[k]];
        } else if (ok)
            ok = pend[0] == g->ch_tr[g->ch_r];
    }
    if (!ok) {
        gm_back(c);
        g->ch_it = -1; /* a chain that was not used up is taken back */
        int nl = 0, ntr = 0, rmax = 0;
        for (int q = 0; q < m; q++)
            if (TR[pend[q]].ohi - TR[pend[q]].olo > gpu_min)
                g->lst[nl++] = q;
        if (!nl) {
            g->hk_ins = g->hk_other = 0;
            return;
        }
        if (g->full)
            gm_full(c);
        u32 *tr = g->ch_tr;
        if (greedy) { /* the launch is paid for: the small trails ride along, and the card can take the best of all */
            int all = np <= GJ_MAXTR;
            for (int q = 0; all && q < np; q++)
                all = TR[pend[q]].ohi > TR[pend[q]].olo;
            if (all) {
                for (ntr = 0; ntr < np; ntr++)
                    tr[ntr] = pend[ntr];
                rmax = ntr < GJ_RMAX ? ntr : GJ_RMAX;
            }
        } else { /* the trails come to the front in the order pend[0], pend[np - 1], pend[np - 2], ...; the chain ends with the first one the host has to decide about */
            for (i64 k = 0; k < np && ntr < GJ_RMAX; k++) {
                u32 t = pend[k ? np - k : 0];
                i64 no = TR[t].ohi - TR[t].olo;
                if (!no)
                    break;
                tr[ntr++] = t;
                if (use_split && no <= splitmax)
                    break;
            }
            rmax = ntr;
        }
        if (rmax) {
            if (!gm_job(c, tr, ntr, greedy, rmax, amp, flat)) {
                gm_round1(c, pend, m, noise);
                return;
            }
            const u64 *o = g->hc + g->jout;
            int rounds = (int)o[0];
            if (rounds < 1 || rounds > rmax)
                DIE("gpu: bad log of a chain (%d rounds of %d)", rounds, rmax);
            memcpy(g->clog, o + 2, (size_t)rounds * (ntr + 2) * 8);
            g->ch_n = rounds;
            g->ch_r = 0;
            g->ch_live = 1;
            g->ch_it = c->it;
            g->ch_amp = amp;
            g->ch_greedy = greedy;
            g->ch_ntr = ntr;
            g->ch_nact = greedy ? ntr : 1;
            g->ch_sha = g->jsha;
            g->ch_shf = g->jshf;
            g->ch_nn0 = c->nn;
            for (int k = 0; k < ntr; k++)
                g->ch_act[k] = k;
            fresh = 1;
        } else {
            again = nl;
            pos = g->lst;
        } /* too many trails for a chain, or a trail without cuts: the big trails only, round by round */
    }
    if (ok || fresh) { /* the answers of round ch_r */
        int r = g->ch_r, ntr = g->ch_ntr, sha = g->ch_sha, shf = g->ch_shf;
        const u64 *L = g->clog + (size_t)r * (ntr + 2);
        int st = (int)(L[0] & 255), na = (int)(L[0] >> 8) & 0xFFF, pick = (int)(L[0] >> 20);
        if (na != m)
            DIE("gpu: round %d of a chain has %d trails, the host has %d", r, na, m);
        t1 = wall();
        again = greedy ? gm_take(c, pend, NULL, na, L + 1, g->ch_act, sha, shf, noise, g->lst)
                       : gm_take(c, pend, NULL, 1, L + 1 + r, NULL, sha, shf, noise, g->lst);
        pos = g->lst;
        if (!st) { /* what the card has inserted after this round */
            int z = greedy ? g->ch_act[pick] : r;
            u64 x = L[1 + z];
            g->ch_xo = TR[g->ch_tr[z]].olo + (i64)((x >> sha) & ((1ULL << (shf - sha)) - 1));
            g->ch_xa = (int)(x & ((1ULL << sha) - 1));
            g->ch_xid = g->ch_nn0 + r;
            if (greedy) {
                g->ch_act[pick] = g->ch_act[na - 1];
                g->ch_nact = na - 1;
            }
        }
        g->ch_r = r + 1;
        if (g->ch_r == g->ch_n && st)
            g->ch_live = 0;
        g->t_post += wall() - t1;
        if (ok)
            g->nserved++;
    }
    for (int pass = fresh || ok; again > 0;
         pass++) { /* (again) the trails at the positions pos[0 .. again), without a chain */
        int n = again;
        again = 0;
        for (int o0 = 0; o0 < n; o0 += GJ_MAXTR) {
            int k = n - o0 < GJ_MAXTR ? n - o0 : GJ_MAXTR;
            u32 tb[GJ_MAXTR];
            for (int z = 0; z < k; z++)
                tb[z] = pend[pos[o0 + z]];
            if (!gm_job(c, tb, k, 1, 1, amp, flat)) {
                gm_round1(c, pend, m, noise);
                return;
            }
            if (pass)
                g->nretry++;
            t1 = wall();
            again += gm_take(c, pend, pos + o0, k, g->hc + g->jout + 3, NULL, g->jsha, g->jshf, noise, g->lst + again);
            g->t_post += wall() - t1;
        }
    }
    g->hk_ins = g->hk_other = 0;
    g->nround++;
    g->t_all += wall() - t0;
}
/* related runs of the trails of nodes ids[0 .. m) (see rel_runs); returns -1 if the card gave too many answers */
static int gm_relt(Ctx *c, const int *ids, int m, int runcap, int *rel) {
    GM *g = c->G;
    double t0 = wall(), t1;
    if (!gpu_batch)
        return gm_relt1(c, ids, m, runcap, rel);
    if (g->full)
        gm_full(c);
    t1 = wall();
    int pa[6];
    i64 pw = gm_patches(c, pa), tot = 0, out = pw + 3 * (i64)m + 1;
    u64 *w = g->hc + pw;
    if (out + 2 + G_OUT / 2 > G_CMD - GJ_HW - 64)
        DIE("gpu: command buffer too small");
    for (int z = 0; z < m; z++) {
        const Trail *T = &TR[c->nd[ids[z]].v.t];
        w[z] = (u64)T->olo;
        w[m + z] = (u64)tot;
        w[2 * m + 1 + z] = 0;
        tot += T->ohi - T->olo;
    }
    w[2 * m] = (u64)tot;
    if (++g->gen == 0) {
        CK(cuMemsetD32(g->d.stamp, 0, (size_t)g->ndcap * 2));
        g->gen = 1;
    }
    u64 *t = gj_head(c, pa, pw, 3 * (i64)m + 1, 2, out);
    t[H_NTR] = (u64)m;
    t[H_TOT] = (u64)tot;
    t[H_GEN] = g->gen;
    t[H_CAP] = G_OUT;
    g->jwork += tot;
    g->t_build += wall() - t1;
    if (!gm_submit(c))
        return gm_relt1(c, ids, m, runcap, rel);
    const int *ans = (const int *)(g->hc + out + 1);
    int cnt = ans[0];
    ans += 2;
    g->nrelt++;
    g->nopen += tot;
    g->nans += cnt;
    if (cnt > G_OUT) {
        g->t_all += wall() - t0;
        return -1;
    }
    t1 = wall();
    rel_begin(c);
    for (int q = 0; q < cnt; q++)
        rel_hit(c, ans[q] >> 1, ans[q] & 1, ids[0], runcap);
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
        if (g->nexch)
            printf(
                "gpu thread %d: one launch per exchange: %lld exchanges, %lld launches started here with %.2f jobs each, %lld rounds answered from the log of a chain, %lld insertions of the card taken back, %lld times the kernel gave up\n",
                c->tid, g->nexch, g->nlead, (double)g->nljobs / (g->nlead ? g->nlead : 1), g->nserved, g->nback,
                g->nfail);
        if (gpu_prof && !gpu_map)
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
    printf(
        "stats: events %lld (unchanged pieces %lld, segments %lld), gap-2 openings %lld, gap-1 openings %lld, duplicate-skip openings %lld, opening cost %lld" NL,
        N, pieces, segs, g2, g1, skips, extra);
    printf("stats: runs %lld, join cost between runs %lld, joins inside runs cost %lld; joins by cost:", runs, inter,
           inrun);
    for (int d = 0; d <= h; d++)
        if (hist[d])
            printf(" %d:%lld", d, hist[d]);
    printf(NL);
    fflush(stdout);
}

/* ==================== own part: the fixed-order pass (as in recut.c) and its incremental forms (--coinc, --coloc, --cosync) ==================== */
/* ---------- cluster optimisation: for a fixed order of the events, the best cuts of all trails at once.
   Shortest path through layers, one per event: cost[p] = D(p) + min over the cuts o of the previous event of
   cost[o] + join(E(o), S(p)).  The minimum is not taken over pairs (co_relax): for k = h..1 a table holds the cheapest o for
   every suffix of length k of E(o) (a hash table, for k <= 3 an array) and prefix_k(S(p)) is looked up; only o with cost[o] - min < k can beat the
   join without overlap (h + min), so few o enter the tables of small k.  Costs are kept relative to the minimum of
   their layer (one byte per option) and the cuts are recovered backwards without back-pointers.
   One option only: segments, pieces of chained trails and of the open path, events outside lo..hi.  An unchanged
   piece that is a whole closed trail is the cut `start 0` of that trail and is free like any other.
   Skip cuts: an event may only take the skip it already uses (co_skip = 0); with co_skip = 1 every skip is
   allowed and the pass is repeated with bans while two events skip the same window. */
typedef struct {
    u64 key;
    u32 gen, val;
} CSlot;
typedef struct {
    CSlot *t;
    u64 cap;
    u32 gen;
    u64 *S, *E, *Ep;
    int *mv;
    i64 wcap;         /* current layer: start words, end words, cheapest way in; Ep: end words of the previous layer */
    unsigned char *d; /* direct tables for k = 1, 2, 3 */
    unsigned char *rel;
    i64 rcap;                    /* cost of every option relative to the minimum of its layer; 255: not allowed */
    i64 *off, *lmin, *cur, lcap; /* per layer: offset into rel, minimum cost, current option (-1: one option only) */
    i64 *ban;
    int nban, bancap;      /* co_skip = 1: (event, window) pairs that are not allowed */
    i64 nfree, nopt, maxm; /* statistics of the last pass: free events, their options, largest layer */
} CO;
/* What the dynamic programme knows about the model is in these functions only, so that a wider model (more cuts,
   other joins) has one place to change each:
     co_nopt, co_opt, co_idx   the cuts a trail may be written from, as a list (number, j-th cut, place of an cut)
     co_join, co_jmax          the cost of joining a piece that ends with the word e to one that starts with s; its maximum
     co_relax                  the same cost over a whole layer: the cheapest way into every cut from the cuts of
                               the layer before, with tables instead of pairs (must agree with co_join)
   Start word, end word, cost and skipped window of an cut are oS_t, oE_t, oD and oSK_t, as everywhere else. */
static inline i64 co_nopt(const Trail *T) {
    return T->ohi - T->olo;
}
static inline i64 co_opt(const Trail *T, i64 j) {
    return T->olo + j;
}
static inline i64 co_idx(const Trail *T, i64 o) {
    return o - T->olo;
}
static inline int co_join(u64 e, u64 s) {
    return dist(e, s);
}
static inline int co_jmax(void) {
    return h;
}
/* Table of one layer step: keeps for key (the last k letters of an end word) the smallest relative cost. */
static inline void co_put(CO *q, u64 mask, u64 key, u32 val) {
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
/* The smallest relative cost stored for key in this generation of the table, or -1. */
static inline int co_get(const CO *q, u64 mask, u64 key) {
    u64 i = hmix(key) & mask;
    while (q->t[i].gen == q->gen) {
        if (q->t[i].key == key)
            return (int)q->t[i].val;
        i = (i + 1) & mask;
    }
    return -1;
}
/* the option an event is, or -1 */
static i64 co_cur(const Ev *x) {
    if (x->kind == EV_OPT)
        return x->a;
    if (x->kind != EV_PIECE)
        return -1;
    const Trail *T = &TR[x->t];
    if (T->fixed || T->c != W + PS[x->a])
        return -1;
    for (i64 j = co_nopt(T) - 1; j >= 0; j--) {
        i64 o = co_opt(T, j);
        if (!OP[o].start && !OP[o].g1) {
            Ev y = make_event(o);
            return (x->l == y.l && x->s == y.s && x->e == y.e) ? o : -1;
        }
    }
    return -1;
}
/* May event i take cut o, which drops an occurrence?  Without anyskip only the occurrence the event drops
   now; with anyskip any occurrence that is not banned for this event. */
static inline int co_skip_ok(const CO *q, const Ev *x, i64 i, const Trail *T, i64 o, int anyskip) {
    i64 r = oSK_t(T, o);
    if (!anyskip)
        return r == x->skip;
    for (int k = 0; k < q->nban; k++)
        if (q->ban[2 * k] == i && q->ban[2 * k + 1] == r)
            return 0;
    return 1;
}
/* mv[j] = min(mv[j], min over the cuts p of the layer before of prel[p] + co_join(Ep[p], S[j])) for the m cuts
   of a layer; prel[p] is the cost of p relative to the minimum of its layer (255: not allowed), rel[j] == 255 marks an
   cut of this layer that is not allowed; mv[j] comes in as co_jmax() */
static void co_relax(CO *q, const unsigned char *prel, i64 pm, const u64 *S, const unsigned char *rel, int *mv, i64 m) {
    u64 need = 16;
    while (need < 2 * (u64)pm)
        need <<= 1;
    if (need > q->cap) {
        free(q->t);
        q->t = calloc(need, sizeof(CSlot));
        q->cap = need;
        q->gen = 0;
        if (!q->t)
            DIE("out of memory");
    }
    u64 mask = need - 1;
    for (int k = h; k >= 4; k--) {
        i64 cnt = 0;
        int sh = 4 * (h - k);
        q->gen++;
        for (i64 j = 0; j < pm; j++)
            if (prel[j] < k) {
                co_put(q, mask, q->Ep[j] & HMASK[k], prel[j]);
                cnt++;
            }
        if (!cnt)
            break;
        for (i64 j = 0; j < m; j++) {
            if (rel[j] == 255 || mv[j] <= h - k)
                continue;
            int v = co_get(q, mask, S[j] >> sh);
            if (v >= 0 && v + h - k < mv[j])
                mv[j] = v + h - k;
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
        for (i64 j = 0; j < m; j++) {
            if (rel[j] == 255 || mv[j] <= h - 3)
                continue;
            int v = d3[S[j] >> (4 * (h - 3))];
            if (v + h - 3 < mv[j])
                mv[j] = v + h - 3;
            if (mv[j] <= h - 2)
                continue;
            v = d2[S[j] >> (4 * (h - 2))];
            if (v + h - 2 < mv[j])
                mv[j] = v + h - 2;
            if (mv[j] == h && !d1[S[j] >> (4 * (h - 1))])
                mv[j] = h - 1;
        }
}
/* events lo..hi may change their cut (their neighbours lo-1 and hi+1 stay); returns the gain in letters */
static i64 co_run(CO *q, Ev *ev, i64 N, i64 lo, i64 hi, int anyskip, int *nchg) {
    i64 a = lo > 0 ? lo - 1 : 0, b = hi + 1 < N ? hi + 1 : N - 1, nl = b - a + 1;
    if (nl > q->lcap) {
        q->lcap = nl + nl / 2 + 64;
        q->off = realloc(q->off, q->lcap * 8);
        q->lmin = realloc(q->lmin, q->lcap * 8);
        q->cur = realloc(q->cur, q->lcap * 8);
    }
    i64 roff = 0, poff = 0, pm = 0, pmin = 0, oldc = 0;
    int pfree = 0;
    u64 pe = 0;
    q->nfree = q->nopt = q->maxm = 0;
    if (nl == N && q->rcap < NO) {
        q->rcap = NO;
        q->rel = realloc(q->rel, (size_t)NO + 1);
    } /* whole sequence: one byte per option, no more */
    for (i64 i = a; i <= b; i++) {
        const Ev *x = &ev[i];
        i64 li = i - a, o0 = (i >= lo && i <= hi) ? co_cur(x) : -1;
        q->cur[li] = o0;
        q->off[li] = roff;
        if (i > a)
            oldc += co_join(ev[i - 1].e, x->s);
        if (o0 < 0) { /* one option */
            i64 cst = 0;
            if (i > a && !pfree)
                cst = pmin + co_join(pe, x->s);
            else if (i > a) {
                const unsigned char *prel = q->rel + poff;
                int best = co_jmax();
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < best) {
                        int v = prel[j] + co_join(q->Ep[j], x->s);
                        if (v < best)
                            best = v;
                    }
                cst = pmin + best;
            }
            q->lmin[li] = pmin = cst;
            pe = x->e;
            pfree = 0;
            continue;
        }
        oldc += oD(o0);
        const Trail *T = &TR[x->t];
        i64 m = co_nopt(T);
        if (m > q->wcap) {
            q->wcap = m + m / 2 + 64;
            q->S = realloc(q->S, q->wcap * 8);
            q->E = realloc(q->E, q->wcap * 8);
            q->Ep = realloc(q->Ep, q->wcap * 8);
            q->mv = realloc(q->mv, q->wcap * sizeof(int));
        }
        if (roff + m > q->rcap) {
            q->rcap = (roff + m) * 2 + 4096;
            q->rel = realloc(q->rel, q->rcap);
        }
        if (!q->d)
            q->d = malloc(16 + 256 + 4096);
        if (!q->S || !q->E || !q->Ep || !q->mv || !q->rel || !q->d)
            DIE("out of memory");
        unsigned char *rel = q->rel + roff;
        const unsigned char *prel = q->rel + poff;
        u64 *S = q->S, *E = q->E;
        int *mv = q->mv;
        for (i64 j = 0; j < m; j++) {
            i64 o = co_opt(T, j);
            if (OP[o].g1 && !co_skip_ok(q, x, i, T, o, anyskip)) {
                rel[j] = 255;
                continue;
            }
            S[j] = oS_t(T, o);
            E[j] = oE_t(T, o);
            rel[j] = 0;
            mv[j] = i == a ? 0 : !pfree ? co_join(pe, S[j]) : co_jmax();
        }
        if (i > a && pfree)
            co_relax(q, prel, pm, S, rel, mv, m);
        int mn = 1 << 20;
        for (i64 j = 0; j < m; j++)
            if (rel[j] != 255) {
                mv[j] += oD(co_opt(T, j));
                if (mv[j] < mn)
                    mn = mv[j];
            }
        for (i64 j = 0; j < m; j++)
            if (rel[j] != 255)
                rel[j] = (unsigned char)(mv[j] - mn);
        q->lmin[li] = pmin = pmin + mn;
        pfree = 1;
        pm = m;
        poff = roff;
        roff += m;
        q->E = q->Ep;
        q->Ep = E;
        q->nfree++;
        q->nopt += m;
        if (m > q->maxm)
            q->maxm = m;
    }
    /* backwards: the option of layer i that reaches the cost wanted by layer i+1 (the current one if it does) */
    i64 newc = q->lmin[nl - 1], want = 0;
    u64 ns = 0;
    int chg = 0;
    for (i64 i = b; i >= a; i--) {
        i64 li = i - a, o0 = q->cur[li];
        Ev *x = &ev[i];
        if (o0 < 0) {
            if (i < b && q->lmin[li] + co_join(x->e, ns) != want)
                DIE("internal error: cluster optimisation (event %lld)", i);
            ns = x->s;
            want = q->lmin[li];
            continue;
        }
        const Trail *T = &TR[x->t];
        const unsigned char *rel = q->rel + q->off[li];
        i64 m = co_nopt(T), pick = -1;
        i64 tgt = i < b ? want : q->lmin[li];
#define COV(j) (q->lmin[li] + rel[j] + (i < b ? co_join(oE_t(T, co_opt(T, j)), ns) : 0))
        if (rel[co_idx(T, o0)] != 255 && COV(co_idx(T, o0)) == tgt)
            pick = co_idx(T, o0);
        for (int pass = 0; pass < 2 && pick < 0; pass++) /* plain cuts first */
            for (i64 j = 0; j < m; j++)
                if (rel[j] != 255 && (pass || !OP[co_opt(T, j)].g1) && COV(j) == tgt) {
                    pick = j;
                    break;
                }
#undef COV
        if (pick < 0)
            DIE("internal error: cluster optimisation (event %lld)", i);
        i64 o = co_opt(T, pick);
        if (o != o0) {
            *x = make_event(o);
            chg++;
        }
        ns = x->s;
        want = q->lmin[li] + rel[pick] - oD(o);
    }
    if (nchg)
        *nchg = chg;
    return oldc - newc;
}
/* co_skip = 1: bans for events that took a skip another event uses; returns the number of new bans */
static int i64pair_cmp(const void *a, const void *b) {
    const i64 *x = a, *y = b;
    return x[0] < y[0] ? -1 : x[0] > y[0] ? 1 : x[1] < y[1] ? -1 : x[1] > y[1];
}
/* After a pass with free choice of the dropped occurrences: every permutation dropped by two or more events
   is banned for all of them but one (the event that dropped it before the pass, if there is one).
   Returns the number of new bans; 0 means the result is valid. */
static int co_clash(CO *q, const Ev *orig, const Ev *ev, i64 N) {
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
    qsort(sk, (size_t)ns, 16, i64pair_cmp);
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
static void co_full(Ev *ev, i64 N) {
    double t0 = wall();
    CO q;
    memset(&q, 0, sizeof q);
    Ev *orig = malloc((size_t)N * sizeof(Ev));
    memcpy(orig, ev, (size_t)N * sizeof(Ev));
    i64 l0 = seq_length(ev, N), l1;
    int chg, rounds = 0;
    for (;;) {
        i64 gain = co_run(&q, ev, N, 0, N - 1, co_skip, &chg);
        l1 = seq_length(ev, N);
        rounds++;
        if (l0 - l1 != gain)
            DIE("internal error: cluster optimisation promised %lld, got %lld", gain, l0 - l1);
        if (!co_skip || !co_clash(&q, orig, ev, N))
            break;
        memcpy(ev, orig, (size_t)N * sizeof(Ev));
    }
    printf(
        "cluster optimisation: %lld -> %lld (%d openings changed; %lld of %lld events free, %lld options, at most %lld per event, %d pass%s, %d bans, %.1fs)\n",
        l0, l1, chg, q.nfree, N, q.nopt, q.maxm, rounds, rounds > 1 ? "es" : "", q.nban, wall() - t0);
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
}

/* ---------- the gain of a cluster optimisation without its cuts, from pass to pass (--coinc).
   In co_run the costs of a layer relative to its minimum (rel) and the step of the minimum from the layer before
   depend only on the event (its trail and the skip it may use), on the event before it and on the rel of that one.
   A thread keeps rel (one byte per cut) and the step of every trail between its passes.  A pass walks the
   sequence and computes only the layers whose event or whose predecessor is new or has come out differently, so the
   work follows the changes since the last pass, not the length of the sequence.  After a pass everything kept agrees
   with the sequence of that pass, which is what makes the next pass right.  The result is the gain co_run would
   return; when it is positive the caller runs co_run for the cuts (and compares the two gains).
   "Everything kept agrees with the sequence of that pass" must also hold for a trail that has no free event in that
   pass (it is written as two segments): nothing is computed for it, so what is kept for it is thrown away.  Without
   that (an earlier version of this file) a trail that is split, stays split over a pass in which the layer before its old place
   changes, and is then one event again behind the same event, was taken with its old costs: the kept gain was wrong
   ("cluster optimisation gains X, the kept one says Y", or the stop "the kept cluster optimisation is above the
   sequence").  The kept gain never changed a sequence or a length by itself, so no word was affected.
   Should the kept costs ever come out above the sequence again, they are thrown away and computed afresh. */
typedef struct CI {
    CO q;
    unsigned char *rel, *nr;
    u64 *sig, *psig;
    int *step;
    i64 maxm;
    int redo;
} CI;
#define CI_FREE(t, skip) ((1ULL << 62) | (u64)(t) << 34 | (u64)((skip) + 1)) /* a free event: its trail and its skip */
#define CI_ONE(e) ((1ULL << 61) | (u64)(e)) /* an event with one option: its end word */
static i64 co_value(Ctx *c) {
    CI *ci = c->ci;
    const Node *nd = c->nd;
    if (!ci) {
        ci = c->ci = calloc(1, sizeof(CI));
        if (!ci)
            DIE("out of memory");
        for (i64 t = 0; t < NT; t++)
            if (co_nopt(&TR[t]) > ci->maxm)
                ci->maxm = co_nopt(&TR[t]);
        ci->rel = malloc((size_t)NO + 1);
        ci->nr = malloc((size_t)ci->maxm + 1);
        ci->sig = calloc((size_t)NT + 1, 8);
        ci->psig = calloc((size_t)NT + 1, 8);
        ci->step = calloc((size_t)NT + 1, sizeof(int));
        ci->q.S = malloc((size_t)(ci->maxm + 1) * 8);
        ci->q.Ep = malloc((size_t)(ci->maxm + 1) * 8);
        ci->q.mv = malloc((size_t)(ci->maxm + 1) * sizeof(int));
        ci->q.d = malloc(16 + 256 + 4096);
        if (!ci->rel || !ci->nr || !ci->sig || !ci->psig || !ci->step || !ci->q.S || !ci->q.Ep || !ci->q.mv || !ci->q.d)
            DIE("out of memory");
    }
    CO *q = &ci->q;
    i64 oldc = 0, tot = 0, pm = 0;
    int pfree = 0, pchg = 0, first = 1;
    u64 pe = 0, psig = 1;
    const Trail *PT = NULL;
    const unsigned char *prel = NULL;
    c->ci_st[0]++;
    for (int id = c->first; id >= 0; id = nd[id].next, first = 0) {
        const Ev *x = &nd[id].v;
        i64 o0 = co_cur(x);
        if (!first)
            oldc += co_join(nd[nd[id].prev].v.e, x->s);
        if (o0 < 0) { /* one option: nothing is kept, the layer after it depends on its end word only */
            if (!first && !pfree)
                tot += co_join(pe, x->s);
            else if (!first) {
                int best = co_jmax();
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < best) {
                        int v = prel[j] + co_join(oE_t(PT, co_opt(PT, j)), x->s);
                        if (v < best)
                            best = v;
                    }
                tot += best;
            }
            pe = x->e;
            pfree = 0;
            psig = CI_ONE(x->e);
            ci->sig[x->t] = 0; /* what is kept for a trail is not kept up while it has no free event */
            continue;
        }
        oldc += oD(o0);
        const Trail *T = &TR[x->t];
        u32 t = x->t;
        i64 m = co_nopt(T);
        u64 sig = CI_FREE(t, x->skip);
        unsigned char *rel = ci->rel + co_opt(T, 0);
        int chg = 0;
        if (ci->sig[t] != sig || ci->psig[t] != psig || (pfree && pchg)) {
            unsigned char *nr = ci->nr;
            u64 *S = q->S;
            int *mv = q->mv;
            for (i64 j = 0; j < m; j++) {
                i64 o = co_opt(T, j);
                if (OP[o].g1 && !co_skip_ok(q, x, 0, T, o, 0)) {
                    nr[j] = 255;
                    continue;
                }
                S[j] = oS_t(T, o);
                nr[j] = 0;
                mv[j] = first ? 0 : !pfree ? co_join(pe, S[j]) : co_jmax();
            }
            if (!first && pfree) {
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < co_jmax())
                        q->Ep[j] = oE_t(PT, co_opt(PT, j)); /* co_relax reads no others */
                co_relax(q, prel, pm, S, nr, mv, m);
            }
            int mn = 1 << 20;
            for (i64 j = 0; j < m; j++)
                if (nr[j] != 255) {
                    mv[j] += oD(co_opt(T, j));
                    if (mv[j] < mn)
                        mn = mv[j];
                }
            for (i64 j = 0; j < m; j++)
                if (nr[j] != 255)
                    nr[j] = (unsigned char)(mv[j] - mn);
            chg = ci->sig[t] != sig || memcmp(nr, rel, (size_t)m) != 0;
            memcpy(rel, nr, (size_t)m);
            ci->sig[t] = sig;
            ci->psig[t] = psig;
            ci->step[t] = mn;
            c->ci_st[1]++;
            c->ci_st[2] += m;
        }
        tot += ci->step[t];
        pfree = 1;
        pchg = chg;
        psig = sig;
        PT = T;
        prel = rel;
        pm = m;
    }
    if (oldc < tot) { /* cannot be: the sequence is itself a path through the layers.  A fault of what is kept */
#ifdef TS_CHECK
        DIE("internal error: the kept cluster optimisation is above the sequence (%lld / %lld)", tot, oldc);
#endif
        if (ci->redo)
            DIE("internal error: the cluster optimisation is above the sequence (%lld / %lld)", tot, oldc);
        printf(
            "internal error: the kept cluster optimisation is above the sequence (%lld / %lld, thread %d, it %lld); all layers are computed again" NL,
            tot, oldc, c->tid, c->it);
        fflush(stdout);
        memset(ci->sig, 0, ((size_t)NT + 1) * 8);
        ci->redo = 1;
        i64 v = co_value(c);
        ci->redo = 0;
        return v;
    }
    return oldc - tot;
}

/* ---------- shared best sequence */
static Ev *G_ev;
static i64 G_N, G_len;
static int G_dirty;
static double G_t0, G_last_ck, G_last_log;
static i64 G_it[256];
static CO G_co;
static i64 G_ver, G_cover, G_cost[3], G_cist[3];
static double G_cosec;
static i64 G_rost[12];
static double G_rosec[2]; /* local re-cutting: the sums of Ctx.ro_st and Ctx.ro_sec */
/* G_ver counts the changes of the best sequence, G_cover is its value at the last cluster optimisation of the best
   sequence; G_cost: passes in the search, passes with a gain, letters gained.  The tables of a pass are shared
   (one byte per cut), so one pass runs at a time. */

/* ==================== own part: moves judged after re-cutting (--reow, --reox), then the search loop ==================== */
/* ---------- local re-cutting: an event takes another cut of its trail where it stands (node_reopen), so a gain
   of the cluster optimisation does not cost a full pass and a reload of the thread.  Three uses:
     ro_window  (--reow)    before a move is accepted or rejected: the best cuts of the events within reow places of
                            its new joins, everything else fixed (co_run on small windows); the move is judged by that
                            length and, if accepted, made with these re-cuts
     co_now     (--coloc)   after co_value has found a gain: backwards through the kept costs as in the second half of
                            co_run (ci_back), the events that come out differently are cut again in place
     ci_move    (--cosync)  after every accepted move: the kept costs of the layers at the changed places are computed
                            again, on from there as long as they come out differently (ci_layer; the same test as in
                            co_value, without the walk over the whole sequence), then backwards from where they stopped
                            changing.  The cuts in place are then again a shortest path through the layers, i.e.
                            the sequence is at the optimum of its order after every accepted move, and that is also
                            what makes the short backward walk right: a shortest path is consistent with the kept
                            costs everywhere, so the walk can stop at the first event before the changed layers that
                            keeps its cut.
   The dynamic programme is reached only through co_run, co_relax and the co_* functions of the model. */
/* a window: the nodes a .. b of the list, their labels */
typedef struct RIv {
    u64 la, lb;
    int a, b;
} RIv;
/* a stretch of layers that were looked at again: its first node, the first node after it (-1: none) */
typedef struct RSt {
    int first, conv;
} RSt;
typedef struct RO {
    CO q;
    Ev *ev;
    int *id;
    i64 cap; /* windows: tables of co_run, the events of a window and their nodes */
    int *rid;
    Ev *rev;
    int nr, rcap; /* re-cuts found: node, new event */
    int *jn;
    int njn, jcap;
    RIv *iv;
    int ivcap; /* joins to look around (left node, right node); windows */
    RelRun *dirty;
    int ndirty, dcap;
    RSt *st;
    int nst, stcap; /* --cosync: nodes whose layer may have changed; stretches */
    int reload;     /* ro_apply had to load the sequence again: node numbers are new */
    int logging, nul, ulcap;
    struct RU *ul;
    unsigned char *ub;
    i64 ubn, ubcap; /* --reox: what ci_layer has overwritten, to take a judged move back */
} RO;
/* a layer as it was: trail, what was kept for it, its costs at ub + off */
typedef struct RU {
    u32 t;
    int step;
    u64 sig, psig;
    i64 off, m;
} RU;
static RO *ro_get(Ctx *c) {
    if (!c->ro && !(c->ro = calloc(1, sizeof(RO))))
        DIE("out of memory");
    return c->ro;
}
/* Logs the event node id had before it was cut again, so that a rejected move can put it back. */
static void ro_add(RO *r, int id, const Ev *x) {
    if (r->nr == r->rcap) {
        r->rcap = r->rcap ? 2 * r->rcap : 256;
        r->rid = realloc(r->rid, (size_t)r->rcap * sizeof(int));
        r->rev = realloc(r->rev, (size_t)r->rcap * sizeof(Ev));
        if (!r->rid || !r->rev)
            DIE("out of memory");
    }
    r->rid[r->nr] = id;
    r->rev[r->nr++] = *x;
}
/* Notes node id as a place where the kept costs have to be computed again. */
static void ro_dirty(const Ctx *c, RO *r, int id) {
    if (id < 0)
        return;
    if (r->ndirty == r->dcap) {
        r->dcap = r->dcap ? 2 * r->dcap : 256;
        r->dirty = realloc(r->dirty, (size_t)r->dcap * sizeof(RelRun));
        if (!r->dirty)
            DIE("out of memory");
    }
    r->dirty[r->ndirty].lab = c->nd[id].lab;
    r->dirty[r->ndirty++].id = id;
}
/* Notes the join between nodes p and q; local re-cutting later looks at the pieces around the noted joins. */
/* p and q are neighbours in the list; -1: the end of the list */
static void ro_join(RO *r, int p, int q) {
    if (r->njn == r->jcap) {
        r->jcap = r->jcap ? 2 * r->jcap : 64;
        r->jn = realloc(r->jn, (size_t)r->jcap * 2 * sizeof(int));
        if (!r->jn)
            DIE("out of memory");
    }
    r->jn[2 * r->njn] = p;
    r->jn[2 * r->njn + 1] = q;
    r->njn++;
}
/* node id takes the event x (its trail from another cut) where it stands: its words leave the index, the new ones
   enter it, and the card is told as for a removed and an inserted node.  Returns the change of the length. */
static i64 node_reopen(Ctx *c, int id, const Ev *x) {
    Node *q = &c->nd[id];
    i64 d = -node_len(c, id);
    if (q->v.skip != x->skip) {
        if (q->v.skip >= 0)
            skp_del(c, q->v.skip);
        if (x->skip >= 0)
            skp_add(c, x->skip);
    }
    index_del(c, id);
    q->v = *x;
    index_add(c, id);
    if (c->G)
        gm_ins(c, id);
    return d + node_len(c, id);
}
/* the join between the positions p and p + 1 has changed: cand[] */
static void cand_fix(Ctx *c, i64 p) {
    if (p < 0 || p + 1 >= c->N)
        return;
    const Node *nd = c->nd;
    int in = dist(nd[c->order[p]].v.e, nd[c->order[p + 1]].v.s) >= 2;
    i64 z = cand_lb(c, p);
    int was = z < c->ncand && c->cand[z] == p;
    if (in == was)
        return;
    if (in) {
        memmove(c->cand + z + 1, c->cand + z, (size_t)(c->ncand - z) * sizeof(int));
        c->cand[z] = (int)p;
        c->ncand++;
    } else {
        memmove(c->cand + z, c->cand + z + 1, (size_t)(c->ncand - z - 1) * sizeof(int));
        c->ncand--;
    }
}
/* the re-cuts noted in ro are made.  order[] and the chains of the trails stay as they are, cand[] is corrected;
   an event whose skipped window changes is noted as dirty (what co_value keeps for its trail no longer fits).  If the
   index has no room for the new words the sequence is loaded again first (ro->reload: the nodes are renumbered).
   Returns the change of the length. */
static i64 ro_apply(Ctx *c) {
    RO *r = c->ro;
    i64 d = 0;
    r->reload = 0;
    if (!r->nr)
        return 0;
    if ((i64)r->nr * ENT_PER + 4096 > c->H.cap - c->H.n) {
        i64 N = c->N;
        for (int q = 0; q < r->nr; q++)
            r->rid[q] = (int)seq_pos(c, r->rid[q], N);
        i64 m = ctx_export(c, c->tmp);
        ctx_load(c, c->tmp, m);
        r->reload = 1;
        r->ndirty = 0;
    }
    for (int q = 0; q < r->nr; q++) {
        int id = r->rid[q];
        if (c->nd[id].v.skip != r->rev[q].skip)
            ro_dirty(c, r, id);
        d += node_reopen(c, id, &r->rev[q]);
    }
    if (r->nr > 64) {
        const Node *nd = c->nd;
        i64 nc = 0;
        for (i64 i = 0; i + 1 < c->N; i++)
            if (dist(nd[c->order[i]].v.e, nd[c->order[i + 1]].v.s) >= 2)
                c->cand[nc++] = (int)i;
        c->ncand = nc;
    } else
        for (int q = 0; q < r->nr; q++) {
            i64 p = seq_pos(c, r->rid[q], c->N);
            cand_fix(c, p - 1);
            cand_fix(c, p);
        }
    c->ro_st[7] += r->nr;
    r->nr = 0;
    return d;
}
/* ---- windows.  An event that no word overlaps stands for the end of the sequence (co_run wants a neighbour). */
static Ev ro_wall(void) {
    Ev x;
    x.kind = EV_SEG;
    x.t = 0;
    x.s = x.e = ~0ULL;
    x.l = 0;
    x.a = 0;
    x.skip = -1;
    return x;
}
static int riv_cmp(const void *a, const void *b) {
    u64 x = ((const RIv *)a)->la, y = ((const RIv *)b)->la;
    return x < y ? -1 : x > y;
}
/* the joins noted with ro_join: the gain of the best re-cutting of the events within reow places of them (windows that
   touch are one window), all other events staying as they are.  The re-cuts go to ro->rid / ro->rev.
   -1: not tried (more than reocap cuts in the windows) */
static i64 ro_window(Ctx *c) {
    RO *r = c->ro;
    const Node *nd = c->nd;
    int m = 0, k = 0;
    i64 gain = 0;
    double no = 0;
    r->nr = 0;
    if (r->njn > r->ivcap) {
        r->ivcap = 2 * r->njn + 16;
        r->iv = realloc(r->iv, (size_t)r->ivcap * sizeof(RIv));
        if (!r->iv)
            DIE("out of memory");
    }
    RIv *iv = r->iv;
    for (int z = 0; z < r->njn; z++) {
        int a = r->jn[2 * z] >= 0 ? r->jn[2 * z] : r->jn[2 * z + 1],
            b = r->jn[2 * z + 1] >= 0 ? r->jn[2 * z + 1] : r->jn[2 * z];
        if (a < 0)
            continue;
        for (int q = 1; q < reow && nd[a].prev >= 0; q++)
            a = nd[a].prev;
        for (int q = 1; q < reow && nd[b].next >= 0; q++)
            b = nd[b].next;
        iv[m].a = a;
        iv[m].b = b;
        iv[m].la = nd[a].lab;
        iv[m].lb = nd[b].lab;
        m++;
    }
    r->njn = 0;
    if (!m)
        return 0;
    qsort(iv, (size_t)m, sizeof(RIv), riv_cmp);
    for (int z = 1; z < m; z++) {
        if (iv[z].la <= iv[k].lb || nd[iv[k].b].next == iv[z].a) {
            if (iv[z].lb > iv[k].lb) {
                iv[k].lb = iv[z].lb;
                iv[k].b = iv[z].b;
            }
        } else
            iv[++k] = iv[z];
    }
    m = k + 1;
    for (int z = 0; z < m; z++)
        for (int id = iv[z].a;; id = nd[id].next) {
            if (nd[id].v.kind == EV_OPT)
                no += (double)co_nopt(&TR[nd[id].v.t]);
            if (id == iv[z].b)
                break;
        }
    if (no > reocap)
        return -1;
    for (int z = 0; z < m; z++) {
        i64 cnt = 1, n2 = 1;
        for (int id = iv[z].a; id != iv[z].b; id = nd[id].next)
            cnt++;
        if (cnt + 4 > r->cap) {
            r->cap = 2 * cnt + 64;
            r->ev = realloc(r->ev, (size_t)r->cap * sizeof(Ev));
            r->id = realloc(r->id, (size_t)r->cap * sizeof(int));
            if (!r->ev || !r->id)
                DIE("out of memory");
        }
        Ev *ev = r->ev;
        int *ids = r->id, lf = nd[iv[z].a].prev, rt = nd[iv[z].b].next, chg;
        ev[0] = lf >= 0 ? nd[lf].v : ro_wall();
        for (int id = iv[z].a;; id = nd[id].next) {
            ids[n2] = id;
            ev[n2++] = nd[id].v;
            if (id == iv[z].b)
                break;
        }
        ev[n2] = rt >= 0 ? nd[rt].v : ro_wall();
        ev[n2 + 1] =
            ev[n2]; /* never read: co_run keeps a byte per cut of the model for a range that ends with its last event */
        i64 g = co_run(&r->q, ev, n2 + 2, 1, n2 - 1, 0, &chg);
        c->ro_st[1] += r->q.nfree;
        c->ro_st[2] += r->q.nopt;
        if (g <= 0)
            continue;
        gain += g;
        for (i64 i = 1; i < n2; i++)
            if (ev[i].kind != nd[ids[i]].v.kind || ev[i].a != nd[ids[i]].v.a)
                ro_add(r, ids[i], &ev[i]);
    }
    return gain;
}
/* ---- while a move is judged (--reox) the layers that are overwritten are kept, so that a rejected move leaves the
   kept costs as they were */
static void ci_log(Ctx *c, u32 t, i64 m) {
    RO *r = c->ro;
    CI *ci = c->ci;
    if (!r || !r->logging)
        return;
    if (r->nul == r->ulcap) {
        r->ulcap = r->ulcap ? 2 * r->ulcap : 64;
        r->ul = realloc(r->ul, (size_t)r->ulcap * sizeof(RU));
        if (!r->ul)
            DIE("out of memory");
    }
    if (r->ubn + m > r->ubcap) {
        r->ubcap = 2 * (r->ubn + m) + 65536;
        r->ub = realloc(r->ub, (size_t)r->ubcap);
        if (!r->ub)
            DIE("out of memory");
    }
    RU *u = &r->ul[r->nul++];
    u->t = t;
    u->step = ci->step[t];
    u->sig = ci->sig[t];
    u->psig = ci->psig[t];
    u->off = r->ubn;
    u->m = m;
    if (m)
        memcpy(r->ub + r->ubn, ci->rel + co_opt(&TR[t], 0), (size_t)m);
    r->ubn += m;
}
/* Takes back what a judged move wrote into the kept costs, newest layer first. */
static void ci_undo(Ctx *c) {
    RO *r = c->ro;
    CI *ci = c->ci;
    for (int k = r->nul - 1; k >= 0; k--) {
        const RU *u = &r->ul[k];
        ci->step[u->t] = u->step;
        ci->sig[u->t] = u->sig;
        ci->psig[u->t] = u->psig;
        if (u->m)
            memcpy(ci->rel + co_opt(&TR[u->t], 0), r->ub + u->off, (size_t)u->m);
    }
    r->nul = 0;
    r->ubn = 0;
}
/* ---- the kept costs of co_value, one layer: the layer of node id is computed again if its event, the event before it
   or (pchg) the costs of the layer before it are not those of the last time; the computation is the one of co_value.
   0: nothing computed (or an event with one option), 1: computed, the same costs, 2: computed, other costs */
static int ci_layer(Ctx *c, int id, int pchg) {
    CI *ci = c->ci;
    CO *q = &ci->q;
    const Node *nd = c->nd;
    const Ev *x = &nd[id].v;
    u32 t = x->t;
    if (co_cur(x) < 0) {
        if (ci->sig[t]) {
            ci_log(c, t, 0);
            ci->sig[t] = 0;
        }
        return 0;
    }
    int p = nd[id].prev, first = p < 0, pfree = 0;
    u64 pe = 0, psig = 1;
    const Trail *PT = NULL;
    const unsigned char *prel = NULL;
    i64 pm = 0;
    if (!first) {
        const Ev *y = &nd[p].v;
        if (co_cur(y) < 0) {
            pe = y->e;
            psig = CI_ONE(y->e);
        } else {
            pfree = 1;
            PT = &TR[y->t];
            prel = ci->rel + co_opt(PT, 0);
            pm = co_nopt(PT);
            psig = CI_FREE(y->t, y->skip);
        }
    }
    const Trail *T = &TR[t];
    i64 m = co_nopt(T);
    u64 sig = CI_FREE(t, x->skip);
    if (ci->sig[t] == sig && ci->psig[t] == psig && !(pfree && pchg))
        return 0;
    unsigned char *rel = ci->rel + co_opt(T, 0), *nr = ci->nr;
    u64 *S = q->S;
    int *mv = q->mv;
    for (i64 j = 0; j < m; j++) {
        i64 o = co_opt(T, j);
        if (OP[o].g1 && !co_skip_ok(q, x, 0, T, o, 0)) {
            nr[j] = 255;
            continue;
        }
        S[j] = oS_t(T, o);
        nr[j] = 0;
        mv[j] = first ? 0 : !pfree ? co_join(pe, S[j]) : co_jmax();
    }
    if (!first && pfree) {
        for (i64 j = 0; j < pm; j++)
            if (prel[j] < co_jmax())
                q->Ep[j] = oE_t(PT, co_opt(PT, j));
        co_relax(q, prel, pm, S, nr, mv, m);
    }
    int mn = 1 << 20;
    for (i64 j = 0; j < m; j++)
        if (nr[j] != 255) {
            mv[j] += oD(co_opt(T, j));
            if (mv[j] < mn)
                mn = mv[j];
        }
    for (i64 j = 0; j < m; j++)
        if (nr[j] != 255)
            nr[j] = (unsigned char)(mv[j] - mn);
    int chg = ci->sig[t] != sig || memcmp(nr, rel, (size_t)m) != 0;
    ci_log(c, t, m);
    memcpy(rel, nr, (size_t)m);
    ci->sig[t] = sig;
    ci->psig[t] = psig;
    ci->step[t] = mn;
    c->ci_st[1]++;
    c->ci_st[2] += m;
    return chg ? 2 : 1;
}
/* backwards through the kept costs from node conv, whose event stays (-1: from the end of the sequence), as in the
   second half of co_run: every event takes the cut that reaches the cost its successor asks for, its own if that
   does, else the first plain one, else the first.  Stops at the first event with a label below stop that keeps its
   cut and returns it (-1: the front was reached).  The re-cuts go to ro->rid / ro->rev.
   In units of a layer: an cut j of a free layer costs rel[j] above the minimum of the layer; the cut picked in
   the layer after it asks the layer before for  step + rel[pick] - D(pick),  an event with one option for the cheapest
   way into it (not kept: found again here). */
static int ci_back(Ctx *c, int conv, u64 stop) {
    CI *ci = c->ci;
    RO *r = c->ro;
    const Node *nd = c->nd;
    int id, have = 0, one = 0;
    i64 need = 0;
    u64 ns = 0;
    if (conv < 0)
        id = c->last;
    else {
        const Ev *x = &nd[conv].v;
        i64 o = co_cur(x);
        ns = x->s;
        have = 1;
        id = nd[conv].prev;
        if (o < 0)
            one = 1;
        else {
            const Trail *T = &TR[x->t];
            need = ci->step[x->t] + (ci->rel + co_opt(T, 0))[co_idx(T, o)] - oD(o);
        }
    }
    for (; id >= 0; id = nd[id].prev) {
        const Ev *x = &nd[id].v;
        i64 o0 = co_cur(x);
        if (o0 < 0) {
            ns = x->s;
            have = one = 1;
            if (nd[id].lab < stop)
                return id;
            continue;
        }
        const Trail *T = &TR[x->t];
        const unsigned char *rel = ci->rel + co_opt(T, 0);
        i64 m = co_nopt(T), pick = -1, j0 = co_idx(T, o0);
        if (one) {
            int best = co_jmax();
            for (i64 j = 0; j < m; j++)
                if (rel[j] < best) {
                    int v = rel[j] + co_join(oE_t(T, co_opt(T, j)), ns);
                    if (v < best)
                        best = v;
                }
            need = best;
        }
#define CBV(j) ((i64)rel[j] + (have ? co_join(oE_t(T, co_opt(T, j)), ns) : 0))
        if (rel[j0] != 255 && CBV(j0) == need)
            pick = j0;
        for (int pass = 0; pass < 2 && pick < 0; pass++)
            for (i64 j = 0; j < m; j++)
                if (rel[j] != 255 && (pass || !OP[co_opt(T, j)].g1) && CBV(j) == need) {
                    pick = j;
                    break;
                }
#undef CBV
        if (pick < 0)
            DIE("internal error: no way back through the kept cluster optimisation (node %d, it %lld)", id, c->it);
        i64 o = co_opt(T, pick);
        if (o != o0) {
            Ev y = make_event(o);
            ro_add(r, id, &y);
            ns = y.s;
        } else
            ns = x->s;
        need = ci->step[x->t] + rel[pick] - oD(o);
        one = 0;
        have = 1;
        if (o == o0 && nd[id].lab < stop)
            return id;
    }
    return -1;
}
/* the nodes noted as dirty, forwards: their layers and what follows from them.  A stretch runs on while a layer comes
   out differently or the next node is dirty too.  0: given up (more than `budget` cuts computed) */
static int ci_fwd(Ctx *c, double budget) {
    RO *r = c->ro;
    const Node *nd = c->nd;
    int di = 0;
    i64 o0 = c->ci_st[2];
    r->nst = 0;
    qsort(r->dirty, (size_t)r->ndirty, sizeof(RelRun), rel_cmp);
    while (di < r->ndirty) {
        int id = r->dirty[di].id, first = id, conv, pchg = 0;
        for (;;) {
            u64 lab = nd[id].lab;
            while (di < r->ndirty && r->dirty[di].lab <= lab)
                di++;
            pchg = ci_layer(c, id, pchg) == 2;
            if ((double)(c->ci_st[2] - o0) > budget) {
                r->ndirty = 0;
                return 0;
            }
            int nx = nd[id].next;
            if (nx < 0) {
                conv = -1;
                break;
            }
            if (!pchg && !(di < r->ndirty && r->dirty[di].id == nx)) {
                conv = nx;
                break;
            }
            id = nx;
        }
        if (r->nst == r->stcap) {
            r->stcap = r->stcap ? 2 * r->stcap : 64;
            r->st = realloc(r->st, (size_t)r->stcap * sizeof(RSt));
            if (!r->st)
                DIE("out of memory");
        }
        r->st[r->nst].first = first;
        r->st[r->nst++].conv = conv;
    }
    r->ndirty = 0;
    return 1;
}
/* backwards through the stretches of ci_fwd, the last one first; a walk that ends inside an earlier stretch goes on
   from there.  The re-cuts come out in the order of the walk: from the back of the sequence to its front. */
static void ci_bwd(Ctx *c) {
    RO *r = c->ro;
    const Node *nd = c->nd;
    int z = 0, havez = 0;
    r->nr = 0;
    for (int k = r->nst - 1; k >= 0; k--) {
        int conv = r->st[k].conv;
        u64 fl = nd[r->st[k].first].lab;
        if (havez) {
            if (z < 0)
                break;
            u64 zl = nd[z].lab;
            if (zl < fl)
                continue;
            if (conv < 0 || zl <= nd[conv].lab)
                conv = z;
        }
        z = ci_back(c, conv, fl);
        havez = 1;
    }
}
/* the nodes noted as dirty: their layers, then the cuts in place.  Returns the gain. */
static i64 ci_sync(Ctx *c) {
    RO *r = c->ro;
    i64 gain = 0;
    while (r->ndirty) {
        ci_fwd(c, 1e300);
        ci_bwd(c);
        if (!r->nr)
            break;
        gain -= ro_apply(
            c); /* an event that has lost its skip is dirty again: no gain can come of that, the cuts in place stay a shortest path */
    }
    return gain;
}
/* what the re-cuts noted in ro (in the order of ci_bwd) gain, without making them */
static i64 ro_gain(const Ctx *c) {
    const RO *r = c->ro;
    const Node *nd = c->nd;
    i64 d = 0;
    for (int q = 0; q < r->nr; q++) {
        int id = r->rid[q], a = nd[id].prev, b = nd[id].next;
        const Ev *x = &nd[id].v, *y = &r->rev[q];
        d += y->l - x->l;
        if (a >= 0)
            d += dist(q + 1 < r->nr && r->rid[q + 1] == a ? r->rev[q + 1].e : nd[a].v.e, y->s) - dist(nd[a].v.e, x->s);
        if (b >= 0 && !(q > 0 && r->rid[q - 1] == b))
            d += dist(y->e, nd[b].v.s) - dist(x->e, nd[b].v.s);
    }
    return -d;
}
/* dirty after a move: the new nodes, the nodes after them, the nodes that stand where a removed one stood */
static void ci_dirty_move(Ctx *c) {
    RO *r = c->ro;
    const Node *nd = c->nd;
    for (int q = 0; q < c->ninslog; q++) {
        int id = c->inslog[q];
        ro_dirty(c, r, id);
        ro_dirty(c, r, nd[id].next);
    }
    for (int q = 0; q < c->nremlog; q++) {
        int id = c->remlog[q];
        do
            id = nd[id].next;
        while (id >= 0 && !nd[id].alive);
        ro_dirty(c, r, id >= 0 ? id : c->last);
    }
}
/* --reox (with --cosync): the move that has just been made in the list, before it is accepted or rejected: what the
   cluster optimisation of the whole new order gains.  The kept costs are brought to the new order (the old layers are
   logged: ci_undo takes the move back) and the walk backwards gives the re-cuts (ro->rid / ro->rev), which are not
   made here.  -1: not judged (more than reocap cuts to compute); the kept costs are as before then. */
static i64 ci_judge(Ctx *c) {
    RO *r = c->ro;
    r->logging = 1;
    r->nul = 0;
    r->ubn = 0;
    r->ndirty = 0;
    ci_dirty_move(c);
    int ok = ci_fwd(c, reocap);
    r->logging = 0;
    if (!ok) {
        ci_undo(c);
        return -1;
    }
    ci_bwd(c);
    i64 g = ro_gain(c);
#if defined(TS_CHECK) && TS_CHECK > 1
    {
        Ev *chk = malloc((size_t)(c->N + 1) * sizeof(Ev));
        i64 cm = ctx_export(c, chk), cg;
        int cc;
#pragma omp critical(co)
        cg = co_run(&G_co, chk, cm, 0, cm - 1, 0, &cc);
        if (cg != g)
            DIE("check: a judged move gains %lld by re-opening, the cluster optimisation says %lld (it %lld)", g, cg,
                c->it);
        free(chk);
    }
#endif
    return g;
}
/* --coloc: the gain val of co_value is taken in place.  *nchg: the number of events cut again */
static i64 co_take(Ctx *c, i64 val, int *nchg) {
    RO *r = ro_get(c);
    if (nchg)
        *nchg = 0;
    if (val <= 0)
        return 0;
#ifdef TS_CHECK /* the checking build runs the full optimisation too: the same gain, the same cuts */
    Ev *chk = malloc((size_t)(c->N + 1) * sizeof(Ev));
    i64 cm = ctx_export(c, chk), cg;
    int cc;
#pragma omp critical(co)
    cg = co_run(&G_co, chk, cm, 0, cm - 1, 0, &cc);
    if (cg != val)
        DIE("check: cluster optimisation gains %lld, the kept one says %lld (it %lld)", cg, val, c->it);
#endif
    r->nr = 0;
    r->ndirty = 0;
    ci_back(c, -1, 0);
    if (nchg)
        *nchg = r->nr;
    i64 d = ro_apply(c);
    if (d != -val)
        DIE("internal error: re-opening in place gains %lld, the kept cluster optimisation says %lld (it %lld)", -d,
            val, c->it);
    c->cur -= val;
#ifdef TS_CHECK
    {
        i64 p = 0;
        for (int id = c->first; id >= 0; id = c->nd[id].next, p++)
            if (c->nd[id].v.kind != chk[p].kind || c->nd[id].v.a != chk[p].a)
                DIE("check: re-opening in place differs from the cluster optimisation at event %lld (it %lld)", p,
                    c->it);
        if (c->cur != ctx_length(c))
            DIE("check: length %lld after re-opening in place, kept %lld (it %lld)", ctx_length(c), c->cur, c->it);
        free(chk);
    }
#endif
    if (cosync) {
        i64 g2 = ci_sync(c);
        if (g2)
            DIE("internal error: a gain of %lld after the cluster optimisation in place (it %lld)", g2, c->it);
    } else
        r->ndirty = 0; /* without --cosync the next pass of co_value sees the lost skips itself */
    return val;
}
static i64 co_now(Ctx *c, int *nchg) {
    return co_take(c, co_value(c), nchg);
}
/* the current sequence of a thread after a gain in place: its best, and the best of all if it is */
static void best_note(Ctx *c, const char *how, int chg) {
    if (c->cur >= c->best_len)
        return;
    c->best_len = c->cur;
#pragma omp critical(gbest)
    if (c->cur < G_len) {
        printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, %s, %d openings)\n", wall() - G_t0, G_len, c->cur,
               c->tid, c->it, how, chg);
        fflush(stdout);
        G_N = ctx_export(c, G_ev);
        G_len = c->cur;
        G_dirty = 1;
        G_cover = ++G_ver;
    }
}
/* --cosync, after an accepted move: c->inslog are the nodes it inserted, c->remlog the nodes it removed (reload: they
   are gone, the whole sequence is walked instead).  Dirty are the new nodes, the nodes after them and the nodes that
   now stand where a removed one stood; the last node if the end of the sequence has changed.  Returns the gain. */
static i64 ci_move(Ctx *c, int reload) {
    RO *r = ro_get(c);
    double t0 = wall();
    i64 g;
    if (reload) {
        r->ndirty = 0;
        g = co_now(c, NULL);
        c->cur += g;
    } else {
        ci_dirty_move(c);
        g = ci_sync(c);
    }
    c->ro_st[8]++;
    c->ro_st[9] += g > 0;
    c->ro_st[10] += g;
    c->ro_sec[1] += wall() - t0;
    return g;
}
/* --coit with --coloc: the pass on the current sequence, in place.  With --cosync there is nothing to find: the pass
   only checks that (a fault is reported and repaired; the checking build stops). */
static void co_pass_loc(Ctx *c) {
    double t1 = wall();
    int chg = 0;
    i64 l0 = c->ci_st[1], val = co_value(c), g;
    if (cosync && (val || c->ci_st[1] != l0)) {
#ifdef TS_CHECK
        DIE("check: the kept cluster optimisation was out of step (%lld layers, gain %lld, it %lld)", c->ci_st[1] - l0,
            val, c->it);
#endif
        printf(
            "internal error: the kept cluster optimisation was out of step (thread %d, it %lld: %lld layers, gain %lld)" NL,
            c->tid, c->it, c->ci_st[1] - l0, val);
        fflush(stdout);
    }
#ifdef TS_CHECK
    if (cosync) {
        Ev *chk = malloc((size_t)(c->N + 1) * sizeof(Ev));
        i64 cm = ctx_export(c, chk), cg;
        int cc;
#pragma omp critical(co)
        cg = co_run(&G_co, chk, cm, 0, cm - 1, 0, &cc);
        if (cg)
            DIE("check: the sequence is %lld above the optimum of its order (it %lld)", cg, c->it);
        free(chk);
    }
#endif
    g = co_take(c, val, &chg);
    c->co_st[0]++;
    c->co_st[1] += g > 0;
    c->co_st[2] += g;
    best_note(c, "cluster optimisation in place", chg);
    c->co_sec += wall() - t1;
}

/* --coit: cluster optimisation of the whole current sequence of a thread, then of the best sequence if that has
   changed since its last pass.  A sequence that gains is loaded again (index, kept arrays, GPU mirror). */
static void co_pass(Ctx *c) {
    if (coloc) {
        co_pass_loc(c);
        return;
    }
    double t1 = wall();
    i64 m = 0, g = 0, bl = 0, ver = -1, val = coinc ? co_value(c) : -1;
    int chg = 0, full = val != 0;
#ifdef TS_CHECK
    full = 1; /* the checking build compares every pass */
#endif
    if (full) {
        m = ctx_export(c, c->tmp);
#pragma omp critical(co)
        g = co_run(&G_co, c->tmp, m, 0, m - 1, 0, &chg);
        if (val >= 0 &&
            g !=
                val) { /* a fault of co_value: the pass itself is right (co_run checks its own result), so the search goes on without --coinc */
#ifdef TS_CHECK
            DIE("internal error: cluster optimisation gains %lld, the kept one says %lld (it %lld)", g, val, c->it);
#endif
            printf(
                "internal error: cluster optimisation gains %lld, the kept one says %lld (thread %d, it %lld); --coinc is switched off" NL,
                g, val, c->tid, c->it);
            fflush(stdout);
            coinc = 0;
        }
    }
    c->co_st[0]++;
    c->co_st[1] += g > 0;
    c->co_st[2] += g > 0 ? g : 0;
    if (g > 0) {
        ctx_load(c, c->tmp, m);
        c->cur -= g;
        if (c->cur != ctx_length(c))
            DIE("internal error: cluster optimisation promised %lld, got %lld", c->cur, ctx_length(c));
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
                G_cover = ++G_ver;
            }
        }
    }
#pragma omp critical(gbest)
    if (G_cover != G_ver) {
        m = G_N;
        bl = G_len;
        ver = G_ver;
        memcpy(c->tmp, G_ev, (size_t)m * sizeof(Ev));
    }
    if (ver >= 0) {
#pragma omp critical(co)
        g = co_run(&G_co, c->tmp, m, 0, m - 1, 0, &chg);
        if (g > 0 && seq_length(c->tmp, m) != bl - g)
            DIE("internal error: cluster optimisation promised %lld, got %lld", bl - g, seq_length(c->tmp, m));
        c->co_st[0]++;
        c->co_st[1] += g > 0;
        c->co_st[2] += g > 0 ? g : 0;
#pragma omp critical(gbest)
        if (G_ver == ver) {
            if (g > 0) {
                printf(
                    "t=%.0fs: best %lld -> %lld (thread %d, it %lld, cluster optimisation of the best sequence, %d openings)\n",
                    wall() - G_t0, G_len, bl - g, c->tid, c->it, chg);
                fflush(stdout);
                memcpy(G_ev, c->tmp, (size_t)m * sizeof(Ev));
                G_len = bl - g;
                G_dirty = 1;
                ++G_ver;
            }
            G_cover = G_ver;
        }
    }
    c->co_sec += wall() - t1;
}

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
    if (coloc) {
        int chg;
        double t1 = wall();
        i64 g = co_now(c, &chg);
        c->co_st[0]++;
        c->co_st[1] += g > 0;
        c->co_st[2] += g;
        c->co_sec += wall() - t1;
        best_note(c, "cluster optimisation in place", chg);
    }
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    double ts0 = wall();
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit && (maxwork <= 0 || c->work < maxwork)) {
        c->it++;
        c->nzit = hmix(c->nzk + (u64)c->it);
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
        }
        /* a block move that is not counted leaves the iteration number where it was: periodic steps run once */
        if (coit > 0 && c->it != c->lastper && (c->it + coit * c->tid / NTHR) % coit == 0)
            co_pass(c);
        c->lastper = c->it;
        nd = c->nd;
        double frac = (wall() - G_t0) / tlimit, temp = tf * T0 * (1 - frac) + 0.05;
#if defined(TS_CHECK) && TS_CHECK > 1
        seq_check(c);
#endif
        double t_it = opstats ? wall() : 0, w_it = c->work;
        int *order = c->order, *cand = c->cand, *rel = c->rel;
        i64 N = c->N, ncand = c->ncand;
#define EVT(i) (nd[order[i]].v)
#define RS(r) ((r) ? cand[(r) - 1] + 1 : 0) /* run r: positions RS(r) .. RE(r) */
#define RE(r) ((r) < ncand ? cand[r] : (int)N - 1)
#define JD(i) dist(EVT(i).e, EVT((i) + 1).s) /* cost of the join i -> i+1 */
#define NOPEN(t) (TR[t].ohi - TR[t].olo)
        int k = (int)rndint(c, 1, kmax);
        i64 nrem = 0;
        double mode = rndu(c);
        int op, blk = 0, b0 = 0, b1 = 0; /* removal rule; block move of the events b0 .. b1 */
        if (!ops_set)
            op = mode < prel ? 0 : mode < 0.5 + prel / 2 ? 1 : mode < 0.75 ? 2 : 3;
        else {
            double ws = 0, z;
            for (int o = 0; o < NOPS; o++)
                ws += opw[o];
            z = mode * ws;
            op = 0;
            for (int o = 0; o < NOPS; o++)
                if (opw[o] > 0) {
                    op = o;
                    if (z < opw[o])
                        break;
                    z -= opw[o];
                }
        }
#define REMOVE(tt)                          \
    do {                                    \
        u32 t_ = (tt);                      \
        if (!c->rem[t_] && !TR[t_].fixed) { \
            c->rem[t_] = 1;                 \
            c->pend[nrem++] = t_;           \
        }                                   \
    } while (0)
        if (op == 0) {
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
                if (nopt <= 600000)
                    c->work += (double)nopt;
                for (int i = RS(X); i <= RE(X); i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), id = rel[z];
                    rel[z] = rel[--nrel];
                    for (;; id = nd[id].next) {
                        REMOVE(nd[id].v.t);
                        if (nd[id].next < 0 || dist(nd[id].v.e, nd[nd[id].next].v.s) >= 2)
                            break;
                    }
                }
            }
        } else if (op == 1) {
            i64 j = ncand ? cand[rndn(c, ncand)] : rndn(c, N - 1);
            i64 lo = j - rndint(c, 0, k);
            if (lo < 0)
                lo = 0;
            for (i64 i = lo; i < N && i < lo + k; i++)
                REMOVE(EVT(i).t);
        } else if (op == 2) {
            for (int q = 0; q < k; q++)
                REMOVE(EVT(rndn(c, N)).t);
        } else if (op == 4) {
            /* windows at two or three expensive joins; half of the time the later joins are related to the first one
               (the event after one join could follow the event before the other at cost <= 2; at most 4096 joins
               are looked at) */
            int segs = (int)rndint(c, 2, 3), len = k / segs > 1 ? k / segs : 1, shaw = rndu(c) < 0.5;
            i64 j0 = -1;
            for (int q = 0; q < segs; q++) {
                i64 j = ncand ? cand[rndn(c, ncand)] : rndn(c, N - 1);
                if (q && shaw && ncand) {
                    i64 z0 = rndn(c, ncand);
                    for (i64 z = 0; z < ncand && z < 4096; z++) {
                        i64 j2 = cand[(z0 + z) % ncand];
                        if (j2 != j0 && (dist(EVT(j0).e, EVT(j2 + 1).s) <= 2 || dist(EVT(j2).e, EVT(j0 + 1).s) <= 2)) {
                            j = j2;
                            break;
                        }
                    }
                }
                if (!q)
                    j0 = j;
                i64 lo = j + 1 - rndint(c, 0, len);
                if (lo < 0)
                    lo = 0;
                for (i64 i = lo; i < N && i < lo + len; i++)
                    REMOVE(EVT(i).t);
            }
        } else if (op == 5) {
            /* worst removal: the trails whose removal shortens the rest most, chosen with a bias towards the top.
               The events (all of them, or worstn random ones of a long sequence) are sorted by their gain; a rank is
               drawn as u^3 and a random event of the same gain is taken. */
            enum { GB = 48, G0 = 16 };
            i64 cntg[GB] = {0}, pos[GB], M = N <= worstn ? N : worstn;
            int *smp = c->wk, *gn = c->wc, *srt = rel, dp = 0;
            for (i64 z = 0; z < M; z++) {
                i64 i = M == N ? z : rndn(c, N);
                int d0 = i == 0 ? 0 : M == N ? dp : JD(i - 1), d1 = i + 1 < N ? JD(i) : 0;
                int g = d0 + d1 - (i > 0 && i + 1 < N ? dist(EVT(i - 1).e, EVT(i + 1).s) : 0) +
                        (EVT(i).kind == EV_OPT ? oD(EVT(i).a) : 0) + G0;
                g = g < 0 ? 0 : g >= GB ? GB - 1 : g;
                smp[z] = (int)i;
                gn[z] = g;
                cntg[g]++;
                dp = d1;
            }
            {
                i64 z = 0;
                for (int g = GB - 1; g >= 0; g--) {
                    pos[g] = z;
                    z += cntg[g];
                }
            }
            for (i64 z = 0; z < M; z++)
                srt[pos[gn[z]]++] = smp[z]; /* pos[g] is now the end of the events of gain g */
            for (int q = 0; q < k; q++) {
                double u = rndu(c);
                i64 z = (i64)(u * u * u * (double)M);
                int g = GB - 1;
                while (g > 0 && z >= pos[g])
                    g--;
                REMOVE(EVT(srt[pos[g] - cntg[g] + rndn(c, cntg[g])]).t);
            }
        } else if (op == 7) {
            /* one whole run that consists of big trails only (2 .. runcap events), nothing else: a random run is
               drawn until one fits (256 draws, then the iteration is given up) */
            int nrun = (int)ncand + 1, X = -1;
            for (int tries = 0; tries < 256 && X < 0; tries++) {
                int r = (int)rndn(c, nrun), ok = RE(r) - RS(r) + 1 >= 2 && RE(r) - RS(r) + 1 <= runcap;
                for (int i = RS(r); i <= RE(r) && ok; i++)
                    if (NOPEN(EVT(i).t) <= splitmax)
                        ok = 0;
                if (ok)
                    X = r;
            }
            if (X < 0)
                continue;
            for (int i = RS(X); i <= RE(X); i++)
                REMOVE(EVT(i).t);
        } else if (op == 6) {
            /* block move: a run, two runs, the first events of a run (the part after an expensive join), or a
               random window */
            double u = rndu(c);
            if (ncand && u < 0.9) {
                i64 r = rndn(c, ncand + 1) - 1;
                int cap = u < 0.75 ? 200 : (int)rndint(c, 1, 3 * k), runs = u >= 0.6 && u < 0.75 ? 2 : 1;
                b0 = r < 0 ? 0 : cand[r] + 1;
                b1 = b0;
                while (b1 + 1 < N && b1 - b0 + 1 < cap && (JD(b1) < 2 || --runs > 0))
                    b1++;
            } else {
                b0 = (int)rndn(c, N);
                b1 = b0 + (int)rndint(c, 0, 2 * k);
                if (b1 > N - 1)
                    b1 = (int)N - 1;
            }
            if (blkfree) {
                c->it--;
                c->xit++;
            }
            blk = 1;
            for (int i = b0; i <= b1; i++)
                if (TR[EVT(i).t].fixed)
                    blk = 0;
            if (!blk || N - (b1 - b0 + 1) < 3)
                continue;
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
        if (!nrem && !blk)
            continue;
        if (!blk && !nbig && focus > 0 && rndu(c) < focus) {
            for (i64 q = 0; q < nrem; q++)
                c->rem[c->pend[q]] = 0;
            continue;
        }
        /* destroy: the nodes of the removed trails, in the order of the sequence */
        c->nremlog = c->ninslog = 0;
        c->relabeled = 0;
        int nn0 = c->nn, nrk = 0, nrth = 0;
        i64 dl = 0; /* dl: change of the length; rth: (trail, head of its nodes) to undo */
        if (blk) {
            /* the events b0 .. b1 as they are (a trail written as two segments may keep one of them where it is): the
               new nodes join the chains of their trails, the old ones leave them when the move is accepted */
            for (int i = b0; i <= b1; i++) {
                int id = order[i];
                u32 t_ = nd[id].v.t;
                if (!c->rem[t_]) {
                    c->rem[t_] = 1;
                    c->rth[2 * nrth] = (int)t_;
                    c->rth[2 * nrth + 1] = c->thead[t_];
                    nrth++;
                }
                if (nrk == c->rkcap) {
                    c->rkcap = c->rkcap ? c->rkcap * 2 : 256;
                    c->rk = realloc(c->rk, (size_t)c->rkcap * sizeof(i64));
                }
                c->rk[nrk++] = ((i64)i << 32) | id;
            }
            for (int q = 0; q < nrth; q++)
                c->rem[c->rth[2 * q]] = 0;
        } else {
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
            nrth = (int)nrem;
            qsort(c->rk, (size_t)nrk, sizeof(i64), i64_cmp);
        }
        for (int q = 0; q < nrk; q++) {
            int id = (int)(c->rk[q] & 0xffffffff);
            dl -= node_len(c, id);
            if (!blk && nd[id].v.skip >= 0)
                skp_del(c, nd[id].v.skip);
            node_unlink(c, id);
            c->remlog[c->nremlog++] = id;
        }
        int nskp0 = c->nskp;
        int accept = 0, greedy = 0, moved = 0, xj = 0;
        i64 nl = 0, rg = 0, sg = 0;
        double noise = 0; /* rg, sg: gained by re-cutting (judged, kept costs); xj: judged with the kept costs */
        if (blk) {
            /* the cheapest other place for the block as it is; no place: back where it was */
            int a0 = b0 > 0 ? order[b0 - 1] : -1, at = blk_place(c, nd[order[b0]].v.s, nd[order[b1]].v.e, a0, rnd64(c));
            if (at < 0)
                at = a0 >= 0 ? a0 : c->first;
            for (int i = b0; i <= b1; i++) {
                Ev x = nd[order[i]].v;
                at = node_insert_after(c, at, &x);
                dl += node_len(c, at);
            }
            moved = 1;
        } else if (c->N >= 3) {
            /* repair */
            for (i64 q = nrem - 1; q > 0; q--) {
                i64 z = rndn(c, q + 1);
                u32 x = c->pend[q];
                c->pend[q] = c->pend[z];
                c->pend[z] = x;
            }
            greedy = rndu(c) < 0.5;
            noise = rndu(c) < 0.5 ? 0.0 : 0.6;
            i64 np = nrem;
            moved = 1;
            while (np > 0) {
#define BEST_INS(q) (c->G && c->G->has[q] ? c->G->ins[q] : best_insertion(c, c->pend[q], noise))
                if (c->G)
                    gm_round(
                        c, c->pend, np, greedy,
                        noise); /* the big trails of this round, and where possible of the next rounds, in one launch */
                if (opstats || maxwork > 0)
                    for (i64 q = 0, m_ = greedy ? np : 1; q < m_; q++)
                        c->work += (double)NOPEN(c->pend[q]);
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
                if (use_split && TR[t].ohi - TR[t].olo <= splitmax) {
                    sp = best_split(c, t, 400);
                    c->work += (double)NOPEN(t);
                }
                if (sp.ok && (double)sp.delta < bi.val) {
                    Ev e1, e2;
                    seg_events(sp.c1, sp.c2, &e1, &e2);
                    dl += node_len(c, node_insert_after(c, c->nd[sp.i].prev, &e1));
                    dl += node_len(c, node_insert_after(c, sp.jm, &e2));
                } else {
                    Ev x = make_event(bi.opt);
                    dl += node_len(c, node_insert_after(c, bi.after, &x));
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                }
                c->pend[pick] = c->pend[--np];
            }
        }
        if (moved) {
            nl = c->cur + dl;
#if defined(TS_CHECK) && TS_CHECK > 1
            if (nl != ctx_length(c))
                DIE("check: length %lld, by differences %lld at it %lld", ctx_length(c), nl, c->it);
#endif
            i64 d = nl - c->cur;
            if (reox && d > 0 && d <= reod && (blk || reorep)) {
                /* a move that is a little too long: its length after the cluster optimisation of the new order */
                double t1 = wall();
                ro_get(c);
                rg = ci_judge(c);
                xj = rg >= 0;
                c->ro_st[0]++;
                if (rg < 0) {
                    c->ro_st[11]++;
                    rg = 0;
                } else if (rg > 0) {
                    c->ro_st[3]++;
                    c->ro_st[4] += rg;
                    nl -= rg;
                    d -= rg;
                }
                c->ro_sec[0] += wall() - t1;
            } else if (reow > 0 && d > 0 && d <= reod && (blk || reorep)) {
                /* the same with windows: its length after the best re-cutting around its new joins */
                double t1 = wall();
                RO *r = ro_get(c);
                if (blk) {
                    int f = c->inslog[0], l = c->inslog[c->ninslog - 1], a0 = b0 > 0 ? order[b0 - 1] : -1;
                    ro_join(r, a0, a0 >= 0 ? nd[a0].next : c->first);
                    ro_join(r, nd[f].prev, f);
                    ro_join(r, l, nd[l].next);
                } else {
                    for (int q = 0; q < c->ninslog; q++) {
                        int x = c->inslog[q];
                        ro_join(r, nd[x].prev, x);
                        ro_join(r, x, nd[x].next);
                    }
                    for (int q = 0; q < c->nremlog; q++) {
                        int p = nd[c->remlog[q]].prev;
                        while (p >= 0 && !nd[p].alive)
                            p = nd[p].prev;
                        ro_join(r, p, p >= 0 ? nd[p].next : c->first);
                    }
                }
                rg = ro_window(c);
                c->ro_st[0]++;
                if (rg < 0) {
                    c->ro_st[11]++;
                    rg = 0;
                } else if (rg > 0) {
                    c->ro_st[3]++;
                    c->ro_st[4] += rg;
                    nl -= rg;
                    d -= rg;
                }
                c->ro_sec[0] += wall() - t1;
            }
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
            if (rg > 0 && accept) {
                c->ro_st[5]++;
                c->ro_st[6] += d <= 0;
            }
            if (opstats) {
                double wkk = c->work - w_it + 100;
                int nr = c->nremlog, b_ = nr <= 2    ? 0
                                          : nr <= 4  ? 1
                                          : nr <= 8  ? 2
                                          : nr <= 12 ? 3
                                          : nr <= 16 ? 4
                                          : nr <= 24 ? 5
                                          : nr <= 40 ? 6
                                                     : 7;
                c->os_n[op]++;
                c->os_acc[op] += accept;
                c->os_w[op] += wkk;
                c->os_t[op] += wall() - t_it;
                c->st_d[d < -1 ? 0 : d > 4 ? 6 : d + 2]++;
                if (d < 0) {
                    c->os_imp[op]++;
                    c->os_gain[op] -= d;
                }
                if (nl < c->best_len)
                    c->os_best[op]++;
                if (!blk) {
                    int g_ = greedy + 2 * (noise > 0);
                    c->gs_n[g_]++;
                    c->gs_imp[g_] += d < 0;
                    c->rs_n[b_]++;
                    c->rs_imp[b_] += d < 0;
                    c->rs_w[b_] += wkk;
                    if (k < 64) {
                        c->ks_n[k]++;
                        c->ks_imp[k] += d < 0;
                    }
                }
            }
        }
        if (accept) {
            c->cur = nl;
            c->acc++;
            for (int q = 0; q < c->nremlog; q++)
                index_del(c, c->remlog[q]);
            if (blk)
                for (int q = 0; q < nrth; q++) {
                    int *pp = &c->thead[c->rth[2 * q]];
                    while (*pp >= 0) {
                        if (!nd[*pp].alive)
                            *pp = c->tnx[*pp];
                        else
                            pp = &c->tnx[*pp];
                    }
                }
            if (c->relabeled)
                seq_build(c);
            else
                seq_patch(c, N, nn0);
            if (rg > 0 || cosync) {
                int rl = 0;
                if (rg > 0) {
                    if (ro_apply(c) != -rg)
                        DIE("internal error: the re-opening of a judged move does not gain what it promised (it %lld)",
                            c->it);
                    rl = c->ro->reload;
                }
                if (xj) {
                    c->ro->nul = 0;
                    c->ro->ubn = 0;
                    if (ci_sync(c))
                        DIE("internal error: a gain after a judged move (it %lld)", c->it);
                } /* the kept costs are those of the new order already */
                else if (cosync) {
                    sg = ci_move(c, rl);
                    nl -= sg;
                    c->cur = nl;
                }
            }
            if (nl < c->best_len) {
                if (coloc && !cosync) {
                    sg = co_now(c, NULL);
                    nl -= sg;
                } /* a new best gets its pass at once */
                c->best_len = nl;
#pragma omp critical(gbest)
                if (nl < G_len) {
                    char ro_[64] = "";
                    if (rg + sg > 0)
                        snprintf(ro_, sizeof ro_, ", %lld by re-opening", rg + sg);
                    if (blk)
                        printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, block move of %d events%s)\n",
                               wall() - G_t0, G_len, nl, c->tid, c->it, b1 - b0 + 1, ro_);
                    else
                        printf("t=%.0fs: best %lld -> %lld (thread %d, it %lld, removed %lld trails, %lld big%s%s)\n",
                               wall() - G_t0, G_len, nl, c->tid, c->it, nrem, nbig,
                               ops_set ? (const char *[]){", rule 0", ", rule 1", ", rule 2", ", rule 3", ", rule 4",
                                                          ", rule 5", ", rule 6", ", rule 7"}[op]
                                       : "",
                               ro_);
                    fflush(stdout);
                    G_N = ctx_export(c, G_ev);
                    G_len = nl;
                    G_dirty = 1;
                    G_ver++;
                    if (coloc)
                        G_cover = G_ver; /* it is at the optimum of its order already */
                }
            }
        } else {
            if (xj) {
                ci_undo(c);
                c->ro->nr = 0;
            }
            for (int q = c->ninslog - 1; q >= 0; q--) {
                node_unlink(c, c->inslog[q]);
                index_del(c, c->inslog[q]);
            }
            for (int q = c->nremlog - 1; q >= 0; q--)
                node_relink(c, c->remlog[q]);
            if (c->relabeled)
                relabel(c);
            for (int q = 0; q < nrth; q++)
                c->thead[c->rth[2 * q]] = c->rth[2 * q + 1];
            if (!blk) {
                c->nskp = nskp0;
                for (int q = 0; q < c->nremlog; q++)
                    if (nd[c->remlog[q]].v.skip >= 0)
                        skp_add(c, nd[c->remlog[q]].v.skip);
            }
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
                if (adopt && cosync) {
                    int chg;
                    double t1 = wall();
                    i64 g = co_now(c, &chg);
                    c->co_st[0]++;
                    c->co_st[1] += g > 0;
                    c->co_st[2] += g;
                    c->co_sec += wall() - t1;
                    best_note(c, "cluster optimisation in place", chg);
                }
            }
        }
    }
#pragma omp critical(gbest)
    {
        G_it[c->tid] = c->it;
        for (int q = 0; q < 3; q++) {
            G_cost[q] += c->co_st[q];
            G_cist[q] += c->ci_st[q];
        }
        G_cosec += c->co_sec;
        if (drift >= 0 && c->cur <= G_len + drift) {
            /* --drift: where this thread has got to.  With the best sequence unchanged a run would hand back the plan it
               was given; these plans are other orders of (about) the same length: other starting points for whatever
               comes after the search */
            char dp[4200];
            size_t ln = strlen(outplan);
            i64 m = ctx_export(c, c->tmp);
            snprintf(dp, sizeof dp, "%.*s.drift%d.plan", (int)(ln > 5 ? ln - 5 : ln), outplan, c->tid);
            write_plan(c->tmp, m, dp);
            printf("drift: thread %d ends with a sequence of length %lld (best %lld): %s" NL, c->tid, c->cur, G_len,
                   dp);
        }
        for (int q = 0; q < 12; q++)
            G_rost[q] += c->ro_st[q];
        G_rosec[0] += c->ro_sec[0];
        G_rosec[1] += c->ro_sec[1];
        if (opstats) {
            static const char *bn[8] = {"1-2", "3-4", "5-8", "9-12", "13-16", "17-24", "25-40", "41+"};
            printf(
                "thread %d: %lld iterations, %lld block moves not counted, %lld accepted; change of length <=-2: %lld, -1: %lld, 0: %lld, 1: %lld, 2: %lld, 3: %lld, >=4: %lld; work %.1fM" NL,
                c->tid, c->it, c->xit, c->acc, c->st_d[0], c->st_d[1], c->st_d[2], c->st_d[3], c->st_d[4], c->st_d[5],
                c->st_d[6], c->work / 1e6);
            for (int o = 0; o < NOPS; o++)
                if (c->os_n[o])
                    printf(
                        "thread %d rule %d: used %lld, accepted %lld, shorter %lld (sum %lld), new best %lld, %.1fs, work %.1fM" NL,
                        c->tid, o, c->os_n[o], c->os_acc[o], c->os_imp[o], c->os_gain[o], c->os_best[o], c->os_t[o],
                        c->os_w[o] / 1e6);
            printf("thread %d shorter / used by k:", c->tid);
            for (int q = 1; q <= kmax && q < 64; q++)
                printf(" %d:%lld/%lld", q, c->ks_imp[q], c->ks_n[q]);
            printf(NL);
            printf("thread %d shorter / used / work (M) by removed events:", c->tid);
            for (int q = 0; q < 8; q++)
                printf(" %s:%lld/%lld/%.0f", bn[q], c->rs_imp[q], c->rs_n[q], c->rs_w[q] / 1e6);
            printf(NL);
            printf(
                "thread %d shorter / used by repair: one by one %lld/%lld, cheapest first %lld/%lld, one by one + noise %lld/%lld, cheapest first + noise %lld/%lld" NL,
                c->tid, c->gs_imp[0], c->gs_n[0], c->gs_imp[1], c->gs_n[1], c->gs_imp[2], c->gs_n[2], c->gs_imp[3],
                c->gs_n[3]);
            fflush(stdout);
        }
    }
    if (c->G)
        gm_report(c, wall() - ts0);
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
        DIE("usage: trailsearch WORD.txt OUT.txt [--time SEC] [--seed S] [--kmax K] [--T0 TEMP] [--noskip] [--nosplit] [--plan-in FILE] [--ckpt SEC] [--iters N] [--threads T] [--sync SEC] [--focus P] [--bigp P] [--gpu] [--ops W,..] [--blkfree] [--worstn M] [--ties] [--opstats] [--maxwork X] [--co] [--co-skip] [--coit N] [--coinc] [--reow W] [--reod D] [--reorep] [--reox] [--reocap M] [--coloc] [--cosync] [--drift D]");
    const char *plan_in = NULL;
    int co_first = 0;
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
        else if (!strcmp(argv[a], "--gpuprof"))
            gpu_prof = 1;
        else if (!strcmp(argv[a], "--gpucopy"))
            gpu_map = 0;
        else if (!strcmp(argv[a], "--gpuold"))
            gpu_batch = 0;
        else if (!strcmp(argv[a], "--gpudepth") && a + 1 < argc)
            gb_depth = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--gpucheck"))
            gpu_check = 1;
        else if (!strcmp(argv[a], "--gpumin") && a + 1 < argc)
            gpu_min = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--ptx") && a + 1 < argc)
            ptx_path = argv[++a];
        else if (!strcmp(argv[a], "--ops") && a + 1 < argc) {
            char *q = argv[++a];
            ops_set = 1;
            for (int o = 0; o < NOPS; o++) {
                opw[o] = *q ? strtod(q, &q) : 0;
                if (*q == ',')
                    q++;
            }
        } else if (!strcmp(argv[a], "--blkfree"))
            blkfree = 1;
        else if (!strcmp(argv[a], "--worstn") && a + 1 < argc)
            worstn = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--ties"))
            ties = 1;
        else if (!strcmp(argv[a], "--opstats"))
            opstats = 1;
        else if (!strcmp(argv[a], "--maxwork") && a + 1 < argc)
            maxwork = atof(argv[++a]) * 1e6;
        else if (!strcmp(argv[a], "--co"))
            co_first = 1;
        else if (!strcmp(argv[a], "--co-skip"))
            co_first = co_skip = 1;
        else if (!strcmp(argv[a], "--coit") && a + 1 < argc)
            coit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--coinc"))
            coinc = 1;
        else if (!strcmp(argv[a], "--reow") && a + 1 < argc)
            reow = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--reod") && a + 1 < argc)
            reod = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--reocap") && a + 1 < argc)
            reocap = atof(argv[++a]) * 1e6;
        else if (!strcmp(argv[a], "--reorep"))
            reorep = 1;
        else if (!strcmp(argv[a], "--reox"))
            reox = cosync = 1;
        else if (!strcmp(argv[a], "--coloc"))
            coloc = 1;
        else if (!strcmp(argv[a], "--cosync"))
            cosync = 1;
        else if (!strcmp(argv[a], "--drift") && a + 1 < argc)
            drift = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--nosplit"))
            use_split = 0;
        else
            DIE("unknown option %s", argv[a]);
    }
    if (NTHR < 1 || NTHR > 256)
        DIE("1 to 256 threads");
    if (cosync)
        coloc = 1;
    if (coloc) {
        coinc = 1;
        if (!cosync && coit <= 0)
            DIE("--coloc: needs --coit N");
    }
    if (reow < 0 || reod < 0)
        DIE("--reow, --reod: not negative");
    {
        double ws = 0;
        for (int o = 0; o < NOPS; o++) {
            if (opw[o] < 0)
                DIE("--ops: negative weight");
            ws += opw[o];
        }
        if (ws <= 0)
            DIE("--ops: no rule has a weight");
    }
    if (worstn < 1)
        DIE("--worstn: at least 1");
    if (blkfree && opw[6] > 0) {
        double ws = 0;
        for (int o = 0; o < NOPS; o++)
            if (o != 6)
                ws += opw[o];
        if (ws <= 0)
            DIE("--blkfree: block moves alone never count an iteration");
    }
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
    }
    if (co_first)
        co_full(ev, N);
    G_cover = co_first ? 0 : -1; /* without --co the first pass of --coit also takes the sequence as it came */
    /* ---------- destroy / repair search */
    char outplan[4096];
    snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
    memcpy(G_ev, ev, (size_t)N * sizeof(Ev));
    G_N = N;
    G_len = seq_length(ev, N);
    if (use_gpu)
        use_gpu = tlimit > 0 ? gpu_init(argv[0], LT) : 0;
    G_t0 = G_last_ck = G_last_log = wall();
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
    if (coit > 0 || cosync)
        printf("cluster optimisation in the search: %lld passes, %lld with a gain, %lld letters, %.1f thread-seconds\n",
               G_cost[0], G_cost[1], G_cost[2], G_cosec);
    if (reox)
        printf(
            "moves judged after the cluster optimisation of their order: %lld (%lld of them given up: too many openings); %lld with a gain (%lld letters), %lld of them accepted, %lld only because of the gain; %.1f thread-seconds" NL,
            G_rost[0], G_rost[11], G_rost[3], G_rost[4], G_rost[5], G_rost[6], G_rosec[0]);
    else if (reow > 0)
        printf(
            "re-opening around the joins of a move: %lld moves judged (%lld more had too many openings), %.1f events and %.0f openings each; %lld with a gain (%lld letters), %lld of them accepted, %lld only because of the gain; %.1f thread-seconds" NL,
            G_rost[0], G_rost[11], (double)G_rost[1] / (G_rost[0] ? G_rost[0] : 1),
            (double)G_rost[2] / (G_rost[0] ? G_rost[0] : 1), G_rost[3], G_rost[4], G_rost[5], G_rost[6], G_rosec[0]);
    if (cosync)
        printf(
            "kept cluster optimisation after every accepted move: %lld moves, %lld with a gain, %lld letters, %.1f thread-seconds" NL,
            G_rost[8], G_rost[9], G_rost[10], G_rosec[1]);
    if (reow > 0 || coloc)
        printf("events re-opened in place: %lld" NL, G_rost[7]);
    if (cosync)
        printf(
            "kept cluster optimisation: %lld layers and %.1f million openings computed in all (%lld passes over the whole sequence)" NL,
            G_cist[1], G_cist[2] / 1e6, G_cist[0]);
    else if (coit > 0 && coinc)
        printf("kept cluster optimisation: %lld passes, %.1f layers and %.0f openings computed per pass" NL, G_cist[0],
               (double)G_cist[1] / (G_cist[0] ? G_cist[0] : 1), (double)G_cist[2] / (G_cist[0] ? G_cist[0] : 1));
    if (tot > 0 && (co_first || coit > 0 || cosync)) {
        co_full(G_ev, G_N);
        G_len = seq_length(G_ev, G_N);
    }
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
