/* segins_gpu.c - segment insertion as in segins.c, made for long words and for piece sets with many pieces of equal
   kind: what a round needs is kept from round to round, the candidates can be judged on an NVIDIA card, a round
   can take moves that leave the length as it is, and the lists of candidates stay inside a fixed amount of memory.

   Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.  The closed trails are
   those of Jay Pantone's construction (github.com/jaypantone/superperm-upper-43-80).

   What it does.  The move is the one of segins.c: the sequence of pieces is cut at three to six joins and the
   blocks of pieces between the cuts are put together in another order (with three cuts a 3-opt move without
   reversal), and every such move is judged with the best cuts of the whole new sequence.  A round has the same
   five steps (tables, pairs, candidates by a chain search, exact judging, all shorter moves that do not disturb
   each other); read the header of segins.c for them.  Without the options that are new here it wrote the plans
   of segins.c on every plan where I compared the two, at n = 11 and n = 12.  What is new:

   1. Kept from round to round.  The tables are not made again after a round: inside every block that moved, the
      costs are computed from its new neighbour on, layer by layer, until a layer comes out as it was
      (o3_tables_move), and the best cuts of the new sequence are read from the tables.  The exact V of joins that
      are not in the lists, the exact gains of the candidates already judged, and the pair lists (if the pieces
      with new costs hold at most P percent of the cuts, --or3-lupct) are kept as well.  Every kept value carries
      the round it was made in and is used only while nothing it depends on has changed.

   2. Long candidates (--or3-long Z).  If every new join of a move has its exact V and the costs behind each new
      join are back to the old ones inside the block that follows, the move gains exactly its estimate.  That holds
      when the blocks are longer than the longest stretch over which costs change (a zone).  A candidate with Z
      pieces or more between all its cuts therefore gets exact values for its joins and is judged only if its
      estimate is 1 or more.  Z is raised to twice the longest zone seen plus one.  On Pantone's pieces at n = 13
      a round with five cuts had 129,225 candidates without this and 10,335 with it, on nearly the same plan.

   3. Judging on the card (--or3-gpu).  One thread block per candidate does what o3_gain does on the host, layer by
      layer and with the same hash tables, and returns the same gain and the same zones.  --or3-gpu-check computes
      everything on both and compares.  The kernel is segins_kern.cu, compiled once to segins_kern.ptx; the program
      loads the CUDA driver library at run time and links nothing else.  Tables, pairs, the chain search and the
      choice of moves stay on the host.  If the kernel file is missing the program prints "judging on the CPU" and
      goes on at CPU speed: look for that line in the log.

   4. Moves of equal length (--or3-eq E, with --or3-slack 1).  On a piece set with many small trails of the same
      kind thousands of candidates of a round keep the length, and there an estimate of 0 means equal length.
      A round then also takes moves of gain 0: E of the candidates with estimate 0 are drawn at random and those of
      equal length are made, in random order, wherever the place is still free, except a move that would make a
      join again that was cut in the last rounds.  After some fifty such moves the next round has hundreds of
      shorter candidates.  The word never gets longer and the plan file always holds the best length.

   5. Candidates in bounded memory (--or3-hmem MB, on by default).  A round does not keep one list of all moves
      found.  A candidate is 24 bytes, a chain is kept only when it is found from its smallest first cut (so no
      repeat is ever stored), the first cuts are searched a share at a time, and the moves made of two crossing
      pairs are counted once and made again when the round reaches them.  The candidates, their order, the batches
      and the moves taken are the same as with one list (--or3-hcheck makes both and compares).

   6. Cuts at vertices only (--gap3, --gap3-list FILE).  The loader keeps only the plain cuts at steps of weight
      3, so that every pass works in the model in which a plan on n symbols lifts to n + 1 symbols (see
      arrange/README.md).  A plan with other cuts is brought into the model when it is loaded: every such cut
      moves to the nearest vertex after it, and the fixed-order pass runs by itself.  A plan written in this model
      is an ordinary plan, and trailsearch.c rebuilds its word without the option.  Right after a plan has been
      brought into the model it has hundreds of expensive joins: use --or3-x 9 for the first pass, because the
      default lists give tens of millions of moves there.

   Build:  gcc -O2 -mpopcnt -fopenmp -o segins_gpu segins_gpu.c -lm           (Linux: add -ldl)
           bash mkptx.sh                (once, for --or3-gpu: segins_kern.cu to segins_kern.ptx; see segins_kern.cu)
   Use:    n = 11   segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 5 --or3-slack 3 --or3-gpu
           n = 12   segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 3 --or3-slack 0
                               --or3-maxcand 200000 --or3-gpu
                    then, with moves of equal length:
                    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 2 --or3 3 --or3-slack 1
                               --or3-eq 3000 --or3-long 600 --or3-gpu --or3-seed 1 --or3-sec 180
           n = 13   segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 10 --or3 3 --or3-slack 0
                               --or3-v 3 --or3-x 6 --or3-long 1000 --or3-maxcand 200000 --or3-gpu --or3-gpu-check
                               --or3-gpu-checkmax 600 --or3-sec 3600 --or3-stop STOPFILE
                    then, with moves of equal length:
                    segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads 10 --or3 3 --or3-slack 1
                               --or3-v 4 --or3-x 5 --or3-long 1000 --or3-eq 30000 --or3-eq-keep 2000000
                               --or3-seed 1 --or3-gpu --or3-sec 2700
   Without --or3-gpu the same commands run on the CPU.

   Options of the pass.  Those of segins.c with the same meaning: --or3 C, --or3-slack S, --or3-v TH, --or3-x T,
   --or3-maxlay L, --or3-margin G, --or3-rounds R, --or3-sec SEC, --or3-stop FILE, --or3-plateau P, --or3-dip D,
   --or3-dry, --or3-zone Z, --or3-old, and --co, --co-skip, --bs K, --bs-test N.  Different or new:
     --or3-maxcand M    the size of a batch: all candidates are looked at, M at a time, and those next to a move
                        already taken are not judged (in segins.c M cuts the list)
     --or3-long Z       see 2 above.  Use about 600 at n = 12 and 1000 at n = 13; at n = 11 it has little to act on
     --or3-order 0|1    1 (default): long candidates first, then chains, then the moves made of two pairs
     --or3-2pv 0|1      0: the joins of two-pair moves are not valued exactly (as in segins.c)
     --or3-lupct P      the pair lists are brought up to date instead of made again if the pieces with new costs
                        hold at most P percent of the cuts (default 15)
     --or3-full, --or3-nolu, --or3-nojc, --or3-noskip
                        switch off what is kept: tables made again every round; pair lists made again; kept gains
                        not used; tables made again when a piece gives up its skip
     --or3-focus Z      after a round with moves, chains only from cuts near a changed piece; a round over all
                        cuts follows when that finds nothing.  No gain seen; off by default
     --or3-check        tables, pair lists and kept gains are compared with new ones every round and no long
                        candidate is dropped.  For tests: slow, and about 2 GB more at n = 13
     --or3-gpu          judge on the card
     --or3-gpu-check    judge on card and host and compare; the host's results are used
     --or3-gpu-checkmax M
                        with --or3-gpu-check only the first M candidates of the pass and the first 10 M values of
                        joins go to both, after that the card alone.  Use it for the first run on a new size
     --or3-gpu-ptx FILE the kernel file (default: segins_kern.ptx next to the program, then the current directory)
     --or3-gpu-min M    calls with fewer than M candidates are judged on the host (default 1)
     --or3-gpu-ms MS    a launch is given the amount of work that took about MS milliseconds last time (default 100)
     --or3-gpu-budget B a fixed amount of work per launch instead
     --or3-gpu-bt T, --or3-gpu-blocks B
                        GPU threads per block (default 1024) and number of blocks (default: half of what the card
                        holds at once; the work is bound by memory traffic and more blocks are slower)
     --or3-gpu-mem MB   card memory the program may take for its blocks (default 3000)
     --or3-gpu-small S  a layer of at most S cuts is computed by the first warp of a block alone (default 2048)
     --or3-gpu-chunk C  candidates per call (default 262,144)
     --or3-gpu-nomemo, --or3-gpu-nozones
                        switch off the memo of joins on the card; switch off judging ahead for the choice of moves
     --or3-gpu-v        more lines about the card in the log
     --or3-eq E         see 4 above.  E = 3000 at n = 12, 30000 at n = 13
     --or3-eq-max M     at most M moves of equal length per round
     --or3-eq-tabu R    a join cut in the last R rounds is not made again (default 8)
     --or3-eq-stop K    the pass ends after K rounds in a row without a gain (default 20)
     --or3-eq-keep K    the search keeps only about K of the moves with estimate 0 that it finds (a hash sample;
                        0: all).  It bounds memory on plans that have not been through a pass with slack 0.
                        With four cuts and more it switches the bounded lists off; without it, four cuts and
                        more hold every candidate with estimate 0 at 24 bytes each (5 million in one n = 12 run),
                        which I would not try at n = 13
     --or3-seed S       the random numbers of the draw (--or3-eq-seed is the same)
     --or3-hmem MB      room for the candidates of a round (default 768); 0: one list of all moves, as in segins.c
     --or3-hmax M       a round looks at the first M candidates of its list only (0: all).  Hardly tested
     --or3-hcheck       both kinds of lists, compared candidate by candidate (for tests)
     --or3-hrec R       for tests: the store holds R candidates
     --gap3             only cuts at vertices (see 6 above); with --time 0 and no pass: only bring the plan into
                        the model and write it
     --gap3-list FILE   the same, and only the vertices whose h-word is in FILE, one word per line (the list for
                        the lift is written by arrange/mkverts.py)
   and all options of trailsearch.c.  With --time 0 no search runs.

   A round that --or3-sec ends early makes no draw and takes no moves of equal length.

   Memory and time.  Most figures were measured with the three programs this file was merged from; the merged
   program itself has run at n = 11 and n = 12 and, with moves of equal length on the card, at n = 13.
   n = 12 on a set of 7,200 pieces, 2 threads, with the card: 2.0 GB before any candidate and 0.2 to 0.7 GB for
   the candidates, where one list of 36 million moves took 4.8 GB.  A round with moves of equal
   length takes 3 seconds, of which the pair lists are 2 to 3.7 and judging 0.1; on the CPU the same round takes
   16 to 19 seconds.  Judging on the card against 4 CPU threads at n = 12: about 116 times faster.  n = 13 on a
   set of 24,000 pieces, 10 threads, --or3-v 3 --or3-x 6: 18.9 to 19.6 GB at the peak and 6 to 8 GB on the card;
   86 million moves found in 3.5 seconds, 23,070 candidates.  With one list the same round ran out of 24 GB.
   Moves of equal length at n = 13 with this program (23,808 pieces, 10 threads, the card, --or3-v 4 --or3-x 5,
   --or3-eq 30000 --or3-eq-keep 2000000): 18.9 GB, 408 rounds in 2,700 seconds; a round finds 60 million moves
   with estimate 0 and keeps one in 31.
   Not measured: four cuts and more at n = 13.  With --or3-v 3 a round of four cuts there has 26 billion
   candidates, because a join that is not listed counts as 4 in a two-pair move; use wider lists or --or3-hmax.

   Words.  The comments say "cut" for the place where a closed trail is cut open.  The names in the code and the
   text the program prints use two older words for it: "opening" and "option" (struct Opt, the table OP, "gap-2
   openings").  The "gap" g of a cut is the weight of the step that is cut: 3 is the usual cut and costs nothing, 2
   is a cut between two 2-cycles and costs one letter, 1 is a cut inside a 1-cycle and costs two letters.
   An "event" is one piece as it is written into the word: a whole trail from one cut, a segment of a trail, or a
   piece of the input word left as it is.  The "h-word" of a piece end is its first or last h = n - 3 letters; two
   pieces are joined with the largest overlap of these words.  A "skip" is a cut that also drops one of the two
   occurrences of a permutation that the trails contain twice.  "Cluster optimisation" is the fixed-order pass.
   In this file a "stretch" is a block of consecutive pieces between two cuts of a move, a "zone" is the part of a
   block in which the costs differ from the old ones, and "V" of a join is what it costs when the cuts of the two
   pieces may change and everything before and after stays.

   Layout of this file.  It is a copy of the first published version of trailsearch.c (the model, the plan, the
   search, the loader) with these parts added, each marked by a line of equal signs: the fixed-order pass of
   recut.c; the neighbourhood of --bs; segment insertion (tables, pairs, the chain search, exact judging, what is
   kept); moves of equal length; the card; the candidates in bounded memory; the pass itself (o3_full); and,
   in the loader, the cuts at vertices only.
   Removed from the working version: the options --cow and --copre (see recut.c) and a measuring option of the
   card code whose kernel is not part of this directory. */
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

/* ==================== shared base (first published trailsearch.c): model, plan, index, search moves ==================== */
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
    int tid;
    u64 rs[4];
    Node *nd;
    int ncap, nn, first, last;
    i64 N;
    int relabeled;
    HTab H, RELT;
    u64 *bf, bfmask; /* bf: one-hash Bloom filter over the keys of H */
    int *order, *dj, *cand, *rid, *rs_, *re_, *rel, *remlog, *inslog;
    int nremlog, ninslog;
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
/* Loads a sequence of N events into the thread: nodes, order labels, index, Bloom filter and the kept arrays
   (seq_build).  Buffers grow when needed.  ev may be the thread's own c->tmp. */
static void ctx_load(Ctx *c, const Ev *ev, i64 N) {
    int need = (int)(4 * N + 65536), self = ev == c->tmp;
    if (need > c->ncap) {
        c->ncap = need;
        c->nd = realloc(c->nd, (size_t)need * sizeof(Node));
        int **arr[] = {&c->order, &c->dj, &c->cand, &c->rid, &c->rs_, &c->re_, &c->rel, &c->remlog, &c->inslog};
        for (int k = 0; k < 9; k++)
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

/* ---------- best insertion of trail t: insert after node `after` */
typedef struct {
    double val;
    i64 delta;
    int after;
    i64 opt;
} Ins;
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
                    double v = (double)d + (noise > 0 ? noise * rndu(c) : 0.0);
                    if (v < best.val) {
                        best.val = v;
                        best.delta = d;
                        best.after = a;
                        best.opt = o;
                    }
                }
            }
        }
    }
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

/* ==================== from recut.c: the fixed-order pass (co_run, co_full) ==================== */
/* ---------- cluster optimisation: for a fixed order of the events, the best cuts of all trails at once.
   Shortest path through layers, one per event: cost[p] = D(p) + min over the cuts o of the previous event of
   cost[o] + dist(E(o), S(p)).  The minimum is not taken over pairs: for k = h..1 a table holds the cheapest o for
   every suffix of length k of E(o) (a hash table, for k <= 3 an array) and prefix_k(S(p)) is looked up; only o with cost[o] - min < k can beat the
   join without overlap (h + min), so few o enter the tables of small k.  Costs are kept relative to the minimum of
   their layer (one byte per option) and the cuts are recovered backwards without back-pointers.
   One option only: segments, pieces of chained trails and of the open path, events outside lo..hi.  An unchanged
   piece that is a whole closed trail is the cut `start 0` of that trail and is free like any other.
   Skip cuts: an event may only take the skip it already uses (co_skip = 0); with co_skip = 1 every skip is
   allowed and the pass is repeated with bans while two events skip the same window. */
static double wall(void);
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
static int co_skip = 0;
static i64 coit = 0;
/* --coit N: every N iterations of a thread the whole current sequence (one pass at a time, the table is shared) */
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
    for (i64 o = T->ohi - 1; o >= T->olo; o--)
        if (!OP[o].start && !OP[o].g1)
            return (x->l == T->R + h + oD(o) && x->s == oS_t(T, o) && x->e == oE_t(T, o)) ? o : -1;
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
            oldc += dist(ev[i - 1].e, x->s);
        if (o0 < 0) { /* one option */
            i64 cst = 0;
            if (i > a && !pfree)
                cst = pmin + dist(pe, x->s);
            else if (i > a) {
                const unsigned char *prel = q->rel + poff;
                int best = h;
                for (i64 j = 0; j < pm; j++)
                    if (prel[j] < best) {
                        int v = prel[j] + dist(q->Ep[j], x->s);
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
        i64 m = T->ohi - T->olo;
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
            i64 o = T->olo + j;
            if (OP[o].g1 && !co_skip_ok(q, x, i, T, o, anyskip)) {
                rel[j] = 255;
                continue;
            }
            S[j] = oS_t(T, o);
            E[j] = oE_t(T, o);
            rel[j] = 0;
            mv[j] = i == a ? 0 : !pfree ? dist(pe, S[j]) : h;
        }
        if (i > a && pfree) {
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
        int mn = 1 << 20;
        for (i64 j = 0; j < m; j++)
            if (rel[j] != 255) {
                mv[j] += oD(T->olo + j);
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
            if (i < b && q->lmin[li] + dist(x->e, ns) != want)
                DIE("internal error: cluster optimisation (event %lld)", i);
            ns = x->s;
            want = q->lmin[li];
            continue;
        }
        const Trail *T = &TR[x->t];
        const unsigned char *rel = q->rel + q->off[li];
        i64 m = T->ohi - T->olo, pick = -1;
        i64 tgt = i < b ? want : q->lmin[li];
#define COV(j) (q->lmin[li] + rel[j] + (i < b ? dist(oE_t(T, T->olo + (j)), ns) : 0))
        if (rel[o0 - T->olo] != 255 && COV(o0 - T->olo) == tgt)
            pick = o0 - T->olo;
        for (int pass = 0; pass < 2 && pick < 0; pass++) /* plain cuts first */
            for (i64 j = 0; j < m; j++)
                if (rel[j] != 255 && (pass || !OP[T->olo + j].g1) && COV(j) == tgt) {
                    pick = j;
                    break;
                }
#undef COV
        if (pick < 0)
            DIE("internal error: cluster optimisation (event %lld)", i);
        i64 o = T->olo + pick;
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
/* passes of --coit in a thread: passes, passes with a gain, letters; seconds */
typedef struct {
    i64 st[3];
    double sec;
} CLog;
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

/* ==================== from segins.c: reordering inside windows of K pieces (--bs) ==================== */
/* ---------- order and cuts together.  The neighbourhood of Balas and Simonetti: all sequences in which event
   i stays before event j whenever i + K <= j in the current order (K = 1: the order as it is, i.e. co_run),
   searched exactly together with the cuts.  Layer p holds the states after p events: the set V of the events
   written so far (0 .. u-1 and a subset `mask` of u+1 .. u+K-1, where u is the first event not yet written), the
   last event j (j in V, j > max V - K) and, as in co_run, the cost of every cut of j: one byte relative to
   the minimum mu of the state.  A layer has 2^(K-1) sets and (K+1) 2^(K-2) states.  All states of one set are
   extended together: the cuts of their last events are one pool of (end word, cost) for the overlap tables of
   co_run, and every event c that may come next (u, or one of u+1 .. u+K-1 not in mask) looks its cuts up
   once.  So a state costs about as much as a layer of co_run, and the pass (K+1) 2^(K-2) times co_run.
   Two layers are kept and one in every `blk`; only if the result is shorter the layers are computed again, block
   by block from the end, and the sequence is read off backwards (no back-pointers).
   Slot of a state in its layer: mask * 2K + (j - u + K). */
/* minimum, table (offset in the pool of the layer), its size (0: no such state), mask of the set it came from */
typedef struct {
    i64 mu, off;
    int m, pm;
} BSt;
typedef struct {
    BSt *st;
    unsigned char *pool;
    i64 used, cap;
} BLay;
/* the cuts an event may take (o = -1: the event as it is) */
typedef struct {
    i64 id, cap;
    int m;
    u64 *S, *E;
    signed char *D;
    i64 *o;
} BEv;
typedef struct {
    CSlot *t;
    u64 cap;
    u32 gen;
    u64 *UE;
    i64 ucap;
    int *mv;
    i64 mcap;
    unsigned char d[16 + 256 + 4096];
} BScr;
typedef struct {
    int K, nm, ns, anyskip, nthr, count;
    const Ev *ev;
    i64 N;
    BEv *ec;
    int ecn;
    BScr *scr;
    CO *q;                   /* q: only the bans of co_skip */
    i64 nst, nbytes, maxlay; /* statistics of the last pass: states, bytes of their tables, largest layer */
} BS;
static int bsK = 0, bs_ntest = 0;
/* The cuts an event may take, cached: start words, end words, costs and cut numbers (one entry if the event
   cannot be cut again). */
static BEv *bs_ev(BS *b, i64 i) {
    BEv *e = &b->ec[i % b->ecn];
    if (e->id == i)
        return e;
    const Ev *x = &b->ev[i];
    const Trail *T = &TR[x->t];
    i64 o0 = co_cur(x), m = o0 < 0 ? 1 : T->ohi - T->olo;
    if (m > e->cap) {
        e->cap = m + m / 2 + 16;
        e->S = realloc(e->S, e->cap * 8);
        e->E = realloc(e->E, e->cap * 8);
        e->o = realloc(e->o, e->cap * 8);
        e->D = realloc(e->D, e->cap);
        if (!e->S || !e->E || !e->o || !e->D)
            DIE("out of memory");
    }
    if (o0 < 0) {
        e->S[0] = x->s;
        e->E[0] = x->e;
        e->D[0] = 0;
        e->o[0] = -1;
    } else {
        m = 0;
        for (i64 o = T->olo; o < T->ohi; o++) {
            if (OP[o].g1 && !co_skip_ok(b->q, x, i, T, o, b->anyskip))
                continue;
            e->S[m] = oS_t(T, o);
            e->E[m] = oE_t(T, o);
            e->D[m] = (signed char)oD(o);
            e->o[m++] = o;
        }
    }
    e->m = (int)m;
    e->id = i;
    return e;
}
/* Is (p events written, set mask) a state of the neighbourhood?  *u = the first event not yet written. */
static inline int bs_valid(const BS *b, i64 p, int mask, i64 *u) {
    *u = p - __builtin_popcount(mask);
    if (*u < 0)
        return 0;
    return mask ? *u + 32 - __builtin_clz(mask) <= b->N - 1 : *u <= b->N;
}
/* event c = u (z = -1) or c = u + 1 + z comes next: the slot of the new state in the next layer, or -1 */
static inline int bs_succ(const BS *b, i64 u, int mask, int z, i64 *c) {
    int K = b->K;
    if (z < 0) {
        int t = __builtin_ctz(~mask);
        *c = u;
        return (mask >> (t + 1)) * 2 * K + K - 1 - t;
    }
    if (((mask >> z) & 1) || u + 1 + z > b->N - 1)
        return -1;
    *c = u + 1 + z;
    return (mask | (1 << z)) * 2 * K + K + 1 + z;
}
/* As co_put, in the scratch table of a thread. */
static inline void bs_put(BScr *w, u64 mask, u64 key, u32 val) {
    u64 i = hmix(key) & mask;
    while (w->t[i].gen == w->gen) {
        if (w->t[i].key == key) {
            if (val < w->t[i].val)
                w->t[i].val = val;
            return;
        }
        i = (i + 1) & mask;
    }
    w->t[i].key = key;
    w->t[i].gen = w->gen;
    w->t[i].val = val;
}
/* As co_get, in the scratch table of a thread. */
static inline int bs_get(const BScr *w, u64 mask, u64 key) {
    u64 i = hmix(key) & mask;
    while (w->t[i].gen == w->gen) {
        if (w->t[i].key == key)
            return (int)w->t[i].val;
        i = (i + 1) & mask;
    }
    return -1;
}
/* The join cost lives in two functions that must agree: bs_dist, the cost of writing an cut that starts with s
   after one that ends with e, and bs_join, the same for many at once: mv[j] = min(h, min over a pool of cuts of
   their cost v + bs_dist(E, S[j])) for every cut j of the events ce[0 .. nc-1].  The pool is given by its end
   words UE sorted by cost (cost v: UE[bnd[v]] .. UE[bnd[v+1]-1], only v < h).  As in co_run: for k = h .. 4 a hash
   table of the cheapest pool entry for every suffix of length k, for k <= 3 arrays.
   rev: the pool is written after the events instead: UE holds start words and mv[j] = min(h, min v + bs_dist(E[j], S)). */
static inline int bs_dist(u64 e, u64 s) {
    return dist(e, s);
}
/* One layer step for several events at once: mv[j] = min over the pooled cuts of (their cost + join to cut j),
   through tables by the last k letters for k = h .. 1 (see the comment above bs_dist). */
static void bs_join(BScr *w, const i64 *bnd, BEv **ce, int nc, int *mv, int rev) {
    for (int k = h; k >= 4 && bnd[k]; k--) {
        u64 need = 16;
        while (need < 2 * (u64)bnd[k])
            need <<= 1;
        if (need > w->cap) {
            free(w->t);
            w->t = calloc(need, sizeof(CSlot));
            w->cap = need;
            w->gen = 0;
            if (!w->t)
                DIE("out of memory");
        }
        u64 hm = need - 1;
        int sh = 4 * (h - k), *m2 = mv;
        w->gen++;
        for (int v = 0; v < k; v++)
            for (i64 e = bnd[v]; e < bnd[v + 1]; e++)
                bs_put(w, hm, rev ? w->UE[e] >> sh : w->UE[e] & HMASK[k], (u32)v);
        for (int q = 0; q < nc; q++) {
            const u64 *S = rev ? ce[q]->E : ce[q]->S;
            int m = ce[q]->m;
            for (int j = 0; j < m; j++) {
                if (m2[j] <= h - k)
                    continue;
                int v = bs_get(w, hm, rev ? S[j] & HMASK[k] : S[j] >> sh);
                if (v >= 0 && v + h - k < m2[j])
                    m2[j] = v + h - k;
            }
            m2 += m;
        }
    }
    if (!bnd[h < 3 ? h : 3])
        return;
    unsigned char *d1 = w->d, *d2 = d1 + 16, *d3 = d2 + 256;
    int *m2 = mv; /* k = 3, 2, 1: tables indexed by the word */
    memset(w->d, 255, sizeof w->d);
    int s3 = 4 * (h - 3), s2 = 4 * (h - 2), s1 = 4 * (h - 1);
    for (int v = 0; v < 3 && v < h; v++)
        for (i64 e = bnd[v]; e < bnd[v + 1]; e++) {
            u64 E = w->UE[e], k3 = rev ? E >> s3 : E & 4095, k2 = rev ? E >> s2 : E & 255, k1 = rev ? E >> s1 : E & 15;
            if (v < d3[k3])
                d3[k3] = (unsigned char)v;
            if (v < 2 && v < d2[k2])
                d2[k2] = (unsigned char)v;
            if (!v)
                d1[k1] = 0;
        }
    for (int q = 0; q < nc; q++) {
        const u64 *S = rev ? ce[q]->E : ce[q]->S;
        int m = ce[q]->m;
        for (int j = 0; j < m; j++) {
            if (m2[j] <= h - 3)
                continue;
            int v = d3[rev ? S[j] & 4095 : S[j] >> s3];
            if (v + h - 3 < m2[j])
                m2[j] = v + h - 3;
            if (m2[j] <= h - 2)
                continue;
            v = d2[rev ? S[j] & 255 : S[j] >> s2];
            if (v + h - 2 < m2[j])
                m2[j] = v + h - 2;
            if (m2[j] == h && !d1[rev ? S[j] & 15 : S[j] >> s1])
                m2[j] = h - 1;
        }
        m2 += m;
    }
}
/* the states of the set (u, mask) of layer A (after p events) -> their successors in layer Bn (tables already placed) */
static void bs_group(BS *b, BScr *w, const BLay *A, BLay *Bn, i64 p, int mask, i64 u) {
    int K = b->K;
    const BSt *as = A->st + (i64)mask * 2 * K;
    i64 muV = 0, bnd[18] = {0}, pos[17];
    if (p) { /* the pool: end words of all cuts that cost less than h more than the cheapest, sorted by that cost */
        muV = 1LL << 60;
        for (int cd = 0; cd < 2 * K; cd++)
            if (as[cd].m && as[cd].mu < muV)
                muV = as[cd].mu;
        for (int pass = 0; pass < 2; pass++) {
            for (int cd = 0; cd < 2 * K; cd++) {
                if (!as[cd].m || as[cd].mu - muV >= h)
                    continue;
                int base = (int)(as[cd].mu - muV), lim = h - base, m = as[cd].m;
                const unsigned char *rel = A->pool + as[cd].off;
                if (!pass) {
                    for (int j = 0; j < m; j++)
                        if (rel[j] < lim)
                            bnd[base + rel[j] + 1]++;
                } else {
                    const u64 *E = bs_ev(b, u - K + cd)->E;
                    for (int j = 0; j < m; j++)
                        if (rel[j] < lim)
                            w->UE[pos[base + rel[j]]++] = E[j];
                }
            }
            if (pass)
                break;
            for (int v = 0; v < h; v++)
                bnd[v + 1] += bnd[v];
            if (bnd[h] > w->ucap) {
                w->ucap = bnd[h] + bnd[h] / 2 + 64;
                free(w->UE);
                w->UE = malloc(w->ucap * 8);
                if (!w->UE)
                    DIE("out of memory");
            }
            for (int v = 0; v < h; v++)
                pos[v] = bnd[v];
        }
    }
    int nc = 0, ts[32];
    BEv *ce[32];
    i64 tot = 0, c;
    for (int z = -1; z < K - 1; z++) {
        int s = bs_succ(b, u, mask, z, &c);
        if (s < 0)
            continue;
        ts[nc] = s;
        ce[nc] = bs_ev(b, c);
        tot += ce[nc++]->m;
    }
    if (tot > w->mcap) {
        w->mcap = tot + tot / 2 + 64;
        free(w->mv);
        w->mv = malloc(w->mcap * sizeof(int));
        if (!w->mv)
            DIE("out of memory");
    }
    int *mv = w->mv;
    for (i64 j = 0; j < tot; j++)
        mv[j] = p ? h : 0;
    if (p)
        bs_join(w, bnd, ce, nc, mv, 0);
    for (int q = 0; q < nc; q++) {
        BSt *s = &Bn->st[ts[q]];
        unsigned char *rel = Bn->pool + s->off;
        const signed char *D = ce[q]->D;
        int m = ce[q]->m, mn = 1 << 20;
        for (int j = 0; j < m; j++) {
            mv[j] += D[j];
            if (mv[j] < mn)
                mn = mv[j];
        }
        for (int j = 0; j < m; j++)
            rel[j] = (unsigned char)(mv[j] - mn);
        s->mu = muV + mn;
        mv += m;
    }
}
/* layer p -> layer p + 1 */
static void bs_layer(BS *b, const BLay *A, BLay *Bn, i64 p) {
    int K = b->K;
    i64 N = b->N, used = 0, u, c, nst = 0;
    for (i64 i = p - 2 * K + 1 > 0 ? p - 2 * K + 1 : 0; i <= p + K - 1 && i < N; i++)
        bs_ev(b, i);
    if (!Bn->st) {
        Bn->st = malloc((size_t)b->ns * sizeof(BSt));
        if (!Bn->st)
            DIE("out of memory");
    }
    memset(Bn->st, 0, (size_t)b->ns * sizeof(BSt));
    for (int mask = 0; mask < b->nm; mask++) {
        if (!bs_valid(b, p, mask, &u) || u >= N)
            continue;
        for (int z = -1; z < K - 1; z++) {
            int s = bs_succ(b, u, mask, z, &c);
            if (s < 0)
                continue;
            BSt *x = &Bn->st[s];
            x->m = bs_ev(b, c)->m;
            x->off = used;
            x->pm = mask;
            used += x->m;
            nst++;
        }
    }
    if (used > Bn->cap) {
        Bn->cap = used + used / 4 + 64;
        free(Bn->pool);
        Bn->pool = malloc((size_t)Bn->cap);
        if (!Bn->pool)
            DIE("out of memory");
    }
    Bn->used = used;
#pragma omp parallel for schedule(dynamic, 1) num_threads(b->nthr) if (b->nthr > 1 && b->nm > 1)
    for (int mask = 0; mask < b->nm; mask++) {
        i64 u2;
        if (!bs_valid(b, p, mask, &u2) || u2 >= N)
            continue;
        bs_group(b, &b->scr[omp_get_thread_num()], A, Bn, p, mask, u2);
    }
    if (b->count) {
        b->nst += nst;
        b->nbytes += used;
        if (used > b->maxlay)
            b->maxlay = used;
    }
}
/* the best sequence of the neighbourhood: perm[k] = the event (its place in ev) that comes k-th, opt[i] = the
   cut of event i (-1: as it is).  Returns the gain in letters; 0: perm and opt describe ev as it is. */
static i64 bs_run(BS *b, const Ev *ev, i64 N, i64 *perm, i64 *opt) {
    int K = b->K, SL = 2 * K;
    b->ev = ev;
    b->N = N;
    b->nst = b->nbytes = b->maxlay = 0;
    for (int k = 0; k < b->ecn; k++)
        b->ec[k].id = -1;
    i64 blk = 16;
    while (blk * blk < N)
        blk++;
    i64 nsnap = (N - 1) / blk + 1, old = 0;
    BLay *snap = calloc((size_t)nsnap, sizeof(BLay)), L2[2];
    memset(L2, 0, sizeof L2);
    L2[0].st = calloc((size_t)b->ns, sizeof(BSt));
    if (!snap || !L2[0].st)
        DIE("out of memory");
    for (i64 i = 0; i < N; i++) {
        opt[i] = co_cur(&ev[i]);
        perm[i] = i;
        if (opt[i] >= 0)
            old += oD(opt[i]);
        if (i)
            old += bs_dist(ev[i - 1].e, ev[i].s);
    }
    b->count = 1;
    for (i64 p = 0; p < N; p++) {
        if (p % blk == 0) {
            BLay *s = &snap[p / blk], *x = &L2[p & 1];
            s->st = malloc((size_t)b->ns * sizeof(BSt));
            s->pool = malloc((size_t)x->used + 1);
            if (!s->st || !s->pool)
                DIE("out of memory");
            memcpy(s->st, x->st, (size_t)b->ns * sizeof(BSt));
            if (x->used)
                memcpy(s->pool, x->pool, (size_t)x->used);
            s->used = s->cap = x->used;
        }
        bs_layer(b, &L2[p & 1], &L2[(p + 1) & 1], p);
    }
    b->count = 0;
    const BSt *fs = L2[N & 1].st;
    i64 best = 1LL << 60;
    int slot = -1;
    for (int cd = K - 1; cd >= 0; cd--)
        if (fs[cd].m && fs[cd].mu < best) {
            best = fs[cd].mu;
            slot = cd;
        }
    if (best > old)
        DIE("internal error: order optimisation (%lld > %lld)", best, old);
    if (best < old) {
        BLay *lay = calloc((size_t)blk + 1, sizeof(BLay));
        int oi = -1;
        if (!lay)
            DIE("out of memory");
        for (i64 q = nsnap - 1; q >= 0; q--) {
            i64 a = q * blk, e = a + blk < N ? a + blk : N;
            BLay keep = lay[0];
            lay[0] = snap[q];
            for (i64 p = a; p < e; p++)
                bs_layer(b, &lay[p - a], &lay[p - a + 1], p);
            for (i64 p = e; p > a;
                 p--) { /* state `slot` of layer p; from layer N - 1 down also the cut oi of its last event */
                const BLay *X = &lay[p - a], *Y = &lay[p - a - 1];
                const BSt *s = &X->st[slot];
                i64 c = p - __builtin_popcount(slot / SL) - K + slot % SL;
                BEv *ce = bs_ev(b, c);
                const unsigned char *rel = X->pool + s->off;
                if (p == N) {
                    for (int t = 0; t < ce->m; t++)
                        if (!rel[t] && (oi < 0 || ce->o[t] == opt[c]))
                            oi = t;
                }
                if (!s->m || oi < 0 || oi >= ce->m)
                    DIE("internal error: order optimisation (layer %lld)", p);
                i64 need = s->mu + rel[oi] - ce->D[oi], cur_c = opt[c];
                u64 Sc = ce->S[oi];
                perm[p - 1] = c;
                opt[c] = ce->o[oi];
                (void)cur_c;
                if (p == 1) {
                    if (need)
                        DIE("internal error: order optimisation (first event)");
                    break;
                }
                int pm = s->pm, fcd = -1, ft = -1;
                i64 u = p - 1 - __builtin_popcount(pm);
                for (int pass = 0; pass < 2 && fcd < 0;
                     pass++) /* the event before c in ev first, and for every event its present cut first */
                    for (int cd = SL - 1; cd >= 0 && fcd < 0; cd--) {
                        const BSt *y = &Y->st[pm * SL + cd];
                        i64 j = u - K + cd;
                        if (!y->m || (j == c - 1) == pass)
                            continue;
                        BEv *je = bs_ev(b, j);
                        const unsigned char *yr = Y->pool + y->off;
                        i64 oj = co_cur(&ev[j]);
                        for (int t = 0; t < je->m; t++)
                            if (y->mu + yr[t] + bs_dist(je->E[t], Sc) == need) {
                                fcd = cd;
                                if (ft < 0 || je->o[t] == oj)
                                    ft = t;
                                if (je->o[t] == oj)
                                    break;
                            }
                    }
                if (fcd < 0)
                    DIE("internal error: order optimisation (no way into layer %lld)", p);
                slot = pm * SL + fcd;
                oi = ft;
            }
            lay[0] = keep;
        }
        for (i64 k = 0; k <= blk; k++) {
            free(lay[k].st);
            free(lay[k].pool);
        }
        free(lay);
    }
    for (i64 k = 0; k < nsnap; k++) {
        free(snap[k].st);
        free(snap[k].pool);
    }
    free(snap);
    free(L2[0].st);
    free(L2[0].pool);
    free(L2[1].st);
    free(L2[1].pool);
    return old - best;
}
/* Sets up the neighbourhood for window size K (1 to 12): number of sets and states per layer, caches, one
   scratch table per thread. */
static void bs_init(BS *b, CO *q, int K) {
    memset(b, 0, sizeof *b);
    memset(q, 0, sizeof *q);
    if (K < 1 || K > 12)
        DIE("--bs K: 1 to 12");
    b->K = K;
    b->nm = 1 << (K - 1);
    b->ns = b->nm * 2 * K;
    b->ecn = 4 * K + 4;
    b->nthr = NTHR;
    b->q = q;
    b->anyskip = co_skip;
    b->ec = calloc((size_t)b->ecn, sizeof(BEv));
    b->scr = calloc((size_t)NTHR, sizeof(BScr));
    if (!b->ec || !b->scr)
        DIE("out of memory");
}
/* Frees what bs_init and the passes allocated. */
static void bs_free(BS *b) {
    for (int k = 0; k < b->ecn; k++) {
        free(b->ec[k].S);
        free(b->ec[k].E);
        free(b->ec[k].D);
        free(b->ec[k].o);
    }
    for (int k = 0; k < b->nthr; k++) {
        free(b->scr[k].t);
        free(b->scr[k].UE);
        free(b->scr[k].mv);
    }
    free(b->ec);
    free(b->scr);
    free(b->q->ban);
}
/* one pass on ev (with co_skip: repeated with bans while two events skip the same window); returns the gain */
static i64 bs_once(BS *b, Ev *ev, i64 N, Ev *orig, Ev *evo, i64 *perm, i64 *opt, i64 *moved, i64 *chg, int *passes) {
    memcpy(orig, ev, (size_t)N * sizeof(Ev));
    b->q->nban = 0;
    *passes = 0;
    i64 l0 = seq_length(ev, N), gain;
    for (;;) {
        gain = bs_run(b, orig, N, perm, opt);
        (*passes)++;
        for (i64 i = 0; i < N; i++) {
            evo[i] = orig[i];
            if (opt[i] >= 0 && opt[i] != co_cur(&orig[i]))
                evo[i] = make_event(opt[i]);
        }
        if (!b->anyskip || !co_clash(b->q, orig, evo, N))
            break;
    }
    *moved = *chg = 0;
    for (i64 k = 0; k < N; k++) {
        i64 i = perm[k];
        ev[k] = evo[i];
        *moved += i != k;
        *chg += evo[i].kind != orig[i].kind || evo[i].a != orig[i].a;
    }
    i64 l1 = seq_length(ev, N);
    if (l0 - l1 != gain)
        DIE("internal error: order optimisation promised %lld, got %lld", gain, l0 - l1);
    return gain;
}
/* the whole sequence, repeated while it gets shorter (a new order has a new neighbourhood) */
static i64 bs_full(Ev *ev, i64 N, int K) {
    BS b;
    CO q;
    bs_init(&b, &q, K);
    Ev *orig = malloc((size_t)N * sizeof(Ev)), *evo = malloc((size_t)N * sizeof(Ev));
    i64 *perm = malloc((size_t)N * 8), *opt = malloc((size_t)N * 8), total = 0;
    if (!orig || !evo || !perm || !opt)
        DIE("out of memory");
    for (;;) {
        double t0 = wall();
        i64 l0 = seq_length(ev, N), moved, chg;
        int passes;
        i64 gain = bs_once(&b, ev, N, orig, evo, perm, opt, &moved, &chg, &passes);
        printf(
            "order optimisation (K=%d): %lld -> %lld (%lld events moved, %lld openings changed; %lld states, tables %lld bytes, largest layer %lld; %d pass%s, %d bans, %.1fs)\n",
            K, l0, l0 - gain, moved, chg, b.nst, b.nbytes, b.maxlay, passes, passes > 1 ? "es" : "", q.nban,
            wall() - t0);
        fflush(stdout);
        total += gain;
        if (gain <= 0)
            break;
    }
    free(orig);
    free(evo);
    free(perm);
    free(opt);
    bs_free(&b);
    return total;
}
/* check against plain enumeration on random windows of at most 8 events: every sequence of the neighbourhood, each with co_run */
static void bs_enum(Ev *sub, int w, int K, int *pm, int d, int used, CO *q, Ev *tmp, i64 *best, i64 *cnt) {
    if (d == w) {
        for (int k = 0; k < w; k++)
            tmp[k] = sub[pm[k]];
        co_run(q, tmp, w, 0, w - 1, 0, NULL);
        i64 l = seq_length(tmp, w);
        if (l < *best)
            *best = l;
        (*cnt)++;
        return;
    }
    int u = 0;
    while ((used >> u) & 1)
        u++;
    for (int c = u; c < w && c < u + K; c++)
        if (!((used >> c) & 1)) {
            pm[d] = c;
            bs_enum(sub, w, K, pm, d + 1, used | (1 << c), q, tmp, best, cnt);
        }
}
/* Self-test of --bs: on random windows of at most 8 events the result of bs_run is compared with plain
   enumeration (bs_enum).  Prints the number of differences. */
static void bs_test(const Ev *ev, i64 N, int K, int trials) {
    BS b;
    CO q, q2;
    bs_init(&b, &q, K);
    b.anyskip = 0;
    memset(&q2, 0, sizeof q2);
    Ev sub[8], s1[8], orig[8], evo[8], tmp[8];
    i64 perm[8], opt[8], bad = 0, gains = 0, nmoved = 0;
    u64 r = seed * 0x9E3779B97F4A7C15ULL + 12345;
    for (int t = 0; t < trials; t++) {
        r = r * 6364136223846793005ULL + 1442695040888963407ULL;
        int w = 2 + (int)((r >> 33) % 7);
        if (w > N)
            w = (int)N;
        r = r * 6364136223846793005ULL + 1442695040888963407ULL;
        i64 a = (i64)((r >> 33) % (u64)(N - w + 1));
        if (K > 5 && w > 7)
            w = 7;
        memcpy(sub, ev + a, (size_t)w * sizeof(Ev));
        if (t & 1)
            for (int k = w - 1; k > 0; k--) {
                r = r * 6364136223846793005ULL + 1442695040888963407ULL;
                int z = (int)((r >> 33) % (u64)(k + 1));
                Ev x = sub[k];
                sub[k] = sub[z];
                sub[z] = x;
            } /* every other window in a random order */
        memcpy(s1, sub, (size_t)w * sizeof(Ev));
        i64 l0 = seq_length(sub, w), moved, chg, best = 1LL << 60, cnt = 0;
        int passes, pm[8];
        i64 gain = bs_once(&b, s1, w, orig, evo, perm, opt, &moved, &chg, &passes);
        bs_enum(sub, w, K, pm, 0, 0, &q2, tmp, &best, &cnt);
        if (l0 - gain != best) {
            bad++;
            printf(
                "bs-test: MISMATCH at %lld (%d events): order optimisation %lld, enumeration %lld (%lld sequences)\n",
                a, w, l0 - gain, best, cnt);
        }
        gains += gain > 0;
        nmoved += moved > 0;
    }
    printf("bs-test K=%d: %d windows, %lld with a gain, %lld with a new order, %lld mismatches\n", K, trials, gains,
           nmoved, bad);
    fflush(stdout);
    bs_free(&b);
}

/* ==================== segment insertion (--or3): tables, pairs, candidates, exact judging, what is kept between rounds ==================== */
/* ---------- segment insertion with re-cutting.  The sequence is cut at k joins (3 <= k <= C of --or3 C) and its
   stretches are put together in another order, none of them reversed.  k = 3: A B C D becomes A C B D, two
   neighbouring stretches of any length change places (a block that moves to another place is the case of a short
   B or C); k = 4 adds A D C B E; k = 5 and 6 add the orders whose new joins form one cycle (see below).
   What a join is worth when the cuts may change: fw is the cost of every cut of every event with the
   best of everything before it, bw with the best of everything after it, both relative to their minimum (fmin,
   gmin), and V(x, y) = min over the cuts of fw_x + join + bw_y is what the join x -> y costs if all before x
   and all after y stay as they are.  The length is fmin[p] + V(p, p+1) + gmin[p+1] + a constant for every p.
   V is listed for every pair with V <= th (only cuts with fw <= th and bw <= th take part), and for the
   pairs between the two sides of expensive joins (V >= T of --or3-x T; at most O3XMAX joins) up to h - 1.
   Candidates: moves with   V of the joins cut - V of the new joins + slack > 0,   found as in Lin and
   Kernighan's method: cut a join, give its left event a new successor y, cut the join before y, give the event
   before y a new successor, ..., and close by joining the last such event to the right event of the first cut;
   after every new join the sum so far must be above -slack (every move has a first cut for which it is).
   The new joins of the chain are listed pairs, each list sorted by V, so a step looks only at the pairs it can
   use.  The closing join may be any pair: if it is not listed its V is computed from the two tables.  A move
   with one join that is not listed is therefore found only from the cut after that join; --or3-dip D lets the
   sum inside the chain go down to -slack - D, so that such a move is found although its cheap cuts come first.
   (The first version, kept as --or3-old, also took pairs that are not listed inside the chain, each as worth
   th + 1, by loops over all events: cubic in the number of expensive joins.)
   Every candidate is judged exactly, that is with the best cuts of the whole new sequence (o3_gain): from
   each new join on, the dynamic programme of co_run is run through the stretch that follows until the costs of
   an event's cuts are what they were before.  That takes a few layers per candidate, and the candidates do
   not depend on each other. */
#define O3KM 6 /* most cuts of a move */
/* for every event: (event, V) */
typedef struct {
    i64 *off;
    int *to;
    unsigned char *c;
} JG;
typedef struct {
    i64 *off, *fmin, *gmin;
    unsigned char *fw, *bw;
} POT;
/* a move: the joins after the events c[0] < ... < c[k-1] are cut (-1: before the first event, N-1: after the last)
   and the stretch that ends at c[i] is followed by the one that starts after c[nx[i]]; est: its gain by the V of
   its joins; ux -> uy: the closing join if it is not listed (-2: none), for a move of two pairs ux -> uy and
   ux2 -> uy2: its joins that are not listed; lg: all stretches between its cuts are long (--or3-long); tp: a move of two pairs;
   gx: its gain; zx, zl, zh: see o3_gain */
typedef struct {
    int k, c[O3KM], nx[O3KM], est, ux, uy, ux2, uy2, lg, tp, zx[O3KM], zl[O3KM], zh[O3KM];
    i64 gx;
} O3M;
/* a move as the search keeps it */
typedef struct {
    int c[O3KM], ux, uy, ux2, uy2;
    short est;
    signed char k, nx[O3KM];
    unsigned char lg, tp;
} O3S;
/* the stretches in their new order: first event, length, new place */
typedef struct {
    int ns;
    i64 lo[O3KM + 1], len[O3KM + 1], at[O3KM + 2];
} O3P;
typedef struct {
    u64 key;
    i64 zr, cum;
} O3C;
typedef struct {
    O3C *t;
    u64 mask;
    i64 n;
} O3Memo;
/* what a thread needs to judge candidates */
typedef struct {
    BS b;
    CO qb;
    unsigned char *T0, *T1;
    i64 st[4];
} O3T;
typedef struct {
    i64 N;
    int th, slack, kc, quiet;
    JG out, in;
    int *old; /* out: by V, then event (--or3-old: by event); in: by event */
    O3S *sv;
    i64 sn, scap; /* the moves found, before they are candidates */
    O3M *mv;
    i64 nc, nall, cap, ntried, budget, nnode[O3KM + 2]; /* nall candidates, nc of them for o3_round */
    O3Memo memo;
    POT P;
    const Ev *ev;
    O3T *tc;
    int ntc, pvalid;
    double tprep; /* pvalid: P belongs to the sequence that comes next */
    /* kept from round to round (only where eid is set): eid[p] names the event at place p; lastF / lastB[name]: the
       round after which its fw / bw last changed; vc: V of pairs of names that were not listed, with the round they are from */
    int *eid, *lastF, *lastB, round;
    struct O3V *vc;
    u64 vcmask;
    i64 vcn, vhit;
    /* lastJ[name]: the round after which the join after the event last changed; jc: the gains of the candidates judged
       in earlier rounds (see o3_jc_ok); jhit: taken from there this round */
    int *lastJ;
    struct O3J *jc;
    u64 jcmask;
    i64 jcn, jhit;
    /* for the pairs of the next round (o3_vupdate), if lvalid: new place -> old place, and whose fw / bw changed (by old place); they belong to o3_full */
    int lvalid;
    const int *lperm;
    const char *lchgF, *lchgB;
    /* lkeep: the sequence is the one of the round before, its pairs stay; dstart (--or3-focus): chains only from the cuts a with dstart[a + 1] */
    int lkeep;
    const char *dstart;
    i64 nstart;
    unsigned char *
        cl; /* of the thread that follows chains: cl[x + 1] = V of x -> the event after the first cut, 255: not listed */
} O3;
typedef struct O3V {
    u64 key;
    int stamp;
    unsigned char v;
} O3V;
/* the move by the names of its cuts; the round it was judged in; its gain; the lengths of its zones */
typedef struct O3J {
    u64 key;
    int stamp, gx;
    unsigned short zn[O3KM];
} O3J;
/* V of the pair if it is kept and still holds, else -1 */
static int o3_vc_get(const O3 *o, int nx, int ny) {
    if (!o->vc)
        return -1;
    u64 key = ((u64)nx << 24) | (u64)ny, i = hmix(key) & o->vcmask;
    while (o->vc[i].key != ~0ULL) {
        if (o->vc[i].key == key)
            return o->vc[i].stamp > o->lastF[nx] && o->vc[i].stamp > o->lastB[ny] ? o->vc[i].v : -1;
        i = (i + 1) & o->vcmask;
    }
    return -1;
}
/* Keeps the exact V of the join between the events named nx and ny, with the number of the round.  The
   table doubles when it is half full. */
static void o3_vc_put(O3 *o, int nx, int ny, int v) {
    if (!o->vc || 2 * (u64)(o->vcn + 1) > o->vcmask + 1) {
        O3V *old = o->vc;
        u64 om = o->vcmask;
        o->vcmask = old ? 2 * om + 1 : (1 << 16) - 1;
        o->vc = malloc((size_t)(o->vcmask + 1) * sizeof(O3V));
        if (!o->vc)
            DIE("out of memory");
        for (u64 z = 0; z <= o->vcmask; z++)
            o->vc[z].key = ~0ULL;
        if (old)
            for (u64 z = 0; z <= om; z++)
                if (old[z].key != ~0ULL) {
                    u64 q = hmix(old[z].key) & o->vcmask;
                    while (o->vc[q].key != ~0ULL)
                        q = (q + 1) & o->vcmask;
                    o->vc[q] = old[z];
                }
        free(old);
    }
    u64 key = ((u64)nx << 24) | (u64)ny, i = hmix(key) & o->vcmask;
    while (o->vc[i].key != ~0ULL && o->vc[i].key != key)
        i = (i + 1) & o->vcmask;
    if (o->vc[i].key == ~0ULL)
        o->vcn++;
    o->vc[i].key = key;
    o->vc[i].stamp = o->round;
    o->vc[i].v = (unsigned char)v;
}
static int o3cuts = 0, o3slack = 2, o3th = 6, o3dry = 0, o3plat = 0, o3old = 0, o3rounds = 0, o3margin = 8, o3dip = 2,
           o3xt = 3, o3zone = 0, o3full = 0, o3check = 0, o3nojc = 0, o3nolu = 0, o3focus = 0, o3lupct = 15,
           o3noskip = 0, o32pv = 1, o3long = 0, o3order = 1;
#define O3XMAX 8000 /* most expensive joins with the long lists */
static double o3sec = 0;
static i64 o3maxcand = 0, o3maxlay = -1; /* o3maxlay < 0: 4096, with --or3-old no limit */
static const char *o3stopfile = NULL, *o3plan = NULL;
static int o3_nround = 0;
static double o3_t0 = 0; /* rounds made, start of the pass */
#define O3NOW() (wall() - o3_t0)
/* --or3-rounds R, --or3-sec S (seconds since the pass began), --or3-stop FILE (stop when FILE exists) */
static int o3_stop(void) {
    if (o3rounds > 0 && o3_nround >= o3rounds)
        return 1;
    if (o3sec > 0 && O3NOW() > o3sec)
        return 1;
    if (o3stopfile) {
        FILE *f = fopen(o3stopfile, "rb");
        if (f) {
            fclose(f);
            return 1;
        }
    }
    return 0;
}
static int u64_cmp(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return x < y ? -1 : x > y;
}
static int int_cmp(const void *a, const void *b) {
    int x = *(const int *)a, y = *(const int *)b;
    return x < y ? -1 : x > y;
}
/* by the move */
static int o3k_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    if (x->k != y->k)
        return x->k < y->k ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->c[i] != y->c[i])
            return x->c[i] < y->c[i] ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->nx[i] != y->nx[i])
            return x->nx[i] < y->nx[i] ? -1 : 1;
    return 0;
}
/* the same order for the short form */
static int o3sk_cmp(const void *a, const void *b) {
    const O3S *x = a, *y = b;
    if (x->k != y->k)
        return x->k < y->k ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->c[i] != y->c[i])
            return x->c[i] < y->c[i] ? -1 : 1;
    for (int i = 0; i < x->k; i++)
        if (x->nx[i] != y->nx[i])
            return x->nx[i] < y->nx[i] ? -1 : 1;
    return 0;
}
/* by falling gain */
static int o3m_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    return x->gx > y->gx ? -1 : x->gx < y->gx ? 1 : o3k_cmp(a, b);
}
/* by falling estimate; --or3-order 1: the long ones first, then the chains, then the two-pair moves */
static int o3e_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    int u = o3order ? (x->lg ? 0 : 1 + x->tp) : 0, v = o3order ? (y->lg ? 0 : 1 + y->tp) : 0;
    return u != v ? (u < v ? -1 : 1) : x->est > y->est ? -1 : x->est < y->est ? 1 : o3k_cmp(a, b);
}
/* Frees the tables of a fixed-order pass. */
static void o3_cofree(CO *q) {
    free(q->t);
    free(q->S);
    free(q->E);
    free(q->Ep);
    free(q->mv);
    free(q->d);
    free(q->rel);
    free(q->off);
    free(q->lmin);
    free(q->cur);
    free(q->ban);
}
/* the cuts an event may take, in the order of bs_ev (no free skips): o3_it(&it, x); while (o3_next(&it)) ... it.j */
typedef struct {
    const Ev *x;
    const Trail *T;
    i64 o, end;
    int j, fixed;
} O3It;
static inline void o3_it(O3It *it, const Ev *x) {
    it->x = x;
    it->T = &TR[x->t];
    it->fixed = co_cur(x) < 0;
    it->o = it->T->olo - 1;
    it->end = it->T->ohi;
    it->j = -1;
}
/* Next cut the event of the iterator may take; 0 at the end.  An event that cannot be cut again has one. */
static inline int o3_next(O3It *it) {
    if (it->fixed) {
        if (it->j >= 0)
            return 0;
        it->j = 0;
        return 1;
    }
    for (it->o++; it->o < it->end; it->o++)
        if (!OP[it->o].g1 || oSK_t(it->T, it->o) == it->x->skip) {
            it->j++;
            return 1;
        }
    return 0;
}
static inline u64 o3_S(const O3It *it) {
    return it->fixed ? it->x->s : oS_t(it->T, it->o);
}
static inline u64 o3_E(const O3It *it) {
    return it->fixed ? it->x->e : oE_t(it->T, it->o);
}
/* in: for every event y the pairs (x, V), by x.  Every thread reads all pairs and takes those of its share of the y */
static void o3_transpose(const JG *out, JG *in, i64 N) {
    i64 cnt = out->off[N];
    in->off = calloc((size_t)(N + 2), 8);
    in->to = malloc((size_t)(cnt + 1) * sizeof(int));
    in->c = malloc((size_t)cnt + 1);
    if (!in->off || !in->to || !in->c)
        DIE("out of memory");
#pragma omp parallel num_threads(NTHR)
    {
        int t = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 ylo = N * t / nt, yhi = N * (t + 1) / nt;
        for (i64 e = 0; e < cnt; e++) {
            i64 y = out->to[e];
            if (y >= ylo && y < yhi)
                in->off[y + 2]++;
        }
#pragma omp barrier
#pragma omp single
        for (i64 y = 0; y < N; y++)
            in->off[y + 2] += in->off[y + 1];
        for (i64 x = 0; x < N; x++)
            for (i64 e = out->off[x]; e < out->off[x + 1]; e++) {
                i64 y = out->to[e];
                if (y >= ylo && y < yhi) {
                    i64 z = in->off[y + 1]++;
                    in->to[z] = (int)x;
                    in->c[z] = out->c[e];
                }
            }
    }
}
/* Sorts the cuts of one event by relative cost into the pool UE of the thread: bnd[v] .. bnd[v+1] hold the
   words of the cuts with cost v.  Cuts with cost h or more are left out. */
static void o3_pool1(BScr *w, const unsigned char *rel, const u64 *word, int m, i64 *bnd) {
    i64 pos[17];
    for (int v = 0; v <= h; v++)
        bnd[v] = 0;
    for (int j = 0; j < m; j++)
        if (rel[j] < h)
            bnd[rel[j] + 1]++;
    for (int v = 0; v < h; v++)
        bnd[v + 1] += bnd[v];
    if (bnd[h] > w->ucap) {
        w->ucap = bnd[h] + bnd[h] / 2 + 64;
        free(w->UE);
        w->UE = malloc((size_t)w->ucap * 8);
        if (!w->UE)
            DIE("out of memory");
    }
    for (int v = 0; v < h; v++)
        pos[v] = bnd[v];
    for (int j = 0; j < m; j++)
        if (rel[j] < h)
            w->UE[pos[rel[j]]++] = word[j];
}
/* fw (dir 0) or bw (dir 1) of the whole sequence */
static void o3_sweep(BS *b, const Ev *ev, i64 N, POT *P, int dir) {
    BScr *w = &b->scr[0];
    i64 bnd[18];
    b->ev = ev;
    b->N = N;
    for (int k = 0; k < b->ecn; k++)
        b->ec[k].id = -1;
    for (i64 z = 0; z < N; z++) {
        i64 p = dir ? N - 1 - z : z, pp = dir ? p + 1 : p - 1;
        BEv *e = bs_ev(b, p);
        int m = e->m, mn = 1 << 20;
        unsigned char *rel = (dir ? P->bw : P->fw) + P->off[p];
        if (m != P->off[p + 1] - P->off[p])
            DIE("internal error: segment insertion (openings of event %lld)", p);
        if (m > w->mcap) {
            w->mcap = m + m / 2 + 64;
            free(w->mv);
            w->mv = malloc((size_t)w->mcap * sizeof(int));
            if (!w->mv)
                DIE("out of memory");
        }
        int *mv = w->mv;
        for (int j = 0; j < m; j++)
            mv[j] = z ? h : 0;
        if (z) {
            BEv *x = bs_ev(b, pp);
            o3_pool1(w, (dir ? P->bw : P->fw) + P->off[pp], dir ? x->S : x->E, x->m, bnd);
            bs_join(w, bnd, &e, 1, mv, dir);
        }
        for (int j = 0; j < m; j++) {
            mv[j] += e->D[j];
            if (mv[j] < mn)
                mn = mv[j];
        }
        for (int j = 0; j < m; j++)
            rel[j] = (unsigned char)(mv[j] - mn < h ? mv[j] - mn : h); /* h: h or more (such an cut is never needed) */
        if (dir)
            P->gmin[p] = (z ? P->gmin[p + 1] : 0) + mn;
        else
            P->fmin[p] = (z ? P->fmin[p - 1] : 0) + mn;
    }
}
/* The two tables of a round: for every cut of every event its cost with the best of everything before it
   (fw) and after it (bw), relative to the minima fmin / gmin.  The two sweeps run in parallel. */
static void o3_pot(const Ev *ev, i64 N, POT *P) {
    P->off = malloc((size_t)(N + 1) * 8);
    P->fmin = malloc((size_t)(N + 1) * 8);
    P->gmin = malloc((size_t)(N + 1) * 8);
    if (!P->off || !P->fmin || !P->gmin)
        DIE("out of memory");
#pragma omp parallel for schedule(dynamic, 64) num_threads(NTHR)
    for (i64 p = 0; p < N; p++) {
        O3It it;
        i64 m = 0;
        o3_it(&it, &ev[p]);
        while (o3_next(&it))
            m++;
        P->off[p + 1] = m;
    }
    P->off[0] = 0;
    for (i64 p = 0; p < N; p++)
        P->off[p + 1] += P->off[p];
    P->fw = malloc((size_t)P->off[N] + 1);
    P->bw = malloc((size_t)P->off[N] + 1);
    if (!P->fw || !P->bw)
        DIE("out of memory");
#pragma omp parallel for schedule(static, 1) num_threads(NTHR > 1 ? 2 : 1)
    for (int dir = 0; dir < 2; dir++) {
        BS b;
        CO q;
        bs_init(&b, &q, 1);
        b.anyskip = 0;
        o3_sweep(&b, ev, N, P, dir);
        bs_free(&b);
    }
    if (P->fmin[N - 1] != P->gmin[0])
        DIE("internal error: forward %lld, backward %lld", P->fmin[N - 1], P->gmin[0]);
}
/* The pairs with V <= th.  A[b]: the start words of the cuts with bw = b as (word << 20 | event), sorted; dir:
   where every pair of leading symbols begins.  An cut of x with fw = f and end word E takes, for every overlap
   kk >= h - (th - f) and every b <= th - f - (h - kk), the entries of A[b] that begin with the last kk symbols of
   E: all of them are pairs with V <= th.
   Pairs between the two sides of expensive joins are listed up to th2 > th: xl[x] says that the join after x is
   expensive, xr[y] that the join before y is, and A[16 + b] holds the cuts of the events y with xr[y].
   st: cuts with fw <= th, with bw <= th, entries looked at. */
typedef struct {
    u64 *a;
    i64 n, dir[258];
} O3A;
typedef struct {
    int *to;
    unsigned char *c;
    i64 n, cap;
} O3Buf;
/* For end word E with relative cost rf: every cut on the other side whose start word overlaps it and whose
   cost keeps the sum at th or less, found in the sorted arrays A[b] (b = cost of the cut).  Updates best[] for
   the events found and lists them in touched. */
static inline void o3_vscan(const O3A *A, int th, int rf, u64 E, int x, unsigned char *best, int *touched, int *nt,
                            i64 *nscan) {
    for (int kk = h; kk >= h - (th - rf) && kk >= 1; kk--) {
        u64 wd = E & HMASK[kk], klo = (wd << (4 * (h - kk))) << 20, khi = ((wd + 1) << (4 * (h - kk))) << 20;
        int v0 = rf + h - kk;
        for (int b = 0; b <= th - v0; b++) {
            const O3A *a = &A[b];
            i64 lo, hi;
            if (kk == 1) {
                lo = a->dir[wd << 4];
                hi = a->dir[(wd + 1) << 4];
            } else {
                u64 bk = wd >> (4 * (kk - 2));
                lo = a->dir[bk];
                hi = a->dir[bk + 1];
            }
            if (kk > 2) {
                i64 z = hi;
                while (lo < z) {
                    i64 mid = (lo + z) >> 1;
                    if (a->a[mid] < klo)
                        lo = mid + 1;
                    else
                        z = mid;
                }
            }
            for (; lo < hi && a->a[lo] < khi; lo++) {
                int y = (int)(a->a[lo] & 0xFFFFF), v = v0 + b;
                (*nscan)++;
                if (y == x || v >= best[y])
                    continue;
                if (best[y] == 255)
                    touched[(*nt)++] = y;
                best[y] = (unsigned char)v;
            }
        }
    }
}
/* The pair lists of a round: V(x, y) for every pair of events with V <= th, and up to th2 for pairs between
   the two sides of expensive joins (xl, xr).  out: successors of x sorted by V; in: predecessors of y. */
static void o3_vbuild(const Ev *ev, i64 N, const POT *P, int th, int byev, const char *xl, const char *xr, int th2,
                      JG *out, JG *in, i64 *st) {
    int nthr = NTHR;
    O3A A[32];
    i64 nf = 0, nscan = 0;
    if (N >= (1 << 20) || th > 15 || th2 > 15)
        DIE("too many events");
    i64 *cnt = calloc((size_t)nthr * 32 * 256, 8), *xpos = malloc((size_t)(N + 1) * 8);
    int *xthr = malloc((size_t)(N + 1) * sizeof(int));
    O3Buf *buf = calloc((size_t)nthr, sizeof(O3Buf));
    out->off = malloc((size_t)(N + 1) * 8);
    if (!cnt || !xpos || !xthr || !buf || !out->off)
        DIE("out of memory");
    memset(A, 0, sizeof A);
#pragma omp parallel num_threads(nthr)
    {
        int t = omp_get_thread_num(), nt = omp_get_num_threads();
        i64 lo = N * t / nt, hi = N * (t + 1) / nt, *ct = cnt + (size_t)t * 32 * 256;
        for (i64 y = lo; y < hi; y++) {
            const unsigned char *bw = P->bw + P->off[y];
            int ext = xr && xr[y];
            O3It it;
            o3_it(&it, &ev[y]);
            while (o3_next(&it)) {
                int b = bw[it.j];
                if (b > th && !(ext && b <= th2))
                    continue;
                int k = (int)(o3_S(&it) >> (4 * (h - 2)));
                if (b <= th)
                    ct[b * 256 + k]++;
                if (ext && b <= th2)
                    ct[(16 + b) * 256 + k]++;
            }
        }
#pragma omp barrier
#pragma omp single
        {
            for (int b = 0; b < 32; b++) {
                i64 at = 0;
                for (int k = 0; k < 256; k++) {
                    A[b].dir[k] = at;
                    for (int z = 0; z < nt; z++) {
                        i64 c = cnt[((size_t)z * 32 + b) * 256 + k];
                        cnt[((size_t)z * 32 + b) * 256 + k] = at;
                        at += c;
                    }
                }
                A[b].dir[256] = A[b].dir[257] = at;
                A[b].n = at;
                A[b].a = malloc((size_t)(at + 1) * 8);
                if (!A[b].a)
                    DIE("out of memory");
            }
        }
        for (i64 y = lo; y < hi; y++) {
            const unsigned char *bw = P->bw + P->off[y];
            int ext = xr && xr[y];
            O3It it;
            o3_it(&it, &ev[y]);
            while (o3_next(&it)) {
                int b = bw[it.j];
                if (b > th && !(ext && b <= th2))
                    continue;
                u64 S = o3_S(&it);
                int k = (int)(S >> (4 * (h - 2)));
                if (b <= th)
                    A[b].a[ct[b * 256 + k]++] = (S << 20) | (u64)y;
                if (ext && b <= th2)
                    A[16 + b].a[ct[(16 + b) * 256 + k]++] = (S << 20) | (u64)y;
            }
        }
#pragma omp barrier
#pragma omp for schedule(dynamic, 4)
        for (int q = 0; q < 32 * 256; q++) {
            const O3A *a = &A[q >> 8];
            int k = q & 255;
            if (a->dir[k + 1] - a->dir[k] > 1)
                qsort(a->a + a->dir[k], (size_t)(a->dir[k + 1] - a->dir[k]), 8, u64_cmp);
        }
    }
#pragma omp parallel num_threads(nthr) reduction(+ : nf, nscan)
    {
        O3Buf *B = &buf[omp_get_thread_num()];
        unsigned char *best = malloc((size_t)N + 1);
        int *touched = malloc((size_t)(N + 1) * sizeof(int));
        if (!best || !touched)
            DIE("out of memory");
        memset(best, 255, (size_t)N + 1);
#pragma omp for schedule(dynamic, 16)
        for (i64 x = 0; x < N; x++) {
            const unsigned char *fw = P->fw + P->off[x];
            int nt = 0, ext = xl && xl[x];
            O3It it;
            o3_it(&it, &ev[x]);
            while (o3_next(&it)) {
                int rf = fw[it.j];
                if (rf > th && !(ext && rf <= th2))
                    continue;
                u64 E = o3_E(&it);
                if (rf <= th) {
                    nf++;
                    o3_vscan(A, th, rf, E, (int)x, best, touched, &nt, &nscan);
                }
                if (ext && rf <= th2)
                    o3_vscan(A + 16, th2, rf, E, (int)x, best, touched, &nt, &nscan);
            }
            if (!byev)
                for (int t = 0; t < nt; t++)
                    touched[t] |= best[touched[t]] << 20;
            qsort(touched, (size_t)nt, sizeof(int), int_cmp);
            if (B->n + nt > B->cap) {
                B->cap = (B->n + nt) * 2 + 4096;
                B->to = realloc(B->to, (size_t)B->cap * sizeof(int));
                B->c = realloc(B->c, (size_t)B->cap);
                if (!B->to || !B->c)
                    DIE("out of memory");
            }
            xthr[x] = omp_get_thread_num();
            xpos[x] = B->n;
            out->off[x + 1] = nt;
            for (int t = 0; t < nt; t++) {
                int y = touched[t] & 0xFFFFF;
                B->to[B->n] = y;
                B->c[B->n++] = best[y];
                best[y] = 255;
            }
        }
        free(best);
        free(touched);
    }
    st[0] = nf;
    st[1] = 0;
    for (int b = 0; b < 16; b++)
        st[1] += A[b].n;
    st[2] = nscan;
    for (int b = 0; b < 32; b++)
        free(A[b].a);
    out->off[0] = 0;
    for (i64 x = 0; x < N; x++)
        out->off[x + 1] += out->off[x];
    out->to = malloc((size_t)(out->off[N] + 1) * sizeof(int));
    out->c = malloc((size_t)out->off[N] + 1);
    if (!out->to || !out->c)
        DIE("out of memory");
#pragma omp parallel for schedule(static) num_threads(nthr)
    for (i64 x = 0; x < N; x++) {
        i64 m = out->off[x + 1] - out->off[x];
        const O3Buf *B = &buf[xthr[x]];
        if (m) {
            memcpy(out->to + out->off[x], B->to + xpos[x], (size_t)m * sizeof(int));
            memcpy(out->c + out->off[x], B->c + xpos[x], (size_t)m);
        }
    }
    for (int t = 0; t < nthr; t++) {
        free(buf[t].to);
        free(buf[t].c);
    }
    free(buf);
    free(cnt);
    free(xpos);
    free(xthr);
    o3_transpose(out, in, N);
}
/* ---- the pairs after a round, from the pairs before it.  V of a pair depends only on fw of its first event and bw
   of its second (and on the cuts they may take), so after a round only the pairs of the events whose fw changed
   (F) with all events, and of all events with those whose bw changed (B), are made again.  For that the cuts of
   all events are looked up in two small tables: their end words among the start words of the cuts of B, by bw
   (as in o3_vbuild), and their start words, read backwards, among the end words read backwards of the cuts of F,
   by fw (a word read backwards begins with its last symbol, so the same search finds the overlap from the other
   side).  All other pairs with V <= th are taken over and get their new places; the pairs between the sides of
   expensive joins (V > th) are made new every round.  The lists are those o3_vbuild would give (--or3-check
   compares them).  perm: new place -> old place; chgF, chgB: by old place; out0: the lists of the old sequence.
   st: events in F, in B, entries looked at, cuts in the two small tables; o3_lu_t: seconds for the small
   tables, for the lists, for turning them round. */
static double o3_lu_t[3];
static inline u64 o3_rev(u64 w) {
    u64 r = 0;
    for (int k = 0; k < h; k++) {
        r = (r << 4) | (w & 15);
        w >>= 4;
    }
    return r;
}
/* A[v], v <= th: the cuts with cost v of the events with sel set (dir 0: bw and start word; dir 1: fw and the end word read backwards) */
static void o3_vsmall(const Ev *ev, i64 N, const POT *P, int th, const char *sel, int dir, O3A *A) {
    i64 ns = 0, tot[16] = {0}, *pc;
    int *lst = malloc((size_t)(N + 1) * sizeof(int));
    if (!lst)
        DIE("out of memory");
    for (i64 y = 0; y < N; y++)
        if (sel[y])
            lst[ns++] = (int)y;
    pc = calloc((size_t)(ns + 1) * 16, 8);
    if (!pc)
        DIE("out of memory"); /* for every event and cost: how many, then where they go */
#pragma omp parallel for schedule(dynamic, 4) num_threads(NTHR)
    for (i64 q = 0; q < ns; q++) {
        i64 y = lst[q], *c = pc + q * 16;
        const unsigned char *tab = (dir ? P->fw : P->bw) + P->off[y];
        for (i64 j = 0, m = P->off[y + 1] - P->off[y]; j < m; j++)
            if (tab[j] <= th)
                c[tab[j]]++;
    }
    for (i64 q = 0; q < ns; q++)
        for (int v = 0; v <= th; v++) {
            i64 c = pc[q * 16 + v];
            pc[q * 16 + v] = tot[v];
            tot[v] += c;
        }
    for (int v = 0; v <= th; v++) {
        A[v].a = malloc((size_t)(tot[v] + 1) * 8);
        A[v].n = tot[v];
        if (!A[v].a)
            DIE("out of memory");
    }
#pragma omp parallel for schedule(dynamic, 4) num_threads(NTHR)
    for (i64 q = 0; q < ns; q++) {
        i64 y = lst[q], *c = pc + q * 16;
        const unsigned char *tab = (dir ? P->fw : P->bw) + P->off[y];
        O3It it;
        o3_it(&it, &ev[y]);
        while (o3_next(&it)) {
            int v = tab[it.j];
            if (v <= th)
                A[v].a[c[v]++] = ((dir ? o3_rev(o3_E(&it)) : o3_S(&it)) << 20) | (u64)y;
        }
    }
    free(lst);
    free(pc);
#pragma omp parallel for schedule(dynamic, 1) num_threads(NTHR)
    for (int v = 0; v <= th; v++) {
        O3A *a = &A[v];
        i64 at = 0;
        if (a->n > 1)
            qsort(a->a, (size_t)a->n, 8, u64_cmp);
        for (int k = 0; k <= 256; k++) {
            while (at < a->n && (i64)(a->a[at] >> (20 + 4 * (h - 2))) < k)
                at++;
            a->dir[k] = at;
        }
        a->dir[256] = a->dir[257] = a->n;
    }
}
/* how many cuts within th the events have whose costs changed (cF from the front, cB from the back), and all events (tF, tB) */
static void o3_share(const POT *P, i64 N, int th, const int *perm, const char *chgF, const char *chgB, i64 *res) {
    i64 tF = 0, tB = 0, cF = 0, cB = 0;
#pragma omp parallel for schedule(dynamic, 64) num_threads(NTHR) reduction(+ : tF, tB, cF, cB)
    for (i64 x = 0; x < N; x++) {
        const unsigned char *fw = P->fw + P->off[x], *bw = P->bw + P->off[x];
        i64 m = P->off[x + 1] - P->off[x], f = 0, b = 0;
        for (i64 j = 0; j < m; j++) {
            f += fw[j] <= th;
            b += bw[j] <= th;
        }
        tF += f;
        tB += b;
        if (chgF[perm[x]])
            cF += f;
        if (chgB[perm[x]])
            cB += b;
    }
    res[0] = tF;
    res[1] = tB;
    res[2] = cF;
    res[3] = cB;
}
/* The pair lists of this round from those of the last one (out0).  perm gives the old place of every
   event; chgF and chgB say whose costs from the front and from the back have changed.  Only pairs with a changed
   side are searched again, the others are copied.  The result is what o3_vbuild makes (--or3-check compares). */
static void o3_vupdate(const Ev *ev, i64 N, const POT *P, int th, const char *xl, const char *xr, int th2,
                       const JG *out0, const int *perm, const char *chgF, const char *chgB, JG *out, JG *in, i64 *st) {
    double t0 = wall(), t1, t2;
    int nthr = NTHR;
    O3A A[32], AF[16];
    i64 nscan = 0, nF = 0, nB = 0, ntri = 0, *xpos = malloc((size_t)(N + 1) * 8);
    int *xthr = malloc((size_t)(N + 1) * sizeof(int)), *inv = malloc((size_t)(N + 1) * sizeof(int)), *lf;
    char *Fn = malloc((size_t)N + 1), *Bn = malloc((size_t)N + 1);
    O3Buf *buf = calloc((size_t)nthr, sizeof(O3Buf));
    u64 *tri = NULL;
    if (N >= (1 << 20) || th > 15 || th2 > 15)
        DIE("too many events");
    out->off = malloc((size_t)(N + 1) * 8);
    if (!xpos || !xthr || !inv || !Fn || !Bn || !buf || !out->off)
        DIE("out of memory");
    for (i64 x = 0; x < N; x++) {
        Fn[x] = chgF[perm[x]];
        Bn[x] = chgB[perm[x]];
        inv[perm[x]] = (int)x;
        nF += Fn[x] != 0;
        nB += Bn[x] != 0;
    }
    lf = malloc((size_t)(nF + 1) * sizeof(int));
    if (!lf)
        DIE("out of memory");
    {
        i64 m = 0;
        for (i64 x = 0; x < N; x++)
            if (Fn[x])
                lf[m++] = (int)x;
    }
    memset(A, 0, sizeof A);
    memset(AF, 0, sizeof AF);
    o3_vsmall(ev, N, P, th, Bn, 0, A);
    if (xr)
        o3_vsmall(ev, N, P, th2, xr, 0, A + 16);
    o3_vsmall(ev, N, P, th, Fn, 1, AF);
    t1 = wall();
    st[3] = st[4] = 0;
    for (int b = 0; b <= th; b++) {
        st[3] += AF[b].n;
        st[4] += A[b].n;
    }
#pragma omp parallel num_threads(nthr) reduction(+ : nscan)
    {
        O3Buf *B = &buf[omp_get_thread_num()];
        unsigned char *best = malloc((size_t)N + 1), *bestx = malloc((size_t)N + 1);
        int *touched = malloc((size_t)(N + 1) * sizeof(int)), *touchx = malloc((size_t)(N + 1) * sizeof(int));
        u64 *L = NULL;
        i64 ln = 0, lcap = 0;
        if (!best || !bestx || !touched || !touchx)
            DIE("out of memory");
        memset(best, 255, (size_t)N + 1);
        memset(bestx, 255, (size_t)N + 1);
/* every event: as the second of a pair with the events of F (kept as x, y, V); if it is not in F, its own list */
#pragma omp for schedule(dynamic, 16)
        for (i64 x = 0; x < N; x++) {
            const unsigned char *fw = P->fw + P->off[x], *bw = P->bw + P->off[x];
            int nt = 0, ntx = 0, ext = xl && xl[x], own = !Fn[x];
            O3It it;
            o3_it(&it, &ev[x]);
            if (own) {
                i64 xo = perm[x];
                for (i64 f = out0->off[xo]; f < out0->off[xo + 1]; f++)
                    if (out0->c[f] <= th && !chgB[out0->to[f]]) {
                        int y = inv[out0->to[f]];
                        best[y] = out0->c[f];
                        touched[nt++] = y;
                    }
            }
            while (o3_next(&it)) {
                int rf = fw[it.j], rb = bw[it.j];
                if (nF && rb <= th)
                    o3_vscan(AF, th, rb, o3_rev(o3_S(&it)), (int)x, bestx, touchx, &ntx, &nscan);
                if (!own || (rf > th && !(ext && rf <= th2)))
                    continue;
                u64 E = o3_E(&it);
                if (nB && rf <= th)
                    o3_vscan(A, th, rf, E, (int)x, best, touched, &nt, &nscan);
                if (ext && rf <= th2)
                    o3_vscan(A + 16, th2, rf, E, (int)x, best, touched, &nt, &nscan);
            }
            if (ln + ntx > lcap) {
                lcap = (ln + ntx) * 2 + 4096;
                L = realloc(L, (size_t)lcap * 8);
                if (!L)
                    DIE("out of memory");
            }
            for (int t = 0; t < ntx; t++) {
                int xf = touchx[t];
                L[ln++] = ((u64)xf << 28) | ((u64)x << 8) | bestx[xf];
                bestx[xf] = 255;
            }
            out->off[x + 1] = 0;
            if (!own)
                continue;
            for (int t = 0; t < nt; t++)
                touched[t] |= best[touched[t]] << 20;
            qsort(touched, (size_t)nt, sizeof(int), int_cmp);
            if (B->n + nt > B->cap) {
                B->cap = (B->n + nt) * 2 + 4096;
                B->to = realloc(B->to, (size_t)B->cap * sizeof(int));
                B->c = realloc(B->c, (size_t)B->cap);
                if (!B->to || !B->c)
                    DIE("out of memory");
            }
            xthr[x] = omp_get_thread_num();
            xpos[x] = B->n;
            out->off[x + 1] = nt;
            for (int t = 0; t < nt; t++) {
                int y = touched[t] & 0xFFFFF;
                B->to[B->n] = y;
                B->c[B->n++] = best[y];
                best[y] = 255;
            }
        }
#pragma omp critical(o3tri)
        {
            tri = realloc(tri, (size_t)(ntri + ln + 1) * 8);
            if (!tri)
                DIE("out of memory");
            if (ln)
                memcpy(tri + ntri, L, (size_t)ln * 8);
            ntri += ln;
        }
        free(L);
#pragma omp barrier
#pragma omp single
        {
            if (ntri > 1)
                qsort(tri, (size_t)ntri, 8, u64_cmp);
        }
/* the events of F: their pairs from what was kept, and those between expensive joins */
#pragma omp for schedule(dynamic, 4)
        for (i64 q = 0; q < nF; q++) {
            i64 x = lf[q], lo = 0, hi = ntri;
            int nt = 0, ext = xl && xl[x];
            u64 key = (u64)x << 28;
            while (lo < hi) {
                i64 mid = (lo + hi) >> 1;
                if (tri[mid] < key)
                    lo = mid + 1;
                else
                    hi = mid;
            }
            for (; lo < ntri && (i64)(tri[lo] >> 28) == x; lo++) {
                int y = (int)((tri[lo] >> 8) & 0xFFFFF);
                best[y] = (unsigned char)(tri[lo] & 255);
                touched[nt++] = y;
            }
            if (ext) {
                const unsigned char *fw = P->fw + P->off[x];
                O3It it;
                o3_it(&it, &ev[x]);
                while (o3_next(&it)) {
                    int rf = fw[it.j];
                    if (rf <= th2)
                        o3_vscan(A + 16, th2, rf, o3_E(&it), (int)x, best, touched, &nt, &nscan);
                }
            }
            for (int t = 0; t < nt; t++)
                touched[t] |= best[touched[t]] << 20;
            qsort(touched, (size_t)nt, sizeof(int), int_cmp);
            if (B->n + nt > B->cap) {
                B->cap = (B->n + nt) * 2 + 4096;
                B->to = realloc(B->to, (size_t)B->cap * sizeof(int));
                B->c = realloc(B->c, (size_t)B->cap);
                if (!B->to || !B->c)
                    DIE("out of memory");
            }
            xthr[x] = omp_get_thread_num();
            xpos[x] = B->n;
            out->off[x + 1] = nt;
            for (int t = 0; t < nt; t++) {
                int y = touched[t] & 0xFFFFF;
                B->to[B->n] = y;
                B->c[B->n++] = best[y];
                best[y] = 255;
            }
        }
        free(best);
        free(bestx);
        free(touched);
        free(touchx);
    }
    st[0] = nF;
    st[1] = nB;
    st[2] = nscan;
    for (int b = 0; b < 32; b++)
        free(A[b].a);
    for (int b = 0; b < 16; b++)
        free(AF[b].a);
    free(tri);
    free(lf);
    free(Fn);
    free(Bn);
    free(inv);
    out->off[0] = 0;
    for (i64 x = 0; x < N; x++)
        out->off[x + 1] += out->off[x];
    out->to = malloc((size_t)(out->off[N] + 1) * sizeof(int));
    out->c = malloc((size_t)out->off[N] + 1);
    if (!out->to || !out->c)
        DIE("out of memory");
#pragma omp parallel for schedule(static) num_threads(nthr)
    for (i64 x = 0; x < N; x++) {
        i64 m = out->off[x + 1] - out->off[x];
        const O3Buf *B = &buf[xthr[x]];
        if (m) {
            memcpy(out->to + out->off[x], B->to + xpos[x], (size_t)m * sizeof(int));
            memcpy(out->c + out->off[x], B->c + xpos[x], (size_t)m);
        }
    }
    for (int t = 0; t < nthr; t++) {
        free(buf[t].to);
        free(buf[t].c);
    }
    free(buf);
    free(xpos);
    free(xthr);
    t2 = wall();
    o3_transpose(out, in, N);
    o3_lu_t[0] = t1 - t0;
    o3_lu_t[1] = t2 - t1;
    o3_lu_t[2] = wall() - t2;
}
/* Are two pair lists equal?  (--or3-check) */
static int o3_jg_same(const JG *A, const JG *B, i64 N) {
    return !memcmp(A->off, B->off, (size_t)(N + 1) * 8) && !memcmp(A->to, B->to, (size_t)A->off[N] * sizeof(int)) &&
           !memcmp(A->c, B->c, (size_t)A->off[N]);
}
/* V of x -> y if the pair is listed, else -1 */
static inline int o3_look(const O3 *o, i64 x, i64 y) {
    const JG *g = &o->in;
    i64 a = g->off[y], b = g->off[y + 1];
    while (a < b) {
        i64 m = (a + b) >> 1;
        if (g->to[m] < x)
            a = m + 1;
        else
            b = m;
    }
    return a < g->off[y + 1] && g->to[a] == x ? g->c[a] : -1;
}
/* V of the join of piece x to piece y, from the lists. */
/* x = -1: nothing before y; y = N: nothing after x; not listed: th + 1 */
static inline int o3_v(const O3 *o, i64 x, i64 y) {
    if (x < 0 || y >= o->N)
        return 0;
    int v = o3_look(o, x, y);
    return v < 0 ? o->th + 1 : v;
}
static inline int o3_old(const O3 *o, i64 c) {
    return c < 0 || c >= o->N - 1 ? 0 : o->old[c];
}
/* V of x -> y from the tables (h: h or more) */
static int o3_exactv(BS *b, const POT *P, i64 x, i64 y) {
    BScr *w = &b->scr[0];
    i64 bnd[18];
    {
        BEv *ex = bs_ev(b, x);
        o3_pool1(w, P->fw + P->off[x], ex->E, ex->m, bnd);
    }
    BEv *e = bs_ev(b, y);
    int mm = e->m, mn = 1 << 20;
    const unsigned char *bw = P->bw + P->off[y];
    if (mm > w->mcap) {
        w->mcap = mm + mm / 2 + 64;
        free(w->mv);
        w->mv = malloc((size_t)w->mcap * sizeof(int));
        if (!w->mv)
            DIE("out of memory");
    }
    int *mv = w->mv;
    for (int q = 0; q < mm; q++)
        mv[q] = h;
    bs_join(w, bnd, &e, 1, mv, 0);
    for (int q = 0; q < mm; q++)
        if (mv[q] + bw[q] < mn)
            mn = mv[q] + bw[q];
    return mn < h ? mn : h;
}
/* the stretches of a move in their new order; 0: they do not form one sequence */
static int o3_order(const O3M *m, i64 N, O3P *P) {
    int k = m->k, s = 0, n = 0;
    i64 at = 0;
    for (;;) {
        i64 lo = s ? m->c[s - 1] + 1 : 0, hi = s < k ? m->c[s] : N - 1;
        if (n > k)
            return 0;
        P->lo[n] = lo;
        P->len[n] = hi - lo + 1;
        P->at[n] = at;
        at += hi - lo + 1;
        n++;
        if (s == k)
            break;
        s = m->nx[s] + 1;
    }
    P->ns = n;
    P->at[n] = at;
    return n == k + 1;
}
/* Writes into ev2 the sequence that move m makes of ev. */
static void o3_permute(const Ev *ev, Ev *ev2, i64 N, const O3M *m) {
    O3P P;
    if (!o3_order(m, N, &P))
        DIE("internal error: segment insertion (order)");
    for (int j = 0; j < P.ns; j++)
        memcpy(ev2 + P.at[j], ev + P.lo[j], (size_t)P.len[j] * sizeof(Ev));
}
/* ==================== own part of this file, 1: moves of equal length (--or3-eq) ==================== */
/* ---------- moves of equal length in every round (--or3-eq E).
   On a piece set with many equal small trails thousands of candidates keep the length, and there an estimate of 0
   means equal length.  After some fifty such moves the next round has hundreds of shorter candidates.
   A round with --or3-eq E:
   - The candidates with estimate 0 are kept apart from the others.  The others go through the batches of o3_full as
     always (--or3-maxcand M), the shorter ones are taken, the best first.
   - With the last batch, E of the candidates with estimate 0 whose place is still free are drawn at random.  Those
     that are not long are judged with that batch (on the card with --or3-gpu), so a shorter one among them is taken
     with the shorter ones.  A long candidate (--or3-long Z) gains exactly its estimate, so a long one with estimate 0
     is a move of equal length as it stands: it is not judged here.  (Without --or3-eq such candidates are left out
     when they are found; with it they stay, and only long ones with an estimate below 0 are left out.)
   - Then all candidates of the round with gain 0, and the long ones drawn, are taken in random order wherever the
     place is still free (--or3-eq-max M: at most M), except one that would make a join again that was cut in the
     last --or3-eq-tabu rounds (default 8).  Each is judged once more with its zones before it is taken, as the
     shorter ones are; that is where a long candidate gets its exact gain, and it is taken only if that is 0.
   - All moves of the round are made together by o3_full (o3_compose + o3_tables_move), so the tables, the stamps
     and the pair lists are brought up to date as after any round.  A round may leave the length as it was; it
     never makes the word longer.  The plan is written after every round (to a new file that then replaces the old
     one), so the plan file always has the best length reached.
   - The pass ends after --or3-eq-stop K rounds in a row without a gain (default 20), when no move is left, or by
     --or3-rounds / --or3-sec / --or3-stop.  --or3-eq-seed S (or --or3-seed S): the random numbers.
   Use --or3-slack 1: the rule needs the candidates with estimate 0, and with slack 0 there are none.
   With one batch (no --or3-maxcand, or one larger than the list) and without --or3-eq-keep the moves of a round
   depend only on the plan, the seed and the number of threads, on the host as on the card.
   --or3-eq-keep K (0: off): memory.  With slack 1 the search keeps every move it finds with estimate 0, most of
   them with a closing join that is not listed and is valued later (on a plan that is not polished: tens of
   millions).  With K only about K of them are kept: one in D, chosen by a hash of the move (so a move that is
   found from several of its cuts is kept or left as a whole), where D = the number found in the round before / K,
   rounded up; the first round of a pass searches once more before, only to count.  A candidate whose estimate
   comes down to 0 when its join is valued is thinned in the same way, so the draw stays even.  The moves with an
   estimate above 0 are never thinned (slack 1 finds about twice as many of them as slack 0: chains may dip lower). */
static i64 o3q_eq = 0, o3q_max = 0;
static int o3q_tabu = 8, o3q_patience = 20;
static u64 o3q_s[2] = {0x9E3779B97F4A7C15ULL, 0xD1B54A32D192ED03ULL};
/* The next 64 random bits of the draw (xorshift128+, seeded by --or3-seed). */
static inline u64 o3q_rnd(void) {
    u64 a = o3q_s[0], b = o3q_s[1];
    o3q_s[0] = b;
    a ^= a << 23;
    o3q_s[1] = a ^ b ^ (a >> 17) ^ (b >> 26);
    return o3q_s[1] + b;
}
/* a long candidate is left out if its estimate is at or below this */
static inline int o3q_lbar(int slack) {
    return o3q_eq > 0 && slack > 0 ? -1 : 0;
}
/* --or3-eq-keep: z0[thread]: moves with estimate 0 found; seen: their number in the last search (-1: none yet);
   div: one in div is kept; cnt: the search only counts */
static i64 o3q_keep = 0, o3q_z0[256][8], o3q_seen = -1;
static u64 o3q_div = 1, o3q_salt = 0, o3q_seedv = 0;
static int o3q_cnt = 0;
/* Hash of a move (its cuts and the order of its blocks) with the salt of the search, for --or3-eq-keep. */
static inline u64 o3q_mhash(int k, const int *c, const int *nx) {
    u64 x = o3q_salt ^ (u64)k;
    for (int i = 0; i < k; i++) {
        x = (x ^ (u64)(u32)c[i]) * 1099511628211ULL;
        x = (x ^ (u64)nx[i]) * 1099511628211ULL;
    }
    return hmix(x);
}
/* a move just found: 1 = it is not kept */
static inline int o3q_skip(const O3M *m) {
    if (o3q_eq <= 0)
        return 0;
    if (m->est == 0) {
        o3q_z0[omp_get_thread_num()][0]++;
        if (!o3q_cnt && o3q_div > 1 && o3q_mhash(m->k, m->c, m->nx) % o3q_div)
            return 1;
    }
    return o3q_cnt;
}
/* the same test for a candidate whose estimate has come down to 0 */
static inline int o3q_skip_s(const O3S *c) {
    int nx[O3KM];
    if (o3q_eq <= 0 || o3q_div <= 1)
        return 0;
    for (int i = 0; i < c->k; i++)
        nx[i] = c->nx[i];
    return o3q_mhash(c->k, c->c, nx) % o3q_div != 0;
}
static int o3_longz = 0; /* --or3-long Z, raised to twice the longest zone seen plus one */
static inline int o3_islong(const O3M *m) {
    if (o3_longz <= 0)
        return 0;
    for (int i = 0; i + 1 < m->k; i++)
        if (m->c[i + 1] - m->c[i] < o3_longz)
            return 0;
    return 1;
}
/* Appends move m to the short list of moves found.  A move gets its full record only when it is a candidate. */
static inline void o3_push(O3 *o, const O3M *m) {
    if (o->sn == o->scap) {
        o->scap = o->scap ? o->scap + o->scap / 2 : 1 << 14;
        o->sv = realloc(o->sv, (size_t)o->scap * sizeof(O3S));
        if (!o->sv)
            DIE("out of memory");
    }
    O3S *s = &o->sv[o->sn++];
    s->k = (signed char)m->k;
    s->est = (short)m->est;
    s->lg = (unsigned char)m->lg;
    s->tp = (unsigned char)m->tp;
    s->ux = m->ux;
    s->uy = m->uy;
    s->ux2 = m->ux2;
    s->uy2 = m->uy2;
    for (int i = 0; i < O3KM; i++) {
        s->c[i] = m->c[i];
        s->nx[i] = (signed char)m->nx[i];
    }
}
/* r[0 .. k-1]: the cuts in the order they were made; the stretch that ends at r[i] is followed by the one that starts after r[i+1], the last by the one after r[0] */
static void o3_emit(O3 *o, const int *r, int k, int est, int ux, int uy) {
    O3M m;
    O3P P;
    int ord[O3KM], rank[O3KM];
    memset(&m, 0, sizeof m);
    m.k = k;
    m.est = est;
    m.ux = ux;
    m.uy = uy;
    m.ux2 = m.uy2 = -2;
    for (int i = 0; i < k; i++) {
        int z = i;
        while (z > 0 && r[ord[z - 1]] > r[i]) {
            ord[z] = ord[z - 1];
            z--;
        }
        ord[z] = i;
    }
    for (int z = 0; z < k; z++) {
        m.c[z] = r[ord[z]];
        rank[ord[z]] = z;
    }
    for (int i = 0; i < k; i++)
        m.nx[rank[i]] = rank[(i + 1) % k];
    if (!o3_order(&m, o->N, &P))
        return;
    m.lg = o3_islong(&m);
    if (m.lg && est <= o3q_lbar(o->slack) && !o3check)
        return; /* long: its gain is its estimate, which the exact V of a join can only lower */
    if (o3q_skip(&m))
        return;
    o3_push(o, &m);
}
/* the chains: g is V of the cuts r[0 .. d] minus V of the joins made */
static void o3_dfs(O3 *o, int *r, int d, int g);
/* the new join r[d] -> y, worth v; then the join before y is cut */
static inline void o3_step(O3 *o, int *r, int d, int g, i64 y, int v) {
    int c = (int)y - 1, p = g - v, sl = o->slack;
    if (p <= -sl - o3dip || c == r[d])
        return;
    for (int z = 0; z < d; z++)
        if (r[z] == c)
            return;
    r[d + 1] = c;
    p += o3_old(o, c);
    if (d + 2 >= 3) { /* close it: c -> the event after the first cut */
        i64 y0 = (i64)r[0] + 1;
        int v2 = c < 0 || y0 >= o->N ? 0 : o->cl[c + 1] == 255 ? -1 : o->cl[c + 1];
        if (v2 >= 0) {
            if (p - v2 > -sl)
                o3_emit(o, r, d + 2, p - v2, -2, -2);
        } else if (p - (o->th + 1) > -sl)
            o3_emit(o, r, d + 2, p - (o->th + 1), c, (int)y0);
    }
    if (d + 2 < o->kc)
        o3_dfs(o, r, d + 1, p);
}
/* Chain search, one level: the left event of the last cut (r[d]) gets each listed successor in turn, as long
   as the sum so far stays above -slack - dip.  g: V of the cuts made minus V of the joins made. */
static void o3_dfs(O3 *o, int *r, int d, int g) {
    i64 N = o->N;
    int x = r[d], lim = g + o->slack + o3dip;
    o->nnode[d]++;
    if (o->ntried++ > o->budget)
        return;
    if (x < 0) {
        for (i64 y = 1; y < N; y++)
            o3_step(o, r, d, g, y, 0);
        return;
    } /* y becomes the first event */
    const JG *out = &o->out;
    for (i64 f = out->off[x], e1 = out->off[x + 1]; f < e1 && out->c[f] < lim; f++)
        o3_step(o, r, d, g, out->to[f], out->c[f]);
    if (x < N - 1)
        o3_step(o, r, d, g, N, 0); /* x becomes the last event */
}
/* --or3-old: the same with pairs that are not listed inside the chain (worth th + 1) and no values computed; lists by event */
static void o3_dfs0(O3 *o, int *r, int d, int g);
/* As o3_step, for --or3-old: a closing join that is not listed counts as th + 1. */
static inline void o3_step0(O3 *o, int *r, int d, int g, i64 y, int v) {
    int c = (int)y - 1, p = g - v;
    if (p <= -o->slack || c == r[d])
        return;
    for (int z = 0; z <= d; z++)
        if (r[z] == c)
            return;
    r[d + 1] = c;
    p += o3_old(o, c);
    if (d + 2 >= 3 && p - o3_v(o, c, (i64)r[0] + 1) > -o->slack)
        o3_emit(o, r, d + 2, p - o3_v(o, c, (i64)r[0] + 1), -2, -2);
    if (d + 2 < o->kc)
        o3_dfs0(o, r, d + 1, p);
}
/* As o3_dfs, for --or3-old: also tries every successor that is not listed, as worth th + 1. */
static void o3_dfs0(O3 *o, int *r, int d, int g) {
    i64 N = o->N;
    int x = r[d], U = o->th + 1;
    o->nnode[d]++;
    if (o->ntried++ > o->budget)
        return;
    if (x < 0) {
        for (i64 y = 1; y < N; y++)
            o3_step0(o, r, d, g, y, 0);
        return;
    }
    const JG *out = &o->out;
    i64 e = out->off[x], e1 = out->off[x + 1];
    for (i64 f = e; f < e1; f++)
        o3_step0(o, r, d, g, out->to[f], out->c[f]);
    if (x < N - 1)
        o3_step0(o, r, d, g, N, 0);
    if (g - U > -o->slack)
        for (i64 y = 0; y < N; y++) { /* pairs that are not listed */
            while (e < e1 && out->to[e] < y)
                e++;
            if (!(e < e1 && out->to[e] == y))
                o3_step0(o, r, d, g, y, U);
        }
}
/* A D C B E is not found that way: its new joins are two pairs, a -> b+1 with b -> a+1 and c -> d+1 with d -> c+1
   for cuts a < c < b < d, and neither pair alone leaves one sequence.  All pairs (a, b) with a listed join are
   collected with their value e = V(a, a+1) + V(b, b+1) - V(a, b+1) - V(b, a+1) (a join that is not listed: th + 1);
   a candidate has a pair with 2e > -slack, and for each of those the pairs that cross it are looked through:
   they are kept by falling e, and within one e by their first cut (X) and by their second cut (Y), so only
   pairs with e high enough and a cut inside the span are touched. */
/* u: 1: a -> b+1 is not listed, 2: b -> a+1 is not */
typedef struct {
    int a, b, e, u;
} O3X;
/* Order of the pairs for two-pair moves: by falling value e, then by first cut, then by second cut. */
static int o3xa_cmp(const void *x, const void *y) {
    const O3X *p = x, *q = y;
    return p->e != q->e   ? (p->e > q->e ? -1 : 1)
           : p->a != q->a ? (p->a < q->a ? -1 : 1)
           : p->b < q->b  ? -1
                          : p->b > q->b;
}
/* The same order with the second cut before the first. */
static int o3xb_cmp(const void *x, const void *y) {
    const O3X *p = x, *q = y;
    return p->e != q->e   ? (p->e > q->e ? -1 : 1)
           : p->b != q->b ? (p->b < q->b ? -1 : 1)
           : p->a < q->a  ? -1
                          : p->a > q->a;
}
/* Puts the four-cut move made of the pairs x and y on the list of candidates. */
/* x.a < y.a < x.b < y.b */
static void o3_cross4(O3 *o, const O3X *x, const O3X *y) {
    O3M m;
    O3P P;
    memset(&m, 0, sizeof m);
    m.k = 4;
    m.c[0] = x->a;
    m.c[1] = y->a;
    m.c[2] = x->b;
    m.c[3] = y->b;
    m.nx[0] = 2;
    m.nx[2] = 0;
    m.nx[1] = 3;
    m.nx[3] = 1;
    m.est = x->e + y->e;
    m.ux = m.uy = m.ux2 = m.uy2 = -2;
    m.lg = o3_islong(&m);
    m.tp = 1;
    if (m.lg && m.est <= o3q_lbar(o->slack) && !o3check)
        return;
    if (o3q_skip(&m))
        return;
    if (o32pv && m.lg)
        for (int q = 0, n_ = 0; q < 2; q++) { /* the joins that are not listed: valued later */
            const O3X *p = q ? y : x;
            if (!p->u)
                continue;
            int jx = p->u == 1 ? p->a : p->b, jy = (p->u == 1 ? p->b : p->a) + 1;
            if (!n_++) {
                m.ux = jx;
                m.uy = jy;
            } else {
                m.ux2 = jx;
                m.uy2 = jy;
            }
        }
    if (!o3_order(&m, o->N, &P))
        DIE("internal error: segment insertion (two pairs)");
    o3_push(o, &m);
}
/* the pairs of the join after a (and of the first place for a = -1) with their values, one after the other */
#define O3XGEN(a, EMIT)                                                                                         \
    do {                                                                                                        \
        if ((a) < 0) {                                                                                          \
            for (i64 b_ = 0; b_ < N - 1; b_++) {                                                                \
                int v_ = o3_look(o, b_, 0);                                                                     \
                EMIT(-1, b_, o3_old(o, b_) - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0);                                \
            }                                                                                                   \
        } /* b + 1 becomes the first event */                                                                   \
        else {                                                                                                  \
            for (i64 f_ = out->off[a]; f_ < out->off[(a) + 1]; f_++) {                                          \
                i64 b_ = (i64)out->to[f_] - 1;                                                                  \
                if (b_ > (a)) {                                                                                 \
                    int v_ = o3_look(o, b_, (a) + 1);                                                           \
                    EMIT(a, b_, o3_old(o, a) + o3_old(o, b_) - out->c[f_] - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0); \
                }                                                                                               \
            }                                                                                                   \
            {                                                                                                   \
                int v_ = o3_look(o, N - 1, (a) + 1);                                                            \
                EMIT(a, N - 1, o3_old(o, a) - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0);                               \
            } /* a becomes the last event */                                                                    \
            for (i64 f_ = in->off[(a) + 1]; f_ < in->off[(a) + 2]; f_++) {                                      \
                i64 b_ = in->to[f_];                                                                            \
                if (b_ > (a) && b_ < N - 1 && o3_look(o, a, b_ + 1) < 0)                                        \
                    EMIT(a, b_, o3_old(o, a) + o3_old(o, b_) - U - in->c[f_], 1);                               \
            }                                                                                                   \
        }                                                                                                       \
    } while (0)
/* The moves with two crossing pairs of joins (A D C B E), which the chain search cannot find (see the comment
   above the type O3X). */
static void o3_cross(O3 *o) {
    i64 N = o->N, n = 0, ng = 0;
    int emax = -1000, U = o->th + 1, sl = o->slack;
    const JG *out = &o->out, *in = &o->in;
    O3X *X = NULL, *Y;
/* the best value first, then only the pairs that can be part of a candidate with it */
#pragma omp parallel for schedule(dynamic, 256) num_threads(NTHR) reduction(max : emax)
    for (i64 a = -1; a < N - 1; a++) {
#define O3EM(A, B, E, W)   \
    do {                   \
        int e_ = (int)(E); \
        if (e_ > emax)     \
            emax = e_;     \
    } while (0)
        O3XGEN(a, O3EM);
#undef O3EM
    }
#pragma omp parallel num_threads(NTHR)
    {
        O3X *L = NULL;
        i64 ln = 0, lcap = 0;
#pragma omp for schedule(dynamic, 256) nowait
        for (i64 a = -1; a < N - 1; a++) {
#define O3EM(A, B, E, W)                                    \
    do {                                                    \
        int e_ = (int)(E);                                  \
        if (e_ + emax > -sl) {                              \
            if (ln == lcap) {                               \
                lcap = lcap ? lcap * 2 : 1024;              \
                L = realloc(L, (size_t)lcap * sizeof(O3X)); \
                if (!L)                                     \
                    DIE("out of memory");                   \
            }                                               \
            L[ln].a = (int)(A);                             \
            L[ln].b = (int)(B);                             \
            L[ln].e = e_;                                   \
            L[ln].u = (W);                                  \
            ln++;                                           \
        }                                                   \
    } while (0)
            O3XGEN(a, O3EM);
#undef O3EM
        }
#pragma omp critical(o3x)
        {
            X = realloc(X, (size_t)(n + ln + 1) * sizeof(O3X));
            if (!X)
                DIE("out of memory");
            if (ln)
                memcpy(X + n, L, (size_t)ln * sizeof(O3X));
            n += ln;
        }
        free(L);
    }
    Y = malloc((size_t)(n + 1) * sizeof(O3X));
    if (!Y)
        DIE("out of memory");
    memcpy(Y, X, (size_t)n * sizeof(O3X));
    qsort(X, (size_t)n, sizeof(O3X), o3xa_cmp);
    qsort(Y, (size_t)n, sizeof(O3X), o3xb_cmp);
    while (ng < n && 2 * X[ng].e > -sl)
        ng++; /* X is sorted by falling e: these stand first */
#pragma omp parallel num_threads(NTHR)
    {
        O3 t = *o;
        i64 nt = 0;
        t.sv = NULL;
        t.sn = t.scap = 0;
#pragma omp for schedule(dynamic, 8) nowait
        for (i64 i = 0; i < ng; i++) {
            const O3X *g = &X[i];
            for (i64 s = 0; s < n && g->e + X[s].e > -sl;) { /* one group of equal e after the other */
                i64 e1 = s, lo, hi;
                int e = X[s].e;
                {
                    i64 a = s, z = n;
                    while (a < z) {
                        i64 mid = (a + z) >> 1;
                        if (X[mid].e == e)
                            a = mid + 1;
                        else
                            z = mid;
                    }
                    e1 = a;
                }
                lo = s;
                hi = e1;
                while (lo < hi) {
                    i64 mid = (lo + hi) >> 1;
                    if (X[mid].a <= g->a)
                        lo = mid + 1;
                    else
                        hi = mid;
                }
                for (i64 j = lo; j < e1 && X[j].a < g->b; j++) {
                    nt++;
                    if (X[j].b > g->b)
                        o3_cross4(&t, g, &X[j]);
                }
                lo = s;
                hi = e1;
                while (lo < hi) {
                    i64 mid = (lo + hi) >> 1;
                    if (Y[mid].b <= g->a)
                        lo = mid + 1;
                    else
                        hi = mid;
                }
                for (i64 j = lo; j < e1 && Y[j].b < g->b; j++) {
                    nt++;
                    if (Y[j].a < g->a)
                        o3_cross4(&t, &Y[j], g);
                }
                s = e1;
            }
        }
#pragma omp critical(o3x2)
        {
            if (o->sn + t.sn > o->scap) {
                o->scap = o->sn + t.sn + (o->sn + t.sn) / 4 + 1024;
                o->sv = realloc(o->sv, (size_t)o->scap * sizeof(O3S));
                if (!o->sv)
                    DIE("out of memory");
            }
            if (t.sn)
                memcpy(o->sv + o->sn, t.sv, (size_t)t.sn * sizeof(O3S));
            o->sn += t.sn;
            o->ntried += nt;
        }
        free(t.sv);
    }
    o->nnode[O3KM + 1] = ng;
    free(X);
    free(Y);
}
#undef O3XGEN
/* the chains from every first cut, on all threads (each with its own list of moves and its share of the step limit) */
static void o3_scan(O3 *o) {
    int over = 0;
    i64 tot = 0;
    for (int d = 0; d <= O3KM + 1; d++)
        o->nnode[d] = 0;
#pragma omp parallel num_threads(NTHR)
    {
        O3 t = *o;
        int r[O3KM + 1];
        t.sv = NULL;
        t.sn = t.scap = t.ntried = 0;
        t.budget = o->budget / omp_get_num_threads();
        memset(t.nnode, 0, sizeof t.nnode);
        const JG *in = &o->in;
        t.cl = malloc((size_t)o->N + 2);
        if (!t.cl)
            DIE("out of memory");
        memset(t.cl, 255, (size_t)o->N + 2);
#pragma omp for schedule(dynamic, 64) nowait
        for (i64 a = -1; a < o->N; a++) {
            if (o->dstart && !o->dstart[a + 1])
                continue;
            r[0] = (int)a;
            int g = o3_old(&t, a);
            if (g <= -t.slack)
                continue;
            if (o3old) {
                o3_dfs0(&t, r, 0, g);
                continue;
            }
            i64 y0 = a + 1, f0 = y0 < o->N ? in->off[y0] : 0, f1 = y0 < o->N ? in->off[y0 + 1] : 0;
            for (i64 f = f0; f < f1; f++)
                t.cl[in->to[f] + 1] = in->c[f];
            o3_dfs(&t, r, 0, g);
            for (i64 f = f0; f < f1; f++)
                t.cl[in->to[f] + 1] = 255;
        }
#pragma omp critical(o3scan)
        {
            tot += t.sn;
            o->ntried += t.ntried;
            if (t.ntried > t.budget)
                over = 1;
            for (int d = 0; d <= O3KM; d++)
                o->nnode[d] += t.nnode[d];
        }
#pragma omp barrier
#pragma omp single
        {
            o->scap = o->sn + tot + 1;
            o->sv = realloc(o->sv, (size_t)o->scap * sizeof(O3S));
            if (!o->sv)
                DIE("out of memory");
        }
#pragma omp critical(o3scan)
        {
            if (t.sn)
                memcpy(o->sv + o->sn, t.sv, (size_t)t.sn * sizeof(O3S));
            o->sn += t.sn;
        }
        free(t.sv);
        free(t.cl);
    }
    if (over)
        o->ntried = o->budget + 1;
    if (o->kc >= 4)
        o3_cross(o);
}
/* the search for candidates (o3_scan) with --or3-eq-keep: see the comment at o3q_eq */
static void o3q_scan(O3 *o) {
    int thin = o3q_eq > 0 && o3q_keep > 0 && !o3old;
    double t0 = wall();
    i64 cnt0 = -1;
    o3q_div = 1;
    if (thin) {
        if (o3q_seen < 0) { /* the first round of a pass: once only to count */
            memset(o3q_z0, 0, sizeof o3q_z0);
            o3q_cnt = 1;
            o3_scan(o);
            o3q_cnt = 0;
            o3q_seen = 0;
            for (int t = 0; t < 256; t++)
                o3q_seen += o3q_z0[t][0];
            free(o->sv);
            o->sv = NULL;
            o->sn = o->scap = 0;
            o->ntried = 0;
            cnt0 = o3q_seen;
        }
        o3q_div = (u64)((o3q_seen + o3q_keep - 1) / o3q_keep);
        if (o3q_div < 1)
            o3q_div = 1;
        o3q_salt = hmix(((u64)o->round << 32) ^ o3q_seedv ^ 0x5851F42D4C957F2DULL);
    }
    double t1 = wall();
    memset(o3q_z0, 0, sizeof o3q_z0);
    o3_scan(o);
    o3q_seen = 0;
    for (int t = 0; t < 256; t++)
        o3q_seen += o3q_z0[t][0];
    if (thin && !o->quiet) {
        printf("segment insertion: %lld moves with estimate 0 found, one in %llu kept (--or3-eq-keep %lld)", o3q_seen,
               (unsigned long long)o3q_div, o3q_keep);
        if (cnt0 >= 0)
            printf("; counted first: %lld (%.1fs)", cnt0, t1 - t0);
        printf("\n");
        fflush(stdout);
    }
}
/* Prints a move: its cuts, the lengths of its blocks and the V of its old and new joins. */
static void o3_print(const O3 *o, const O3M *m, i64 N) {
    O3P P;
    o3_order(m, N, &P);
    printf("cuts after");
    for (int i = 0; i < m->k; i++)
        printf(" %d", m->c[i]);
    printf(", stretches of");
    for (int j = 0; j < P.ns; j++)
        printf(" %lld", P.len[j]);
    printf(" events");
    if (o) {
        printf(", V of the new joins");
        for (int i = 0; i < m->k; i++) {
            i64 x = m->c[i], y = (i64)m->c[m->nx[i]] + 1;
            int v = x < 0 || y >= N ? 0 : o3_look(o, x, y);
            if (v < 0)
                printf(" -");
            else
                printf(" %d", v);
        }
        printf(" for");
        for (int i = 0; i < m->k; i++)
            printf(" %d", o3_old(o, m->c[i]));
    }
}
/* The exact gain of a move.  The stretch before the first cut stays as it is (its costs are fw).  From each new join
   on, the dynamic programme of co_run is run through the stretch that follows, but only until the costs of an
   event's cuts are again what they were (relative to their minimum, and h standing for h or more): the rest
   of the stretch is then as before and its old costs are taken.  The last stretch needs its first event only:
   bw says what follows.  With fwd the last stretch is treated like the others: then nothing here looks ahead,
   and two moves do not disturb each other when neither changes what the other one has read (see o3_place).
   Many candidates share a new join x -> y; when the stretch that ends with x has its old costs
   at x, what follows y does not depend on the candidate and is kept (O3Memo, shared by the threads: where the old
   costs are back and the cost up to there; for a last stretch its cost).  T0, T1: two tables for the largest
   event.  st: layers computed, most layers after one join, joins computed, joins taken from the memo.
   The move gets its zones: for the j-th new join, zl[j] .. zh[j] are the events whose costs were computed again.
   O3BAD: given up (--or3-maxlay: more than that many layers after one join) or not judged. */
#define O3BAD (-(1LL << 40))
/* Looks up what follows a new join x -> y when the block before x has its old costs (shared by the threads). */
static int o3_memo_get(O3Memo *M, u64 key, i64 *zr, i64 *cum) {
    int f = 0;
#pragma omp critical(o3memo)
    if (M->t) {
        u64 i = hmix(key) & M->mask;
        while (M->t[i].key != ~0ULL) {
            if (M->t[i].key == key) {
                *zr = M->t[i].zr;
                *cum = M->t[i].cum;
                f = 1;
                break;
            }
            i = (i + 1) & M->mask;
        }
    }
    return f;
}
/* Stores that; the table doubles when it is half full. */
static void o3_memo_put(O3Memo *M, u64 key, i64 zr, i64 cum) {
#pragma omp critical(o3memo)
    {
        if (!M->t || 2 * (u64)(M->n + 1) > M->mask + 1) {
            O3C *old = M->t;
            u64 om = M->mask;
            M->mask = old ? 2 * om + 1 : (1 << 12) - 1;
            M->t = malloc((size_t)(M->mask + 1) * sizeof(O3C));
            if (!M->t)
                DIE("out of memory");
            for (u64 z = 0; z <= M->mask; z++)
                M->t[z].key = ~0ULL;
            if (old)
                for (u64 z = 0; z <= om; z++)
                    if (old[z].key != ~0ULL) {
                        u64 q = hmix(old[z].key) & M->mask;
                        while (M->t[q].key != ~0ULL)
                            q = (q + 1) & M->mask;
                        M->t[q] = old[z];
                    }
            free(old);
        }
        u64 i = hmix(key) & M->mask;
        while (M->t[i].key != ~0ULL && M->t[i].key != key)
            i = (i + 1) & M->mask;
        if (M->t[i].key == ~0ULL)
            M->n++;
        M->t[i].key = key;
        M->t[i].zr = zr;
        M->t[i].cum = cum;
    }
}
/* Exact gain of move m: the best cuts of the whole new sequence, computed block by block as described in
   the comment above.  Fills the zones of the move.  O3BAD: given up. */
static i64 o3_gain(BS *b, const POT *P, i64 N, O3M *m, unsigned char *T0, unsigned char *T1, O3Memo *M, i64 *st,
                   int fwd) {
    O3P R;
    BScr *w = &b->scr[0];
    i64 bnd[18], tot = 0, pe = -1, zr, mc;
    const unsigned char *pt = NULL;
    unsigned char *T = T0;
    int nz = 0;
    if (!o3_order(m, N, &R))
        DIE("internal error: segment insertion (order)");
    for (int j = 0; j < O3KM; j++) {
        m->zx[j] = m->zl[j] = 0;
        m->zh[j] = -1;
    }
    for (int j = 0; j < R.ns; j++) {
        i64 lo = R.lo[j], hi = lo + R.len[j] - 1;
        if (hi < lo)
            continue;
        if (!j) {
            tot = P->fmin[hi];
            pt = P->fw + P->off[hi];
            pe = hi;
            continue;
        }
        int clean = pe >= 0 && pt == P->fw + P->off[pe], last = !fwd && j == R.ns - 1 && pe >= 0,
            zi = nz < O3KM ? nz++ : O3KM - 1;
        u64 key = ((u64)last << 62) | ((u64)(pe + 1) << 24) | (u64)lo;
        m->zx[zi] = (int)pe;
        m->zl[zi] = (int)lo;
        m->zh[zi] = (int)lo;
        if (clean && o3_memo_get(M, key, &zr, &mc)) {
            if (last) {
                st[3]++;
                return P->fmin[N - 1] - (tot + mc + P->gmin[lo]);
            }
            if (zr <= hi) {
                st[3]++;
                m->zh[zi] = (int)zr;
                tot += mc + P->fmin[hi] - P->fmin[zr];
                pt = P->fw + P->off[hi];
                pe = hi;
                continue;
            }
        }
        st[2]++;
        if (last) {
            {
                BEv *x = bs_ev(b, pe);
                o3_pool1(w, pt, x->E, x->m, bnd);
            }
            BEv *e = bs_ev(b, lo);
            int mm = e->m, mn = 1 << 20;
            const unsigned char *bw = P->bw + P->off[lo];
            if (mm > w->mcap) {
                w->mcap = mm + mm / 2 + 64;
                free(w->mv);
                w->mv = malloc((size_t)w->mcap * sizeof(int));
                if (!w->mv)
                    DIE("out of memory");
            }
            int *mv = w->mv;
            for (int q = 0; q < mm; q++)
                mv[q] = h;
            bs_join(w, bnd, &e, 1, mv, 0);
            for (int q = 0; q < mm; q++)
                if (mv[q] + bw[q] < mn)
                    mn = mv[q] + bw[q];
            st[0]++;
            if (clean)
                o3_memo_put(M, key, lo, mn);
            return P->fmin[N - 1] - (tot + mn + P->gmin[lo]);
        }
        i64 cum = 0, nl = 0;
        for (i64 z = lo;; z++) {
            if (pe >= 0) {
                BEv *x = bs_ev(b, pe);
                o3_pool1(w, pt, x->E, x->m, bnd);
            }
            BEv *e = bs_ev(b, z);
            int mm = e->m, mn = 1 << 20;
            if (mm > w->mcap) {
                w->mcap = mm + mm / 2 + 64;
                free(w->mv);
                w->mv = malloc((size_t)w->mcap * sizeof(int));
                if (!w->mv)
                    DIE("out of memory");
            }
            int *mv = w->mv;
            for (int q = 0; q < mm; q++)
                mv[q] = pe >= 0 ? h : 0;
            if (pe >= 0)
                bs_join(w, bnd, &e, 1, mv, 0);
            for (int q = 0; q < mm; q++) {
                mv[q] += e->D[q];
                if (mv[q] < mn)
                    mn = mv[q];
            }
            for (int q = 0; q < mm; q++)
                T[q] = (unsigned char)(mv[q] - mn < h ? mv[q] - mn : h);
            tot += mn;
            cum += mn;
            st[0]++;
            nl++;
            m->zh[zi] = (int)z;
            if (!memcmp(T, P->fw + P->off[z], (size_t)mm)) {
                if (clean)
                    o3_memo_put(M, key, z, cum);
                tot += P->fmin[hi] - P->fmin[z];
                pt = P->fw + P->off[hi];
                pe = hi;
                break;
            }
            pt = T;
            pe = z;
            T = T == T0 ? T1 : T0;
            if (z == hi)
                break;
            if (nl >= (o3maxlay > 0 ? o3maxlay : o3maxlay < 0 && !o3old ? 4096 : N + 1)) {
                if (nl > st[1])
                    st[1] = nl;
                return O3BAD;
            }
        }
        if (nl > st[1])
            st[1] = nl;
    }
    return P->fmin[N - 1] - tot;
}
/* ==================== own part of this file, 2: judging on the card (--or3-gpu) ==================== */
/* ---------- segment insertion on the card (--or3-gpu).  The candidates are judged by the kernel or_judge (segins_kern.cu,
   compiled to segins_kern.ptx; loaded through the CUDA driver library that comes with the display driver, nothing else
   is linked): one thread block per candidate does what o3_gain does, layer by layer, with the same hash tables.
   On the card, once: start word, end word and cost of every cut (11 bytes each), in the order of OP.  Every
   round: fw and bw of every cut in that order (255: an cut the event may not take), the first cut and
   the number of cuts of every event, fmin and gmin; an event with one cut only gets a slot behind the last
   cut.  Every call: the candidates (their stretches) and room for their gains and zones.
   A launch ends when every block has spent its budget of cut-layers; the blocks write down where they are and
   the next launch goes on from there.  The budget follows the time a launch took (--or3-gpu-ms, default 100 ms), so
   the card is never held for long by one launch whatever a candidate costs.
   The memo of o3_gain has its counterpart on the card (a hash table of the round, shared by the blocks; two blocks
   that meet the same join at the same time both compute it, so a few more joins are computed than on the host;
   --or3-gpu-nomemo: none).  The values of the closing joins that are not listed (o3_exactv) are jobs of the same
   kernel.  The gains, zones and values are the same as on the host (--or3-gpu-check computes everything on both and
   compares; the host's results are then the ones used).
   Blocks: 1024 GPU threads each, and half as many blocks as the card can hold at once (the work is bound by memory
   traffic: more blocks are slower; --or3-gpu-bt, --or3-gpu-blocks).
   Everything else of a round (tables, pairs, the chain search, taking the moves) stays on the host. */
#if defined(_WIN32)
#define OGAPI __stdcall
__declspec(dllimport) void *__stdcall LoadLibraryA(const char *);
__declspec(dllimport) void *__stdcall GetProcAddress(void *, const char *);
static void *og_lib_open(void) {
    return LoadLibraryA("nvcuda.dll");
}
static void *og_lib_sym(void *l, const char *s) {
    return GetProcAddress(l, s);
}
#else
#include <dlfcn.h>
#define OGAPI
static void *og_lib_open(void) {
    return dlopen("libcuda.so.1", RTLD_NOW);
}
static void *og_lib_sym(void *l, const char *s) {
    return dlsym(l, s);
}
#endif
typedef u64 OGP; /* CUdeviceptr */
static int(OGAPI *ogInit)(unsigned), (OGAPI * ogDeviceGet)(int *, int), (OGAPI * ogDeviceGetName)(char *, int, int),
    (OGAPI * ogCtxCreate)(void **, unsigned, int), (OGAPI * ogCtxDestroy)(void *);
static int(OGAPI *ogModuleLoadData)(void **, const void *),
    (OGAPI * ogModuleGetFunction)(void **, void *, const char *);
static int(OGAPI *ogMemAlloc)(OGP *, size_t), (OGAPI * ogMemFree)(OGP),
    (OGAPI * ogMemsetD8)(OGP, unsigned char, size_t), (OGAPI * ogMemGetInfo)(size_t *, size_t *);
static int(OGAPI *ogHtoD)(OGP, const void *, size_t), (OGAPI * ogDtoH)(void *, OGP, size_t), (OGAPI * ogCtxSync)(void);
static int(OGAPI *ogLaunch)(void *, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, unsigned, void *,
                            void **, void **);
static int(OGAPI *ogOcc)(int *, void *, int, size_t), (OGAPI * ogDevAttr)(int *, int, int);
#define OGCK(x)                                                   \
    do {                                                          \
        int e_ = (x);                                             \
        if (e_)                                                   \
            DIE("CUDA driver error %d at line %d", e_, __LINE__); \
    } while (0)
/* as struct OG in segins_kern.cu */
typedef struct {
    OGP oS, oE, oSh, oEh, oD, fw, bw, evb, evm, fmin, gmin, cand, out, ht, scr, gen, ctl, sav, memo;
    i64 N, ncand, htslots, scrsz, maxlay, budget, memomask;
    int h, fwd;
    OGP stat;
    int small, epoch;
} OGDev;
enum { OG_SAVW = 64, OG_CW = 16, OG_OW = 12, OG_UPCH = 1 << 22, OG_VCH = 1 << 18 };
static struct {
    int on, check, bt, ready, failed, nbmax, nb, round_ok, nbuser, nomemo, memo_clear, verbose;
    double ms, memmb;
    const char *ptx;
    void *ctx, *fn;
    OGDev d;
    i64 xcap, nx, candcap,
        nbal; /* slots for events with one cut, used; candidates that fit; blocks that have scratch memory */
    unsigned char *hfw, *hbw, *hxf, *hxb;
    i64 upcap, memocap;
    u64 *hevb;
    u32 *hevm, *hxs, *hxe;
    unsigned char *hxsh, *hxeh;
    int *hcand;
    i64 *hout, hcap;
    O3M *hchk;
    i64 chkcap;
    double budget, t_init, t_round, t_judge, t_kern, t_chk, t_val, devmb, rtab, rval;
    i64 nval, nvchk, nvbad;
    i64 ncalls, njud, nlaunch, nlay, njoin, nmemo, nchk, nbad, rj, rl, rlay, rjoin, rmemo;
    double rt, rk;
    int stats, small, chunk, nozones;
    unsigned epoch;
    double fixbudget, t_up, t_launch, t_ctl, t_down, t_prep,
        t_post; /* --or3-gpu-budget; seconds of the host side of the calls */
} og = {.bt = 1024, .ms = 100, .memmb = 3000, .budget = 300000, .small = 2048, .chunk = 1 << 18};
static void ogz_clear(void);
#define OG_NSTAT 512
#define OG_KERNEL "segins_kern.ptx"
static const char *og_argv0 = "";
/* is this call judged on the card?  (--or3-gpu-min M: calls with fewer candidates stay on the host) */
static int og_min = 1;
/* --or3-gpu-checkmax M: with --or3-gpu-check only the first M candidates of the pass and the first 10 M
   values of joins are computed on both; after that the card alone */
static i64 og_chkmax = 0;
static inline int og_use(i64 n) {
    return og.on && og.ready && !og.failed && og.round_ok && n >= og_min;
}
/* candidates per call of o3_judge in a round (between calls the time limit is looked at) */
static inline i64 og_chunk(void) {
    return og.on && og.ready && !og.failed && og.round_ok ? (og.chunk > 256 ? og.chunk : 256) : 256;
}

/* the driver, the kernel, and the cuts; 0 (with the reason): the candidates are judged on the host */
static int og_init(const char *argv0, i64 N) {
    double t0 = wall();
    void *lib = og_lib_open();
    if (!lib) {
        printf("or3-gpu: the CUDA driver library was not found; judging on the CPU\n");
        return 0;
    }
    const char *miss = NULL;
#define OGSYM(v, name)                        \
    do {                                      \
        *(void **)&v = og_lib_sym(lib, name); \
        if (!v)                               \
            miss = name;                      \
    } while (0)
    OGSYM(ogInit, "cuInit");
    OGSYM(ogDeviceGet, "cuDeviceGet");
    OGSYM(ogDeviceGetName, "cuDeviceGetName");
    OGSYM(ogCtxCreate, "cuCtxCreate_v2");
    OGSYM(ogCtxDestroy, "cuCtxDestroy_v2");
    OGSYM(ogModuleLoadData, "cuModuleLoadData");
    OGSYM(ogModuleGetFunction, "cuModuleGetFunction");
    OGSYM(ogMemAlloc, "cuMemAlloc_v2");
    OGSYM(ogMemFree, "cuMemFree_v2");
    OGSYM(ogMemsetD8, "cuMemsetD8_v2");
    OGSYM(ogMemGetInfo, "cuMemGetInfo_v2");
    OGSYM(ogHtoD, "cuMemcpyHtoD_v2");
    OGSYM(ogDtoH, "cuMemcpyDtoH_v2");
    OGSYM(ogCtxSync, "cuCtxSynchronize");
    OGSYM(ogLaunch, "cuLaunchKernel");
    OGSYM(ogOcc, "cuOccupancyMaxActiveBlocksPerMultiprocessor");
    OGSYM(ogDevAttr, "cuDeviceGetAttribute");
#undef OGSYM
    if (miss) {
        printf("or3-gpu: %s is missing in the CUDA driver library; judging on the CPU\n", miss);
        return 0;
    }
    char path[4096];
    FILE *pf = NULL; /* --or3-gpu-ptx FILE, or segins_kern.ptx next to the program, or in the current directory */
    if (og.ptx)
        pf = fopen(og.ptx, "rb");
    else {
        const char *sl = strrchr(argv0, '/'), *bs = strrchr(argv0, '\\');
        if (bs > sl)
            sl = bs;
        if (sl) {
            snprintf(path, sizeof path, "%.*s/" OG_KERNEL, (int)(sl - argv0), argv0);
            pf = fopen(path, "rb");
        }
        if (!pf)
            pf = fopen(OG_KERNEL, "rb");
    }
    if (!pf) {
        printf("or3-gpu: the kernel file %s was not found; judging on the CPU\n", og.ptx ? og.ptx : OG_KERNEL);
        return 0;
    }
    fseek(pf, 0, SEEK_END);
    long psz = ftell(pf);
    fseek(pf, 0, SEEK_SET);
    char *ptx = calloc((size_t)psz + 1, 1);
    if (!ptx || fread(ptx, 1, (size_t)psz, pf) != (size_t)psz) {
        fclose(pf);
        printf("or3-gpu: cannot read the kernel file; judging on the CPU\n");
        return 0;
    }
    fclose(pf);
    int dev, e, occ = 0, sms = 0;
    void *mod;
    char name[128] = "";
    if ((e = ogInit(0)) || (e = ogDeviceGet(&dev, 0)) || (e = ogDeviceGetName(name, sizeof name, dev)) ||
        (e = ogCtxCreate(&og.ctx, 4, dev))) {
        printf("or3-gpu: no usable CUDA device (driver error %d); judging on the CPU\n", e);
        return 0;
    }
    if ((e = ogModuleLoadData(&mod, ptx)) || (e = ogModuleGetFunction(&og.fn, mod, "or_judge"))) {
        printf("or3-gpu: the kernel file was not accepted by the driver (error %d); judging on the CPU\n", e);
        ogCtxDestroy(og.ctx);
        return 0;
    }
    free(ptx);
    if (og.bt < 32 || og.bt > 1024)
        og.bt = 1024;
    if (ogOcc(&occ, og.fn, og.bt, 0) || ogDevAttr(&sms, 16, dev) || occ < 1 || sms < 1) {
        occ = 1;
        sms = 64;
    }
    og.nbmax = occ * sms;
    size_t fr0, fr1, tot;
    OGCK(ogMemGetInfo(&fr0, &tot));
    og.xcap = N + 64;
    size_t no = (size_t)(NO + og.xcap), need = no * 13 + (size_t)N * 28;
    if (need + (600ULL << 20) > fr0) {
        printf("or3-gpu: %.1f GB needed for the openings, %.1f GB free on the card; judging on the CPU\n", need / 1e9,
               fr0 / 1e9);
        ogCtxDestroy(og.ctx);
        return 0;
    }
    double t1 = wall();
    OGDev *d = &og.d;
    memset(d, 0, sizeof *d);
    OGCK(ogMemAlloc(&d->oS, no * 4));
    OGCK(ogMemAlloc(&d->oE, no * 4));
    OGCK(ogMemAlloc(&d->oSh, no));
    OGCK(ogMemAlloc(&d->oEh, no));
    OGCK(ogMemAlloc(&d->oD, no));
    OGCK(ogMemAlloc(&d->fw, no));
    OGCK(ogMemAlloc(&d->bw, no));
    OGCK(ogMemAlloc(&d->evb, (size_t)N * 8));
    OGCK(ogMemAlloc(&d->evm, (size_t)N * 4));
    OGCK(ogMemAlloc(&d->fmin, (size_t)N * 8));
    OGCK(ogMemAlloc(&d->gmin, (size_t)N * 8));
    OGCK(ogMemAlloc(&d->ctl, 64));
    OGCK(ogMemsetD8(d->oD + (size_t)NO, 0, (size_t)og.xcap));
    OGCK(ogMemAlloc(&d->stat, OG_NSTAT * 8));
    OGCK(ogMemsetD8(d->stat, 0, OG_NSTAT * 8));
    i64 CH = 1 << 22;
    u32 *bs = malloc((size_t)CH * 4), *be = malloc((size_t)CH * 4);
    unsigned char *bsh = malloc((size_t)CH), *beh = malloc((size_t)CH);
    signed char *bd = malloc((size_t)CH);
    if (!bs || !be || !bsh || !beh || !bd)
        DIE("out of memory");
    for (i64 o0 = 0; o0 < NO; o0 += CH) {
        i64 m = NO - o0 < CH ? NO - o0 : CH;
#pragma omp parallel num_threads(NTHR)
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
                bd[q] = (signed char)oD(o);
            }
        }
        OGCK(ogHtoD(d->oS + 4 * (u64)o0, bs, (size_t)m * 4));
        OGCK(ogHtoD(d->oE + 4 * (u64)o0, be, (size_t)m * 4));
        OGCK(ogHtoD(d->oSh + (u64)o0, bsh, (size_t)m));
        OGCK(ogHtoD(d->oEh + (u64)o0, beh, (size_t)m));
        OGCK(ogHtoD(d->oD + (u64)o0, bd, (size_t)m));
    }
    free(bs);
    free(be);
    free(bsh);
    free(beh);
    free(bd);
    og.hxf = malloc((size_t)og.xcap);
    og.hxb = malloc((size_t)og.xcap);
    og.hevb = malloc((size_t)N * 8);
    og.hevm = malloc((size_t)N * 4);
    og.hxs = malloc((size_t)og.xcap * 4);
    og.hxe = malloc((size_t)og.xcap * 4);
    og.hxsh = malloc((size_t)og.xcap);
    og.hxeh = malloc((size_t)og.xcap);
    if (!og.hxf || !og.hxb || !og.hevb || !og.hevm || !og.hxs || !og.hxe || !og.hxsh || !og.hxeh)
        DIE("out of memory");
    OGCK(ogMemGetInfo(&fr1, &tot));
    og.devmb = (fr0 - fr1) / 1e6;
    og.t_init = wall() - t0;
    d->N = N;
    d->h = h;
    printf(
        "or3-gpu: %s; driver and kernel ready in %.2fs, %lld openings loaded in %.2fs (%.0f MB on the card, %.1f of %.1f GB free); up to %d blocks of %d GPU threads, launches of about %.0f ms\n",
        name, t1 - t0, NO, wall() - t1, og.devmb, fr1 / 1e9, tot / 1e9, og.nbmax, og.bt, og.ms);
    fflush(stdout);
    return 1;
}
/* the tables of a round; called when fw and bw are ready */
static void og_round(O3 *o) {
    og.round_ok = 0;
    if (!og.on || og.failed)
        return;
    if (!og.ready) {
        if (h < 4 || h > 10 || !og_init(og_argv0, o->N)) {
            og.failed = 1;
            return;
        }
        og.ready = 1;
    }
    double t0 = wall();
    const POT *P = &o->P;
    const Ev *ev = o->ev;
    i64 N = o->N, nx = 0, maxm = 1, bad = 0;
    OGDev *d = &og.d;
    int *tev = malloc((size_t)(NT + 1) * sizeof(int));
    if (!tev)
        DIE("out of memory");
    for (i64 t = 0; t < NT; t++) {
        tev[t] = -1;
        if (t + 1 < NT && TR[t].ohi != TR[t + 1].olo)
            bad++;
    }
    for (i64 p = 0; p < N; p++) { /* the slots of the events with one cut, and no trail twice */
        const Ev *x = &ev[p];
        if (co_cur(x) < 0) {
            og.hevb[p] = (u64)(NO + nx);
            og.hevm[p] = 1;
            og.hxf[nx] = P->fw[P->off[p]];
            og.hxb[nx] = P->bw[P->off[p]];
            og.hxs[nx] = (u32)x->s;
            og.hxe[nx] = (u32)x->e;
            og.hxsh[nx] = (unsigned char)(x->s >> 32);
            og.hxeh[nx] = (unsigned char)(x->e >> 32);
            nx++;
        } else {
            if (tev[x->t] >= 0)
                bad++;
            tev[x->t] = (int)p;
            og.hevb[p] = (u64)TR[x->t].olo;
            og.hevm[p] = (u32)(TR[x->t].ohi - TR[x->t].olo);
            if ((i64)og.hevm[p] > maxm)
                maxm = og.hevm[p];
        }
    }
    /* fw and bw in the order of OP, a few million cuts at a time (no second copy of them on the host) */
    for (i64 ta = 0, tb; ta < NT && !bad; ta = tb) {
        i64 o0 = TR[ta].olo, cnt = 0;
        for (tb = ta; tb < NT && (tb == ta || TR[tb].ohi - o0 <= OG_UPCH); tb++)
            cnt = TR[tb].ohi - o0;
        if (cnt > og.upcap) {
            og.upcap = cnt + 4096;
            free(og.hfw);
            free(og.hbw);
            og.hfw = malloc((size_t)og.upcap);
            og.hbw = malloc((size_t)og.upcap);
            if (!og.hfw || !og.hbw)
                DIE("out of memory");
        }
        memset(og.hfw, 255, (size_t)cnt);
        memset(og.hbw, 255, (size_t)cnt);
#pragma omp parallel for schedule(dynamic, 64) num_threads(NTHR) reduction(+ : bad)
        for (i64 t = ta; t < tb; t++) {
            i64 p = tev[t];
            if (p < 0)
                continue;
            const Ev *x = &ev[p];
            const Trail *T = &TR[t];
            const unsigned char *fw = P->fw + P->off[p], *bw = P->bw + P->off[p];
            i64 j = 0, m = P->off[p + 1] - P->off[p];
            for (i64 q = T->olo; q < T->ohi; q++)
                if (!OP[q].g1 || oSK_t(T, q) == x->skip) {
                    if (j < m) {
                        og.hfw[q - o0] = fw[j];
                        og.hbw[q - o0] = bw[j];
                    }
                    j++;
                }
            if (j != m)
                bad++;
        }
        if (bad)
            break;
        OGCK(ogHtoD(d->fw + (u64)o0, og.hfw, (size_t)cnt));
        OGCK(ogHtoD(d->bw + (u64)o0, og.hbw, (size_t)cnt));
    }
    free(tev);
    og.round_ok = !bad;
    og.nx = nx;
    og.memo_clear = 1;
    ogz_clear();
    if (bad) {
        printf("or3-gpu: this sequence cannot be put on the card (%lld events); this round is judged on the CPU\n",
               bad);
        fflush(stdout);
        return;
    }
    OGCK(ogHtoD(d->evb, og.hevb, (size_t)N * 8));
    OGCK(ogHtoD(d->evm, og.hevm, (size_t)N * 4));
    OGCK(ogHtoD(d->fmin, P->fmin, (size_t)N * 8));
    OGCK(ogHtoD(d->gmin, P->gmin, (size_t)N * 8));
    if (nx) {
        OGCK(ogHtoD(d->oS + 4 * (u64)NO, og.hxs, (size_t)nx * 4));
        OGCK(ogHtoD(d->oE + 4 * (u64)NO, og.hxe, (size_t)nx * 4));
        OGCK(ogHtoD(d->oSh + (u64)NO, og.hxsh, (size_t)nx));
        OGCK(ogHtoD(d->oEh + (u64)NO, og.hxeh, (size_t)nx));
        OGCK(ogHtoD(d->fw + (u64)NO, og.hxf, (size_t)nx));
        OGCK(ogHtoD(d->bw + (u64)NO, og.hxb, (size_t)nx));
    }
    /* scratch memory of the blocks: three byte tables and a hash table of twice the largest event */
    i64 scrsz = (maxm + 4095) & ~4095LL, hts = 16;
    while (hts < 2 * maxm)
        hts <<= 1;
    i64 per = 3 * scrsz + 8 * hts + 4 + 4 * OG_SAVW, nb = og.nbuser > 0 ? og.nbuser : (og.nbmax + 1) / 2;
    if (nb * per > (i64)(og.memmb * 1e6))
        nb = (i64)(og.memmb * 1e6) / per;
    if (nb < 1)
        nb = 1;
    if (scrsz > d->scrsz || hts > d->htslots || nb > og.nbal) {
        if (d->ht) {
            OGCK(ogMemFree(d->ht));
            OGCK(ogMemFree(d->scr));
            OGCK(ogMemFree(d->gen));
            OGCK(ogMemFree(d->sav));
        }
        if (scrsz < d->scrsz)
            scrsz = d->scrsz;
        if (hts < d->htslots)
            hts = d->htslots;
        OGCK(ogMemAlloc(&d->ht, (size_t)nb * hts * 8));
        OGCK(ogMemAlloc(&d->scr, (size_t)nb * 3 * scrsz));
        OGCK(ogMemAlloc(&d->gen, (size_t)nb * 4));
        OGCK(ogMemAlloc(&d->sav, (size_t)nb * 4 * OG_SAVW));
        OGCK(ogMemsetD8(d->ht, 0, (size_t)nb * hts * 8));
        OGCK(ogMemsetD8(d->gen, 0, (size_t)nb * 4));
        d->scrsz = scrsz;
        d->htslots = hts;
        og.nbal = nb;
        size_t fr, tot;
        OGCK(ogMemGetInfo(&fr, &tot));
        printf(
            "or3-gpu: %lld blocks, each with %.2f MB of tables (largest event %lld openings); %.1f of %.1f GB free on the card\n",
            nb, per / 1e6, maxm, fr / 1e9, tot / 1e9);
        fflush(stdout);
    }
    og.nb = (int)(nb < og.nbal ? nb : og.nbal);
    og.t_round += wall() - t0;
    og.rj = og.rl = og.rlay = og.rjoin = og.rmemo = 0;
    og.rt = og.rk = og.rval = 0;
    og.rtab = wall() - t0;
}
/* room for the jobs of a call */
static void og_room(i64 n) {
    OGDev *d = &og.d;
    if (n <= og.hcap)
        return;
    og.hcap = n + n / 2 + 1024;
    free(og.hcand);
    free(og.hout);
    og.hcand = malloc((size_t)og.hcap * OG_CW * sizeof(int));
    og.hout = malloc((size_t)og.hcap * OG_OW * 8);
    if (!og.hcand || !og.hout)
        DIE("out of memory");
    if (d->cand) {
        OGCK(ogMemFree(d->cand));
        OGCK(ogMemFree(d->out));
    }
    OGCK(ogMemAlloc(&d->cand, (size_t)og.hcap * OG_CW * sizeof(int)));
    OGCK(ogMemAlloc(&d->out, (size_t)og.hcap * OG_OW * 8));
}
/* the n jobs of og.hcand: launches until all are done; their results are then in og.hout.  The budget of a launch
   (cut-layers per block) follows the time the launches take: down at once, up slowly. */
static void og_run(i64 n) {
    OGDev *d = &og.d;
    u32 ctl[3] = {0, 0, 0};
    int gb = (int)(n < og.nb ? n : og.nb);
    double ta = wall();
    OGCK(ogHtoD(d->cand, og.hcand, (size_t)n * OG_CW * sizeof(int)));
    OGCK(ogHtoD(d->ctl, ctl, sizeof ctl));
    OGCK(ogMemsetD8(d->sav, 0, (size_t)gb * 4 * OG_SAVW));
    d->ncand = n;
    og.t_up += wall() - ta;
    for (i64 guard = 0; ctl[1] < (u32)n; guard++) {
        void *args[1] = {d};
        double t1 = wall();
        u32 done0 = ctl[1];
        d->budget = (i64)(og.fixbudget > 0 ? og.fixbudget : og.budget);
        if (d->budget < 1)
            d->budget = 1;
        d->small = og.small;
        d->epoch = (int)(++og.epoch ? og.epoch : ++og.epoch);
        OGCK(ogLaunch(og.fn, (unsigned)gb, 1, 1, (unsigned)og.bt, 1, 1, 0, NULL, args, NULL));
        OGCK(ogCtxSync());
        double t2 = wall();
        OGCK(ogDtoH(ctl, d->ctl, 8));
        double dt = wall() - t1;
        og.t_kern += dt;
        og.rk += dt;
        og.nlaunch++;
        og.rl++;
        og.t_launch += t2 - t1;
        og.t_ctl += dt - (t2 - t1);
        if (og.verbose) {
            printf("or3-gpu: launch %lld: %d blocks, budget %lld, %.1f ms, %u of %lld done\n", guard, gb, d->budget,
                   dt * 1e3, ctl[1], n);
            fflush(stdout);
        }
        if (ctl[1] < (u32)n) { /* the launch ran out of budget: aim at og.ms */
            double f = og.ms * 1e-3 / (dt > 1e-5 ? dt : 1e-5);
            if (f > 1.25)
                f = 1.25;
            if (f < 0.25)
                f = 0.25;
            og.budget *= f;
            if (og.budget < 1000)
                og.budget = 1000;
            if (og.budget > 4e12)
                og.budget = 4e12;
        }
        if (ctl[1] == done0 && guard > 1000000)
            DIE("or3-gpu: the kernel makes no progress");
    }
    ta = wall();
    OGCK(ogDtoH(og.hout, d->out, (size_t)n * OG_OW * 8));
    og.t_down += wall() - ta;
}
/* the values of the closing joins that are not listed (o3_exactv for every key of pk) on the card */
static void og_values(O3 *o, const u64 *pk, i64 n, unsigned char *pv) {
    double t0 = wall();
    OGDev *d = &og.d;
    for (i64 a = 0; a < n; a += OG_VCH) { /* a quarter of a million at a time: there may be millions of them */
        i64 m = n - a < OG_VCH ? n - a : OG_VCH;
        og_room(m);
        memset(og.hcand, 0, (size_t)m * OG_CW * sizeof(int));
        for (i64 q = 0; q < m; q++) {
            og.hcand[q * OG_CW + 1] = (int)(pk[a + q] >> 24) - 1;
            og.hcand[q * OG_CW + 2] = (int)(pk[a + q] & 0xFFFFFF);
        }
        d->memomask = 0;
        d->fwd = 0;
        d->maxlay = 1;
        og_run(m);
        for (i64 q = 0; q < m; q++)
            pv[a + q] = (unsigned char)og.hout[q * OG_OW];
    }
    og.nval += n;
    og.t_val += wall() - t0;
    og.rval = wall() - t0;
    i64 nc = !og.check ? 0 : og_chkmax <= 0 || 10 * og_chkmax - og.nvchk >= n ? n : 10 * og_chkmax - og.nvchk;
    if (nc > 0) {
        i64 nbad = 0;
#pragma omp parallel for schedule(dynamic, 16) num_threads(NTHR) reduction(+ : nbad)
        for (i64 q = 0; q < nc; q++) {
            int v = o3_exactv(&o->tc[omp_get_thread_num()].b, &o->P, (i64)(pk[q] >> 24) - 1, (i64)(pk[q] & 0xFFFFFF));
            if (v != pv[q]) {
                nbad++;
                pv[q] = (unsigned char)v;
            }
        }
        og.nvchk += nc;
        og.nvbad += nbad;
        if (nbad) {
            printf("or3-gpu-check: %lld of %lld values of joins differ (MISMATCH)\n", nbad, nc);
            fflush(stdout);
        }
    }
}
/* Candidates judged with their zones ahead of time (see og_judge_zones): what the card said about each, kept until
   the selection loop asks for it, so that the counters of the round are those of the candidates it did ask for. */
typedef struct {
    i64 idx;
    u32 lay, mxl, joins, memo;
} OGZ;
static struct {
    OGZ *t;
    i64 mask, n, look, hits, made, ncall, nahead, nused;
} ogz = {.look = 64};
/* The record of candidate idx among those judged ahead with their zones.  add: make one if there is none. */
static OGZ *ogz_find(i64 idx, int add) {
    if (!ogz.t) {
        if (!add)
            return NULL;
        ogz.mask = (1 << 14) - 1;
        ogz.t = calloc((size_t)ogz.mask + 1, sizeof(OGZ));
        if (!ogz.t)
            DIE("out of memory");
    }
    if (add && 2 * (ogz.n + 1) > ogz.mask + 1) {
        OGZ *old = ogz.t;
        i64 om = ogz.mask;
        ogz.mask = 2 * om + 1;
        ogz.t = calloc((size_t)ogz.mask + 1, sizeof(OGZ));
        if (!ogz.t)
            DIE("out of memory");
        for (i64 q = 0; q <= om; q++)
            if (old[q].idx) {
                u64 i = hmix((u64)old[q].idx) & (u64)ogz.mask;
                while (ogz.t[i].idx)
                    i = (i + 1) & (u64)ogz.mask;
                ogz.t[i] = old[q];
            }
        free(old);
    }
    u64 i = hmix((u64)(idx + 1)) & (u64)ogz.mask;
    while (ogz.t[i].idx) {
        if (ogz.t[i].idx == idx + 1)
            return &ogz.t[i];
        i = (i + 1) & (u64)ogz.mask;
    }
    if (!add)
        return NULL;
    ogz.t[i].idx = idx + 1;
    ogz.n++;
    return &ogz.t[i];
}
static void ogz_clear(void) {
    if (ogz.t && ogz.n)
        memset(ogz.t, 0, (size_t)(ogz.mask + 1) * sizeof(OGZ));
    ogz.n = 0;
}
static void o3_judge(O3 *o, const i64 *idx, i64 n, int fwd);
static int o3_place(char *mark, const O3M *m, i64 N, int mg, int what, int judged);
static void og_judge2(O3 *o, const i64 *idx, i64 n, int fwd, int stash);
/* o3_judge on the card */
static void og_judge(O3 *o, const i64 *idx, i64 n, int fwd) {
    og_judge2(o, idx, n, fwd, 0);
}
/* The selection loop judges the shorter candidates once more with their zones (fwd), a few at a time (batch), in the
   order ord[from ..]; every such call would be a launch of its own that lasts as long as its slowest candidate.
   Here the card gets, together with the candidates asked for, those the loop will come to next (not taken, not next
   to a move taken so far): their gains and zones are written into the moves at once (they depend on nothing else),
   and later calls find them done.  How far to look ahead follows how much of it was used. */
static void og_judge_zones(O3 *o, const i64 *batch, int nb, const O3M *mv, const i64 *ord, const char *cs, i64 from,
                           i64 ns, char *mark, i64 N, int mg) {
    if (!og_use(nb) || og.check || og.nozones) {
        o3_judge(o, batch, nb, 1);
        return;
    }
    int miss = 0;
    for (int z = 0; z < nb; z++)
        if (!ogz_find(batch[z], 0))
            miss++;
    ogz.ncall++;
    if (miss) {
        if (ogz.made) { /* the last look ahead: used well, look further; hardly, look less far */
            if (2 * ogz.hits >= ogz.made && ogz.look < 8192)
                ogz.look *= 2;
            else if (5 * ogz.hits < ogz.made && ogz.look > 8)
                ogz.look /= 2;
        }
        i64 cap = nb + ogz.look + 1, n = 0, *L = malloc((size_t)cap * 8);
        if (!L)
            DIE("out of memory");
        for (int z = 0; z < nb; z++)
            if (!ogz_find(batch[z], 0))
                L[n++] = batch[z];
        i64 nreq = n;
        for (i64 k = from; k < ns && n < nreq + ogz.look; k++) {
            if (cs[k])
                continue;
            i64 x = ord[k];
            int in = 0;
            for (int z = 0; z < nb; z++)
                in |= batch[z] == x;
            if (in || ogz_find(x, 0) || !o3_place(mark, &mv[x], N, mg, 0, 0))
                continue;
            L[n++] = x;
        }
        og_judge2(o, L, n, 1, 1);
        ogz.made = n - nreq;
        ogz.hits = 0;
        ogz.nahead += n - nreq;
        for (i64 q = 0; q < nreq; q++) {
            OGZ *e = ogz_find(L[q], 0);
            if (e)
                e->memo |= 0x80000000u;
        } /* asked for, not looked ahead */
        free(L);
    }
    i64 *st = o->tc[0].st;
    for (int z = 0; z < nb; z++) {
        OGZ *e = ogz_find(batch[z], 0);
        if (!e)
            DIE("internal error: or3-gpu (zones)");
        if (!(e->memo & 0x80000000u)) {
            ogz.hits++;
            ogz.nused++;
        }
        if (e->joins & 0x80000000u)
            ((O3M *)mv)[batch[z]].gx = O3BAD;
        st[0] += e->lay;
        st[2] += e->joins & 0x7FFFFFFFu;
        st[3] += e->memo & 0x7FFFFFFFu;
        if ((i64)e->mxl > st[1])
            st[1] = e->mxl;
    }
}
/* Judges the n candidates idx[] on the card in one call: writes their blocks, runs launches until every
   candidate is done, reads gains, zones and counters back.  fwd: with zones.  stash: nobody asked for these yet,
   their counters wait in ogz until the selection loop asks.  With --or3-gpu-check the first candidates are judged
   on the host as well and compared. */
static void og_judge2(O3 *o, const i64 *idx, i64 n, int fwd, int stash) {
    double t0 = wall();
    i64 N = o->N;
    OGDev *d = &og.d;
    og_room(n);
    for (i64 q = 0; q < n; q++) {
        O3P R;
        int *cd = og.hcand + q * OG_CW;
        if (!o3_order(&o->mv[idx[q]], N, &R))
            DIE("internal error: segment insertion (order)");
        memset(cd, 0, OG_CW * sizeof(int));
        cd[0] = R.ns;
        for (int j = 0; j < R.ns; j++) {
            cd[1 + j] = (int)R.lo[j];
            cd[8 + j] = (int)(R.lo[j] + R.len[j] - 1);
        }
    }
    d->memomask = 0;
    if (!og.nomemo) { /* the memo of the round: room for twelve keys per candidate */
        i64 want = 1 << 16, most = o->nc > n ? o->nc : n;
        while (want < 12 * most && want < (1LL << 25))
            want <<= 1;
        if (want > og.memocap) {
            if (d->memo)
                OGCK(ogMemFree(d->memo));
            OGCK(ogMemAlloc(&d->memo, (size_t)want * 16));
            og.memocap = want;
            og.memo_clear = 1;
        }
        if (og.memo_clear) {
            OGCK(ogMemsetD8(d->memo, 0, (size_t)og.memocap * 16));
            og.memo_clear = 0;
        }
        d->memomask = og.memocap - 1;
    }
    d->fwd = fwd;
    d->maxlay = o3maxlay > 0 ? o3maxlay : o3maxlay < 0 && !o3old ? 4096 : N + 1;
    double tp0 = wall();
    og.t_prep += tp0 - t0;
    og_run(n);
    double tp1 = wall();
    i64 lay = 0, joins = 0, mxl = 0, nmemo = 0;
    i64 nck = !og.check                 ? 0
              : og_chkmax <= 0          ? n
              : og.nchk >= og_chkmax    ? 0
              : og_chkmax - og.nchk < n ? og_chkmax - og.nchk
                                        : n; /* the first nck are judged on the host as well */
    for (i64 q = 0; q < n; q++) {
        O3M *m = &o->mv[idx[q]];
        const i64 *r = og.hout + q * OG_OW;
        i64 g = r[0] == -(1LL << 40) ? O3BAD : r[0];
        int zn[18];
        for (int z = 0; z < 9; z++) {
            zn[2 * z] = (int)(u32)(u64)r[3 + z];
            zn[2 * z + 1] = (int)(u32)((u64)r[3 + z] >> 32);
        }
        if (fwd && m->gx != O3BAD && g != O3BAD && g != m->gx)
            DIE("internal error: segment insertion (gain %lld, with its zones %lld)", m->gx, g);
        for (int j = 0; j < O3KM; j++) {
            m->zx[j] = zn[j];
            m->zl[j] = zn[6 + j];
            m->zh[j] = zn[12 + j];
        }
        i64 g0 = m->gx;
        m->gx = g;
        if (stash) { /* judged ahead: counted when the loop asks for it; "given up" is said then, too */
            OGZ *e = ogz_find(idx[q], 1);
            e->lay = (u32)(u64)r[1];
            e->mxl = (u32)((u64)r[1] >> 32);
            e->joins = (u32)(u64)r[2] & 0x7FFFFFFFu;
            e->memo = (u32)((u64)r[2] >> 32) & 0x7FFFFFFFu;
            if (g == O3BAD) {
                e->joins |= 0x80000000u;
                m->gx = g0;
            }
            continue;
        }
        if (q < nck)
            continue;
        lay += (u32)(u64)r[1];
        joins += (u32)(u64)r[2];
        nmemo += (i64)((u64)r[2] >> 32);
        if ((i64)((u64)r[1] >> 32) > mxl)
            mxl = (i64)((u64)r[1] >> 32);
    }
    og.ncalls++;
    og.njud += n;
    og.nlay += lay;
    og.njoin += joins;
    og.nmemo += nmemo;
    og.rj += n;
    og.rlay += lay;
    og.rjoin += joins;
    og.rmemo += nmemo;
    int chk = nck > 0;
    {
        i64 *st = o->tc[0].st;
        st[0] += lay;
        st[2] += joins;
        st[3] += nmemo;
        if (mxl > st[1])
            st[1] = mxl;
    }
    double t2 = wall();
    og.t_judge += t2 - t0;
    og.rt += t2 - t0;
    og.t_post += t2 - tp1;
    if (chk) { /* the same candidates on the host: gains and zones must agree; the host's values are kept */
        if (nck > og.chkcap) {
            og.chkcap = nck + nck / 2 + 64;
            free(og.hchk);
            og.hchk = malloc((size_t)og.chkcap * sizeof(O3M));
            if (!og.hchk)
                DIE("out of memory");
        }
        for (i64 q = 0; q < nck; q++)
            og.hchk[q] = o->mv[idx[q]];
        i64 nbad = 0;
#pragma omp parallel for schedule(dynamic, 1) num_threads(NTHR) reduction(+ : nbad)
        for (i64 q = 0; q < nck; q++) {
            O3T *c = &o->tc[omp_get_thread_num()];
            O3M *m = &o->mv[idx[q]];
            const O3M *a = &og.hchk[q];
            i64 g = o3_gain(&c->b, &o->P, o->N, m, c->T0, c->T1, &o->memo, c->st, fwd);
            int diff = g != a->gx;
            for (int j = 0; j < O3KM; j++)
                if (m->zx[j] != a->zx[j] || m->zl[j] != a->zl[j] || m->zh[j] != a->zh[j])
                    diff = 1;
            m->gx = g;
            if (diff) {
                nbad++;
#pragma omp critical(ogchk)
                {
                    printf("or3-gpu-check: MISMATCH (fwd %d): host gain %lld, card %lld; zones host", fwd, g, a->gx);
                    for (int j = 0; j < O3KM; j++)
                        printf(" %d:%d-%d", m->zx[j], m->zl[j], m->zh[j]);
                    printf(", card");
                    for (int j = 0; j < O3KM; j++)
                        printf(" %d:%d-%d", a->zx[j], a->zl[j], a->zh[j]);
                    printf("; ");
                    o3_print(NULL, m, N);
                    printf("\n");
                    fflush(stdout);
                }
            }
        }
        og.nchk += nck;
        og.nbad += nbad;
        og.t_chk += wall() - t2;
        if (og_chkmax > 0 && og.nchk >= og_chkmax) {
            printf(
                "or3-gpu-check: %lld candidates judged on both, %lld MISMATCHES; %lld values of joins on both, %lld MISMATCHES; from here on the card alone\n",
                og.nchk, og.nbad, og.nvchk, og.nvbad);
            fflush(stdout);
        }
    }
}
/* Prints what the card did in this round. */
static void og_round_report(void) {
    if (!og.on || !og.ready || !og.rj)
        return;
    printf(
        "or3-gpu: %lld candidates judged on the card in %.2fs (%.2fs in %lld launches; %lld layers, %lld joins computed, %lld from the memo); tables of the round to the card %.2fs, values of joins %.2fs\n",
        og.rj, og.rt, og.rk, og.rl, og.rlay, og.rjoin, og.rmemo, og.rtab, og.rval);
    fflush(stdout);
}
/* Prints what the card did in the whole pass. */
static void og_report(void) {
    if (!og.on)
        return;
    if (!og.ready) {
        printf("or3-gpu: the card was not used\n");
        return;
    }
    printf(
        "or3-gpu: %lld candidates judged on the card in %lld calls and %lld launches: %.1fs in the kernel, %.1fs in all; %lld layers, %lld joins computed, %lld from the memo; %lld values of joins %.1fs; tables of the rounds %.1fs, start %.1fs\n",
        og.njud, og.ncalls, og.nlaunch, og.t_kern, og.t_judge, og.nlay, og.njoin, og.nmemo, og.nval, og.t_val,
        og.t_round, og.t_init);
    if (og.check)
        printf(
            "or3-gpu-check: %lld candidates judged on both, %lld MISMATCHES (host %.1fs); %lld values of joins on both, %lld MISMATCHES\n",
            og.nchk, og.nbad, og.t_chk, og.nvchk, og.nvbad);
    if (ogz.ncall)
        printf(
            "or3-gpu: zones: %lld calls of the selection loop, %lld candidates judged ahead, %lld of them asked for later\n",
            ogz.ncall, ogz.nahead, ogz.nused);
    printf(
        "or3-gpu: host side of the calls: candidates written %.2fs, sent %.2fs, launches %.2fs, their counters read %.2fs, results fetched %.2fs, results read %.2fs\n",
        og.t_prep, og.t_up, og.t_launch, og.t_ctl, og.t_down, og.t_post);
    fflush(stdout);
    if (og.ctx)
        ogCtxDestroy(og.ctx);
    og.ctx = NULL;
}
/* A fresh pass for a sequence of N events, with the options as given. */
static void o3_init(O3 *o, i64 N) {
    memset(o, 0, sizeof *o);
    o->N = N;
    o->th = o3th < h ? o3th : h - 1;
    o->slack = o3slack;
    o->budget = 4000000000LL; /* chain steps of a round, all threads together */
    o->kc = o3cuts < 3 ? 3 : o3cuts > O3KM ? O3KM : o3cuts;
    o->old = malloc((size_t)N * sizeof(int));
    if (!o->old)
        DIE("out of memory");
}
/* what a round leaves behind (the tables stay if they have been brought up to date: pvalid) */
static void o3_pfree(POT *P) {
    free(P->off);
    free(P->fmin);
    free(P->gmin);
    free(P->fw);
    free(P->bw);
    memset(P, 0, sizeof *P);
}
/* Frees what one round used: pair lists, memo, the tables of the threads, and the two big tables unless they
   are kept (pvalid). */
static void o3_clear(O3 *o) {
    free(o->out.off);
    free(o->out.to);
    free(o->out.c);
    free(o->in.off);
    free(o->in.to);
    free(o->in.c);
    free(o->memo.t);
    memset(&o->out, 0, sizeof o->out);
    memset(&o->in, 0, sizeof o->in);
    memset(&o->memo, 0, sizeof o->memo);
    if (!o->pvalid)
        o3_pfree(&o->P);
    for (int t = 0; t < o->ntc; t++) {
        free(o->tc[t].T0);
        free(o->tc[t].T1);
        bs_free(&o->tc[t].b);
    }
    free(o->tc);
    o->tc = NULL;
    o->ntc = 0;
}
/* Frees everything of the pass. */
static void o3_done(O3 *o) {
    o->pvalid = 0;
    o3_clear(o);
    free(o->old);
    free(o->mv);
    free(o->sv);
    free(o->eid);
    free(o->lastF);
    free(o->lastB);
    free(o->vc);
    free(o->lastJ);
    free(o->jc);
}
/* ---- gains kept from round to round.  The gain of a move is the sum, over its zones, of what the events of the zone
   cost before minus what they cost after (see o3_gain); it is found from the costs (fw) of the events its cuts follow,
   the costs (fw) of the events of its zones, which follow each other as they did, and, for the last stretch, the
   costs from the other end (bw) of its first event.  If none of these has changed since the move was judged, and
   every cut still follows the same event and is followed by the same event, its gain is what it was.  So a candidate
   is named by the names of the events its cuts follow (o->eid) and kept with the round it was judged in and the
   lengths of its zones; lastF, lastB, lastJ say what has changed since.  Only where the tables are kept (pvalid). */
static u64 o3_jkey(const O3 *o, const O3M *m) {
    u64 x = 1469598103934665603ULL ^ (u64)m->k;
    for (int i = 0; i < m->k; i++) {
        x = (x ^ (u64)(m->c[i] < 0 ? 0x1000000 + o->eid[0] : o->eid[m->c[i]])) * 1099511628211ULL;
        x = (x ^ (u64)m->nx[i]) * 1099511628211ULL;
    }
    x = hmix(x);
    return x == ~0ULL ? 0 : x;
}
/* The kept gain with this key, or NULL. */
static O3J *o3_jc_find(const O3 *o, u64 key) {
    if (!o->jc)
        return NULL;
    for (u64 i = key & o->jcmask; o->jc[i].key != ~0ULL; i = (i + 1) & o->jcmask)
        if (o->jc[i].key == key)
            return &o->jc[i];
    return NULL;
}
/* Is the kept gain e of move m still good?  Nothing it depends on may have changed since its round: the
   costs of the events its cuts follow, the costs inside its zones and, for the last block, the costs from the
   other end of its first event. */
static int o3_jc_ok(const O3 *o, const O3M *m, const O3J *e) {
    O3P R;
    int s = e->stamp, nz = 0;
    i64 pe = -1;
    const int *id = o->eid;
    for (int i = 0; i < m->k; i++)
        if (m->c[i] >= 0 && (o->lastF[id[m->c[i]]] >= s || o->lastJ[id[m->c[i]]] >= s))
            return 0;
    if (!o3_order(m, o->N, &R))
        return 0;
    for (int j = 0; j < R.ns; j++) {
        i64 lo = R.lo[j], hi = lo + R.len[j] - 1;
        if (hi < lo)
            continue;
        if (!j) {
            pe = hi;
            continue;
        }
        int zi = nz < O3KM ? nz++ : O3KM - 1;
        if (j == R.ns - 1 && pe >= 0)
            return o->lastB[id[lo]] < s; /* the last stretch: bw of its first event */
        i64 zh = lo + e->zn[zi] - 1;
        if (!e->zn[zi] || zh > hi)
            return 0;
        for (i64 z = lo; z <= zh; z++)
            if (o->lastF[id[z]] >= s || (z < zh && o->lastJ[id[z]] >= s))
                return 0;
        pe = hi;
    }
    return 1;
}
/* Keeps the exact gain and the zone lengths of a judged move under its key.  At 4 million moves the table
   begins again from empty. */
static void o3_jc_put(O3 *o, u64 key, const O3M *m) {
    if (m->gx == O3BAD || m->gx > 30000 || m->gx < -30000)
        return;
    if (!o->jc || 2 * (u64)(o->jcn + 1) > o->jcmask + 1) {
        O3J *old = o->jc;
        u64 om = o->jcmask;
        int wipe = old && om + 1 >= (1ULL << 23); /* 4 million moves: begin again */
        o->jcmask = !old ? (1 << 14) - 1 : wipe ? om : 2 * om + 1;
        o->jc = malloc((size_t)(o->jcmask + 1) * sizeof(O3J));
        if (!o->jc)
            DIE("out of memory");
        for (u64 z = 0; z <= o->jcmask; z++)
            o->jc[z].key = ~0ULL;
        if (wipe)
            o->jcn = 0;
        else if (old)
            for (u64 z = 0; z <= om; z++)
                if (old[z].key != ~0ULL) {
                    u64 q = old[z].key & o->jcmask;
                    while (o->jc[q].key != ~0ULL)
                        q = (q + 1) & o->jcmask;
                    o->jc[q] = old[z];
                }
        free(old);
    }
    u64 i = key & o->jcmask;
    while (o->jc[i].key != ~0ULL && o->jc[i].key != key)
        i = (i + 1) & o->jcmask;
    if (o->jc[i].key == ~0ULL)
        o->jcn++;
    O3J *e = &o->jc[i];
    e->key = key;
    e->stamp = o->round;
    e->gx = (int)m->gx;
    for (int j = 0; j < O3KM; j++) {
        i64 len = m->zh[j] >= m->zl[j] ? (i64)m->zh[j] - m->zl[j] + 1 : 0;
        e->zn[j] = (unsigned short)(len < 65535 ? len : 0);
    } /* a zone too long to note: never taken from here */
}
/* Exact V, from the tables, for the joins of the candidates that are not listed (ux -> uy, ux2 -> uy2): those that at
   least `share` candidates have (share 1: all).  The estimates are corrected (such a join counted as th + 1, the
   least it can be), and a candidate whose estimate can no longer reach its bar is dropped: a long one needs 1 (its
   gain is its estimate), the others more than -slack.  Values kept from earlier rounds are used if the tables of
   both events are what they were.  Returns the number of candidates dropped; *nvalp: joins valued, *nhitp: of them
   known from earlier rounds. */
static i64 o3_value(O3 *o, const POT *P, i64 share, i64 *nvalp, i64 *nhitp) {
    i64 np = 0, m = 0, nsel = 0, ndrop = 0, ntodo = 0;
    int th = o->th, sl = o->slack;
    *nvalp = *nhitp = 0;
    for (i64 k = 0; k < o->sn; k++)
        np += (o->sv[k].ux > -2) + (o->sv[k].ux2 > -2);
    if (!np)
        return 0;
    u64 *pk = malloc((size_t)np * 8);
    unsigned char *pv;
    if (!pk)
        DIE("out of memory");
    for (i64 k = 0; k < o->sn; k++) {
        if (o->sv[k].ux > -2)
            pk[m++] = ((u64)(o->sv[k].ux + 1) << 24) | (u64)o->sv[k].uy;
        if (o->sv[k].ux2 > -2)
            pk[m++] = ((u64)(o->sv[k].ux2 + 1) << 24) | (u64)o->sv[k].uy2;
    }
    qsort(pk, (size_t)np, 8, u64_cmp);
    for (i64 a = 0; a < np;) {
        i64 b = a;
        while (b < np && pk[b] == pk[a])
            b++;
        if (b - a >= share)
            pk[nsel++] = pk[a];
        a = b;
    }
    if (!nsel) {
        free(pk);
        return 0;
    }
    pv = malloc((size_t)nsel + 1);
    i64 *todo = malloc((size_t)(nsel + 1) * 8);
    if (!pv || !todo)
        DIE("out of memory");
    for (i64 k = 0; k < nsel; k++) {
        int v = o->eid ? o3_vc_get(o, o->eid[(pk[k] >> 24) - 1], o->eid[pk[k] & 0xFFFFFF]) : -1;
        if (v >= 0)
            pv[k] = (unsigned char)v;
        else
            todo[ntodo++] = k;
    }
    if (og_use(ntodo)) {
        u64 *pk2 = malloc((size_t)(ntodo + 1) * 8);
        unsigned char *pv2 = malloc((size_t)ntodo + 1);
        if (!pk2 || !pv2)
            DIE("out of memory");
        for (i64 q = 0; q < ntodo; q++)
            pk2[q] = pk[todo[q]];
        og_values(o, pk2, ntodo, pv2);
        for (i64 q = 0; q < ntodo; q++)
            pv[todo[q]] = pv2[q];
        free(pk2);
        free(pv2);
    } else
#pragma omp parallel for schedule(dynamic, 16) num_threads(NTHR)
        for (i64 q = 0; q < ntodo; q++) {
            i64 k = todo[q];
            pv[k] = (unsigned char)o3_exactv(&o->tc[omp_get_thread_num()].b, P, (i64)(pk[k] >> 24) - 1,
                                             (i64)(pk[k] & 0xFFFFFF));
        }
    if (o->eid)
        for (i64 q = 0; q < ntodo; q++) {
            i64 k = todo[q];
            o3_vc_put(o, o->eid[(pk[k] >> 24) - 1], o->eid[pk[k] & 0xFFFFFF], pv[k]);
        }
    *nvalp = nsel;
    *nhitp = nsel - ntodo;
    free(todo);
    m = 0;
    for (i64 k = 0; k < o->sn; k++) {
        O3S *c = &o->sv[k];
        int had = 0, e0 = c->est;
        for (int q = 0; q < 2; q++) {
            int jx = q ? c->ux2 : c->ux, jy = q ? c->uy2 : c->uy;
            if (jx <= -2)
                continue;
            u64 key = ((u64)(jx + 1) << 24) | (u64)jy;
            i64 a = 0, z = nsel;
            while (a < z) {
                i64 mid = (a + z) >> 1;
                if (pk[mid] < key)
                    a = mid + 1;
                else
                    z = mid;
            }
            if (a == nsel || pk[a] != key)
                continue; /* not among those valued this time */
            c->est = (short)(c->est + th + 1 - pv[a]);
            had = 1;
            if (q)
                c->ux2 = c->uy2 = -2;
            else
                c->ux = c->uy = -2;
        }
        if (had && (c->lg ? !o3check && c->est <= o3q_lbar(sl) : c->est <= -sl)) {
            ndrop++;
            continue;
        } /* --or3-check: a long one stays and is judged */
        if (had && e0 > 0 && c->est == 0 && c->ux <= -2 && c->ux2 <= -2 && o3q_skip_s(c)) {
            ndrop++;
            continue;
        } /* --or3-eq-keep */
        o->sv[m++] = *c;
    }
    o->sn = m;
    free(pk);
    free(pv);
    return ndrop;
}
/* ==================== own part of this file, 3: the candidates of a round in bounded memory (--or3-hmem) ==================== */
/* ---------- the candidates of a round in bounded memory (--or3-hmem MB).
   o3_prepare as it was keeps every move the search finds (52 bytes), sorts them to drop those found more than once,
   and then holds every candidate in full (160 bytes) until the round ends: 4.8 GB for 36 million moves at n = 12.
   Here the round gets the same candidates in the same order (o3e_cmp: long ones, chains, two-pair moves; inside
   each by falling estimate, then by the move), but they are made a piece at a time:
   - A candidate is 24 bytes (O3R): w[0] = class and estimate, w[1], w[2] = number of cuts, the cuts, and the rank of
     nx among the permutations; numbers compare as o3e_cmp does.
   - Chains.  A move whose joins are all listed is found once from every cut from which the sums stay above the bar
     (o3_step); such a move is kept only when it is found from the smallest of those cuts (o3h_canon works that out
     from the V of its joins), so nothing is found twice and nothing has to be sorted to drop repeats.  The first
     cuts are searched a share at a time; after each share the closing joins that are not listed get their exact V
     (the kept values, the card, or the host), the moves that fall below the bar are dropped, and what is left goes
     to the store.  A closing join belongs to one first cut, so no join is valued twice.  If the store is full it
     keeps the best ranks only (rank: class, estimate, number of cuts, first cut) and the search is run again for
     the next ranks when the round gets there.
   - Two-pair moves (o3_cross) are not stored at all.  They are counted once, for every estimate and first cut, and
     made again a window of first cuts at a time when the round asks for them: the pair with the larger value
     (2e above the bar) looks through the groups of pairs that cross it, as o3_cross does, but a move both of whose
     pairs are such is made from its first pair only.  A long move (--or3-long) gains its estimate with the exact V
     of its joins: those are properties of its two pairs, so every pair that can be part of a long move gets its
     exact value first (o3h_pairs) and the long moves are counted and made from those values; the moves that are
     not long are found without looking at the long ones (three ranges of the crossing pair instead of one).
   - The round (o3h_batches, called by o3_full) takes the candidates in pieces of og_chunk(), judges them and keeps
     only the shorter ones of a batch (32 bytes each) for the choice of moves, which is the one of o3_full.
   What differs from one list of all moves (--or3-hmem 0): nothing in the candidates, their order, the batches and the moves taken
   (--or3-hcheck makes both lists every round and compares them).  The log differs where it counts work: with four
   cuts and more "moves" counts a two-pair move once, joins of long two-pair moves are valued per pair, and when
   the time limit ends a round the candidates not looked at are not counted.  --or3-old, --or3-check, --or3-focus
   and more than 262,141 events use the one list.  With --or3-dry the joins are valued (with the one list they are not). */
static i64 o3h_mb =
    768; /* --or3-hmem MB: room for the candidates (store, window, moves of a share); 0: one list of all moves */
static int o3h_chk = 0, o3h_ctx = 0; /* --or3-hcheck; o3_prepare is called by o3_full */
static i64 o3h_rec = 0; /* --or3-hrec R (for tests): the store holds R candidates, a window and a share R / 2 */
static i64 o3h_max = 0; /* --or3-hmax M: a round looks at the first M candidates of its list only (0: all) */
#define O3H_LBAR(sl) o3q_lbar(sl) /* a long candidate needs an estimate above this */
#ifndef O3H_OTHER_LISTS
#define O3H_OTHER_LISTS            \
    (o3q_eq > 0 && o3q_keep > 0 && \
     o->kc >= 4) /* a condition under which the one list is used: --or3-eq-keep does not thin two-pair moves here */
#endif
#define O3H_VCMAX (1LL << 22) /* values of joins kept between rounds: no new ones beyond this many (128 MB) */
#define O3H_NCMEMO \
    (1LL           \
     << 19) /* the memo of the card is sized for at most this many candidates (128 MB there and in the host's committed memory) */
#define O3H_JCMAX \
    (1LL          \
     << 22) /* gains are kept between rounds (o3_jc_put) only in rounds with at most this many candidates: more do not fit (it begins again at 4 million) */
typedef struct {
    u64 w[3];
} O3R;
/* a chain as it is found: w[0] = class | long << 8 | (estimate + 0x8000) << 16 | (kx + 1) << 32; kx: its closing join among the keys of the thread, -1: listed */
/* a shorter candidate of a batch: w[0] = (2^24 - gain) << 16 | 0x8000 - estimate */
typedef struct {
    u64 w[3];
} O3K;
#define O3H_M18 0x3FFFFULL
#if defined(_WIN32)
__declspec(dllimport) void *__stdcall VirtualAlloc(void *, size_t, unsigned long, unsigned long);
__declspec(dllimport) int __stdcall VirtualFree(void *, size_t, unsigned long);
__declspec(dllimport) void *__stdcall GetCurrentProcess(void);
__declspec(dllimport) int __stdcall K32GetProcessMemoryInfo(void *, void *, unsigned long);
/* committed memory of the process now and at its peak, in MB (what a memory limit on the job counts) */
/* PROCESS_MEMORY_COUNTERS: PagefileUsage, PeakPagefileUsage */
static void o3h_commit(i64 *now, i64 *peak) {
    size_t c[9];
    memset(c, 0, sizeof c);
    *(unsigned int *)c = sizeof c;
    K32GetProcessMemoryInfo(GetCurrentProcess(), c, sizeof c);
    *now = (i64)(c[7] >> 20);
    *peak = (i64)(c[8] >> 20);
}
#else
static void o3h_commit(i64 *now, i64 *peak) {
    *now = *peak = 0;
}
#endif
/* memory that grows without being copied: address space is set aside, pages are taken as they are needed */
/* low: the pages below this have been given back */
typedef struct {
    char *p;
    size_t res, com, low;
} O3HV;
/* Gives the address space and its pages back. */
static void o3hv_close(O3HV *v) {
#if defined(_WIN32)
    if (v->p)
        VirtualFree(v->p, 0, 0x8000);
#else
    free(v->p);
#endif
    v->p = NULL;
    v->res = v->com = v->low = 0;
}
/* Sets aside address space for `bytes`.  Pages are taken later, as they are needed (o3hv_need). */
static void o3hv_open(O3HV *v, size_t bytes) {
    o3hv_close(v);
    v->res = (bytes + (64 << 20)) & ~(size_t)0xFFFF;
#if defined(_WIN32)
    v->p = VirtualAlloc(NULL, v->res, 0x2000, 1);
    if (!v->p)
        DIE("out of address space (%.1f GB)", v->res / 1073741824.0);
#endif
}
/* after this v->p may be another address */
static void o3hv_need(O3HV *v, size_t bytes) {
    if (bytes <= v->com)
        return;
    size_t want = (bytes + bytes / 16 + (4 << 20)) & ~(size_t)0xFFFF;
    if (want > v->res || !v->res) {
#if defined(_WIN32)
        O3HV w;
        memset(&w, 0, sizeof w);
        o3hv_open(&w, want + want / 2);
        if (v->com) {
            if (!VirtualAlloc(w.p, v->com, 0x1000, 4))
                DIE("out of memory");
            memcpy(w.p, v->p, v->com);
            w.com = v->com;
        }
        o3hv_close(v);
        *v = w;
#else
        v->res = want + want / 2;
#endif
    }
    if (want > v->res)
        want = v->res;
#if defined(_WIN32)
    if (!VirtualAlloc(v->p + v->com, want - v->com, 0x1000, 4))
        DIE("out of memory");
#else
    v->p = realloc(v->p, want);
    if (!v->p)
        DIE("out of memory");
#endif
    v->com = want;
}
/* what lies below `bytes` has been read: its pages go back (not written again before o3hv_open) */
static void o3hv_drop(O3HV *v, size_t bytes) {
    size_t to = bytes & ~(size_t)0xFFFF;
    if (to > v->com)
        to = v->com & ~(size_t)0xFFFF;
    if (to < v->low + (16 << 20))
        return;
#if defined(_WIN32)
    VirtualFree(v->p + v->low, to - v->low, 0x4000);
    v->low = to;
#endif
}
/* pages above `bytes` go back */
static void o3hv_trim(O3HV *v, size_t bytes) {
    size_t keep = (bytes + 0xFFFF) & ~(size_t)0xFFFF;
    if (keep >= v->com)
        return;
#if defined(_WIN32)
    VirtualFree(v->p + keep, v->com - keep, 0x4000);
    v->com = keep;
#else
    if (!keep) {
        free(v->p);
        v->p = NULL;
        v->com = 0;
    }
#endif
}
/* sorting: quicksort with the median of three (of nine for long arrays), the two parts as tasks */
#define O3H_QS(NAME, T, LT)                                                                                           \
    static inline T *NAME##_m3(T *a, T *b, T *c) {                                                                    \
        return LT(a, b) ? (LT(b, c) ? b : LT(a, c) ? c : a) : (LT(a, c) ? a : LT(b, c) ? c : b);                      \
    }                                                                                                                 \
    static i64 NAME##_part(T *a, i64 n) {                                                                             \
        T *l = a, *m = a + n / 2, *r = a + n - 1, p, t;                                                               \
        if (n > 2048) {                                                                                               \
            i64 s = n / 8;                                                                                            \
            l = NAME##_m3(a, a + s, a + 2 * s);                                                                       \
            m = NAME##_m3(m - s, m, m + s);                                                                           \
            r = NAME##_m3(r - 2 * s, r - s, r);                                                                       \
        }                                                                                                             \
        p = *NAME##_m3(l, m, r);                                                                                      \
        i64 i = -1, j = n;                                                                                            \
        for (;;) {                                                                                                    \
            do                                                                                                        \
                i++;                                                                                                  \
            while (LT(&a[i], &p));                                                                                    \
            do                                                                                                        \
                j--;                                                                                                  \
            while (LT(&p, &a[j]));                                                                                    \
            if (i >= j)                                                                                               \
                break;                                                                                                \
            t = a[i];                                                                                                 \
            a[i] = a[j];                                                                                              \
            a[j] = t;                                                                                                 \
        }                                                                                                             \
        return j == n - 1 ? n - 2 : j;                                                                                \
    }                                                                                                                 \
    static void NAME##_1(T *a, i64 n) {                                                                               \
        while (n > 20) {                                                                                              \
            i64 j = NAME##_part(a, n);                                                                                \
            if (j + 1 < n - j - 1) {                                                                                  \
                NAME##_1(a, j + 1);                                                                                   \
                a += j + 1;                                                                                           \
                n -= j + 1;                                                                                           \
            } else {                                                                                                  \
                NAME##_1(a + j + 1, n - j - 1);                                                                       \
                n = j + 1;                                                                                            \
            }                                                                                                         \
        }                                                                                                             \
        for (i64 i = 1; i < n; i++) {                                                                                 \
            T x = a[i];                                                                                               \
            i64 j = i;                                                                                                \
            while (j > 0 && LT(&x, &a[j - 1])) {                                                                      \
                a[j] = a[j - 1];                                                                                      \
                j--;                                                                                                  \
            }                                                                                                         \
            a[j] = x;                                                                                                 \
        }                                                                                                             \
    }                                                                                                                 \
    static void NAME##_par(T *a, i64 n, i64 cut) {                                                                    \
        while (n > cut) {                                                                                             \
            i64 j = NAME##_part(a, n);                                                                                \
            T *b = a + j + 1;                                                                                         \
            i64 nb = n - j - 1;                                                                                       \
            _Pragma("omp task firstprivate(b, nb, cut)") NAME##_par(b, nb, cut);                                      \
            n = j + 1;                                                                                                \
        }                                                                                                             \
        NAME##_1(a, n);                                                                                               \
    }                                                                                                                 \
    static void NAME(T *a, i64 n) {                                                                                   \
        if (n < (1 << 14) || NTHR < 2) {                                                                              \
            NAME##_1(a, n);                                                                                           \
            return;                                                                                                   \
        }                                                                                                             \
        _Pragma("omp parallel num_threads(NTHR)") _Pragma("omp single") NAME##_par(a, n, n / (8 * (i64)NTHR) + 2048); \
    }
#define O3R_LT(x, y)                                  \
    ((x)->w[0] != (y)->w[0]   ? (x)->w[0] < (y)->w[0] \
     : (x)->w[1] != (y)->w[1] ? (x)->w[1] < (y)->w[1] \
                              : (x)->w[2] < (y)->w[2])
#define O3XA_LT(x, y) ((x)->e != (y)->e ? (x)->e > (y)->e : (x)->a != (y)->a ? (x)->a < (y)->a : (x)->b < (y)->b)
#define O3XB_LT(x, y) ((x)->e != (y)->e ? (x)->e > (y)->e : (x)->b != (y)->b ? (x)->b < (y)->b : (x)->a < (y)->a)
O3H_QS(o3r_sort, O3R, O3R_LT)
#define O3K_LT(x, y)                                                \
    (((x)->w[0] >> 16) != ((y)->w[0] >> 16) ? (x)->w[0] < (y)->w[0] \
     : (x)->w[1] != (y)->w[1]               ? (x)->w[1] < (y)->w[1] \
                                            : (x)->w[2] < (y)->w[2])
O3H_QS(o3k_sort, O3K, O3K_LT)
O3H_QS(o3xa_sort, O3X, O3XA_LT)
O3H_QS(o3xb_sort, O3X, O3XB_LT)
/* nx among the permutations of k, in the order of o3k_cmp */
static inline int o3h_nxrank(const int *nx, int k) {
    int r = 0;
    for (int i = 0; i < k; i++) {
        int s = 0;
        for (int j = i + 1; j < k; j++)
            s += nx[j] < nx[i];
        r = r * (k - i) + s;
    }
    return r;
}
/* The inverse of o3h_nxrank: the order nx of k blocks from its rank r. */
static inline void o3h_nxun(int r, int k, int *nx) {
    int f[O3KM], used = 0;
    for (int i = k - 1; i >= 0; i--) {
        f[i] = r % (k - i);
        r /= k - i;
    }
    for (int i = 0; i < k; i++) {
        int s = f[i], v = 0;
        for (;; v++)
            if (!((used >> v) & 1)) {
                if (!s)
                    break;
                s--;
            }
        nx[i] = v;
        used |= 1 << v;
    }
}
/* First word of a packed candidate: class and estimate, so that packed candidates compare as numbers in the
   order of o3e_cmp. */
static inline u64 o3h_w0(int cls, int est) {
    if (est <= -32000 || est >= 32000)
        DIE("internal error: segment insertion (estimate %d)", est);
    return ((u64)cls << 16) | (u64)(0x8000 - est);
}
/* w[1], w[2] */
static inline void o3h_packm(u64 *w, int k, const int *c, int nxr) {
    u64 a = (u64)k << 54, b = (u64)nxr;
    if (k > 0)
        a |= (u64)(c[0] + 1) << 36;
    if (k > 1)
        a |= (u64)(c[1] + 1) << 18;
    if (k > 2)
        a |= (u64)(c[2] + 1);
    if (k > 3)
        b |= (u64)(c[3] + 1) << 46;
    if (k > 4)
        b |= (u64)(c[4] + 1) << 28;
    if (k > 5)
        b |= (u64)(c[5] + 1) << 10;
    w[1] = a;
    w[2] = b;
}
/* A full move record from a packed candidate. */
static inline void o3h_unpack(const u64 *w, int est, O3M *m) {
    memset(m, 0, sizeof *m);
    int k = (int)(w[1] >> 54) & 7;
    m->k = k;
    if (k > 0)
        m->c[0] = (int)((w[1] >> 36) & O3H_M18) - 1;
    if (k > 1)
        m->c[1] = (int)((w[1] >> 18) & O3H_M18) - 1;
    if (k > 2)
        m->c[2] = (int)(w[1] & O3H_M18) - 1;
    if (k > 3)
        m->c[3] = (int)((w[2] >> 46) & O3H_M18) - 1;
    if (k > 4)
        m->c[4] = (int)((w[2] >> 28) & O3H_M18) - 1;
    if (k > 5)
        m->c[5] = (int)((w[2] >> 10) & O3H_M18) - 1;
    o3h_nxun((int)(w[2] & 1023), k, m->nx);
    m->est = est;
    m->ux = m->uy = m->ux2 = m->uy2 = -2;
    m->gx = O3BAD;
    m->lg = o3_islong(m);
    m->tp = k == 4 && m->nx[0] == 2 && m->nx[1] == 3 && m->nx[2] == 0 && m->nx[3] == 1;
}
#define O3H_EST(w0) (0x8000 - (int)((w0) & 0xFFFF))
#define O3H_NXTP 16 /* the rank of nx = 2 3 0 1 */
/* the rank of a candidate: class, estimate, number of cuts, first cut */
#define O3H_R1(r) ((r)->w[1] >> 36)
static inline int o3h_rlt(u64 a0, u64 a1, u64 b0, u64 b1) {
    return a0 != b0 ? a0 < b0 : a1 < b1;
}
/* ---------- moves of equal length (--or3-eq) on the candidates in bounded memory (--or3-hmem).  What the part
   "moves of equal length" above does with the one list o->mv is done here with the list as o3h_batches reads it:
   - the search of o3h_begin keeps a long candidate with estimate 0 (O3H_LBAR = o3q_lbar) and thins the moves with
     estimate 0 for --or3-eq-keep by the same hash and rate as o3_emit and o3_value do (o3h_emit, o3h_share; the
     rate is set by o3hq_pre as o3q_scan sets it; the first round of a pass counts with o3_scan, which stores
     nothing then);
   - o3h_batches sets the candidates with estimate 0 apart as it reads them (24 bytes each), notes those judged with
     gain 0, makes the draw when the list is at its end (o3hq_draw: the same order, the same random numbers), judges
     the ones drawn with the last batch, and after it takes the moves of equal length (o3hq_equal, through o3q_take).
   With four cuts and more and --or3-eq-keep the one list is used (the two-pair moves are not thinned here). */
static int o3hq_thin = 0;
static i64 o3hq_cnt0 = -1, o3hq_seen0 = -1;
static double o3hq_tcnt = 0;
/* before the search of o3h_begin: the rate of --or3-eq-keep, as o3q_scan */
static void o3hq_pre(O3 *o) {
    o3hq_thin = o3q_eq > 0 && o3q_keep > 0 && !o3old;
    o3hq_cnt0 = -1;
    o3hq_tcnt = 0;
    o3q_div = 1;
    if (o3hq_thin) {
        if (o3q_seen < 0) { /* the first round of a pass: once only to count */
            double t0 = wall();
            memset(o3q_z0, 0, sizeof o3q_z0);
            free(o->sv);
            o->sv = NULL;
            o->sn = o->scap = 0;
            o->ntried = 0;
            o3q_cnt = 1;
            o3_scan(o);
            o3q_cnt = 0;
            o3q_seen = 0;
            for (int t = 0; t < 256; t++)
                o3q_seen += o3q_z0[t][0];
            free(o->sv);
            o->sv = NULL;
            o->sn = o->scap = 0;
            o->ntried = 0;
            o3hq_cnt0 = o3q_seen;
            o3hq_tcnt = wall() - t0;
        }
        o3q_div = (u64)((o3q_seen + o3q_keep - 1) / o3q_keep);
        if (o3q_div < 1)
            o3q_div = 1;
        o3q_salt = hmix(((u64)o->round << 32) ^ o3q_seedv ^ 0x5851F42D4C957F2DULL);
    }
    o3hq_seen0 = o3q_seen;
    memset(o3q_z0, 0, sizeof o3q_z0);
}
/* after it: the number of moves with estimate 0 found, for the rate of the next round (again: with --or3-hcheck the
   search for the one list follows in the same round and must find the rate this one had) */
static void o3hq_post(O3 *o, int again) {
    if (o3q_eq <= 0)
        return;
    o3q_seen = 0;
    for (int t = 0; t < 256; t++)
        o3q_seen += o3q_z0[t][0];
    if (o3hq_thin && !o->quiet) {
        printf("segment insertion: %lld moves with estimate 0 found, one in %llu kept (--or3-eq-keep %lld)", o3q_seen,
               (unsigned long long)o3q_div, o3q_keep);
        if (o3hq_cnt0 >= 0)
            printf("; counted first: %lld (%.1fs)", o3hq_cnt0, o3hq_tcnt);
        printf("\n");
        fflush(stdout);
    }
    if (again)
        o3q_seen = o3hq_seen0;
}
/* a move that is found (o3h_emit): 1 = it is not kept (as o3q_skip; cnt: only in the first search of a round) */
static inline int o3hq_skip(int est, int k, const int *c, const int *nx, int cnt) {
    if (o3q_eq <= 0 || est != 0)
        return 0;
    if (cnt)
        o3q_z0[omp_get_thread_num()][0]++;
    return o3q_div > 1 && o3q_mhash(k, c, nx) % o3q_div != 0;
}
/* a chain whose estimate has come down to 0 with the value of its closing join (o3h_share): as o3q_skip_s */
static inline int o3hq_skip_r(const O3R *x) {
    if (o3q_eq <= 0 || o3q_div <= 1)
        return 0;
    int k = (int)(x->w[1] >> 54) & 7, c[O3KM], nx[O3KM];
    if (k > 0)
        c[0] = (int)((x->w[1] >> 36) & O3H_M18) - 1;
    if (k > 1)
        c[1] = (int)((x->w[1] >> 18) & O3H_M18) - 1;
    if (k > 2)
        c[2] = (int)(x->w[1] & O3H_M18) - 1;
    if (k > 3)
        c[3] = (int)((x->w[2] >> 46) & O3H_M18) - 1;
    if (k > 4)
        c[4] = (int)((x->w[2] >> 28) & O3H_M18) - 1;
    if (k > 5)
        c[5] = (int)((x->w[2] >> 10) & O3H_M18) - 1;
    o3h_nxun((int)(x->w[2] & 1023), k, nx);
    return o3q_mhash(k, c, nx) % o3q_div != 0;
}
typedef struct { /* a thread of the chain search */
    O3HV rv;
    O3R *raw;
    i64 nraw, rcap, nout;
    u64 *key;
    i64 nkey, kcap, base;
    int *kix, *touch, ntouch;
    unsigned char *cl;
    i64 nfound, ndup, ntried, budget, nnode[O3KM + 2], byk[O3KM + 1], nun, nkept, nlong, ndrop;
} O3HT;
/* the two-pair moves of one class and estimate */
typedef struct {
    u64 w0;
    int kind[2], ei[2], nk;
    i64 tot;
} O3HB;
typedef struct {
    int act, vfy;
    O3 *o;
    i64 N;
    int Z, sl, th, nthr;
    /* the chains: s[0 .. sn-1], sorted; the ranks lo <= rank < hi are there; more: there are chains at hi and beyond */
    O3HV sv;
    O3R *s;
    i64 sn, scap, si, rawcap, rawn;
    u64 lo0, lo1, hi0, hi1;
    int more, npass, over;
    i64 nchain, byk[O3KM + 1], nfound, ndup, nun, nval, nhit, nkept, nlong, ncut;
    /* the pairs: kind 0 with the V of the lists (moves that are not long), kind 1 with exact V (long moves); X by e, a, b; Y by e, b, a */
    O3X *X[2], *Y[2];
    i64 nx[2], ntop[2], *gs[2];
    int bar[2], emax[2], ngr[2], elo[2], ne[2], cls[2];
    u32 **cnt[2];
    i64 ntp[2], npv, nphit;
    O3HB *tb;
    int ntb, ti;
    i64 ta, *pos, *off;
    /* the piece the round reads now */
    O3HV gv;
    const O3R *g;
    i64 gn, gi, segmax, nseg, nfill;
    double tfill, tpass, tsort, tval, tpair, tcount;
    i64 nall, peak;
} O3H;
static O3H o3h;
/* Frees the lists of the round. */
static void o3h_close(O3H *h) {
    o3hv_close(&h->sv);
    o3hv_close(&h->gv);
    for (int q = 0; q < 2; q++) {
        free(h->X[q]);
        free(h->Y[q]);
        free(h->gs[q]);
        if (h->cnt[q]) {
            for (int e = 0; e < h->ne[q]; e++)
                free(h->cnt[q][e]);
            free(h->cnt[q]);
        }
        h->X[q] = h->Y[q] = NULL;
        h->gs[q] = NULL;
        h->cnt[q] = NULL;
        h->nx[q] = h->ntop[q] = h->ntp[q] = 0;
        h->ne[q] = h->ngr[q] = 0;
    }
    free(h->tb);
    free(h->pos);
    free(h->off);
    h->tb = NULL;
    h->pos = h->off = NULL;
    h->ntb = 0;
    h->s = NULL;
    h->g = NULL;
    h->sn = h->gn = h->gi = h->si = 0;
    h->act = h->vfy = 0;
}
static inline void o3h_mem(O3H *h) {
    i64 m = (i64)(h->sv.com + h->gv.com);
    if (m > h->peak)
        h->peak = m;
}
/* exact V of the joins pk[0 .. n-1] (keys as in o3_value): the values kept, else the card or the host; new ones are kept */
static void o3h_values(O3 *o, const POT *P, const u64 *pk, i64 n, unsigned char *pv, i64 *nhit) {
    i64 ntodo = 0;
    if (n <= 0)
        return;
#pragma omp parallel for schedule(static) num_threads(NTHR)
    for (i64 k = 0; k < n; k++) {
        int v = o->eid ? o3_vc_get(o, o->eid[(pk[k] >> 24) - 1], o->eid[pk[k] & 0xFFFFFF]) : -1;
        pv[k] = v >= 0 ? (unsigned char)v : 255;
    }
    for (i64 k = 0; k < n; k++)
        ntodo += pv[k] == 255;
    *nhit += n - ntodo;
    if (!ntodo)
        return;
    u64 *pk2 = malloc((size_t)(ntodo + 1) * 8);
    unsigned char *pv2 = malloc((size_t)ntodo + 1);
    if (!pk2 || !pv2)
        DIE("out of memory");
    {
        i64 q = 0;
        for (i64 k = 0; k < n; k++)
            if (pv[k] == 255)
                pk2[q++] = pk[k];
    }
    if (og_use(ntodo))
        og_values(o, pk2, ntodo, pv2);
    else {
#pragma omp parallel for schedule(dynamic, 16) num_threads(NTHR)
        for (i64 q = 0; q < ntodo; q++)
            pv2[q] = (unsigned char)o3_exactv(&o->tc[omp_get_thread_num()].b, P, (i64)(pk2[q] >> 24) - 1,
                                              (i64)(pk2[q] & 0xFFFFFF));
    }
    {
        i64 q = 0;
        for (i64 k = 0; k < n; k++)
            if (pv[k] == 255)
                pv[k] = pv2[q++];
    }
    if (o->eid)
        for (i64 q = 0; q < ntodo && o->vcn < O3H_VCMAX; q++)
            o3_vc_put(o, o->eid[(pk2[q] >> 24) - 1], o->eid[pk2[q] & 0xFFFFFF], pv2[q]);
    free(pk2);
    free(pv2);
}
/* ---- the chains.  r[0 .. k-1]: the cuts in the order they were made; vv[i]: V of the join r[i] -> the event after
   r[i + 1] (vv[k - 1]: of the closing join).  Would the search also find this move from the cut r[j]?  It does if the
   first cut passes the bar, every join but the last can be a step (listed, or the first / last place: the closing join
   from before the first event to behind the last one is the one that cannot), and the sums stay above the bar. */
static inline int o3h_canon(const O3 *o, const int *r, const int *vv, int k) {
    int sl = o->slack, cst = !(r[k - 1] < 0 && (i64)r[0] + 1 >= o->N);
    for (int j = 1; j < k; j++) {
        if (r[j] > r[0])
            continue;
        int g = o3_old(o, r[j]), ok = g > -sl;
        for (int i = 0; ok && i + 1 < k; i++) {
            int q = (j + i) % k, p = g - vv[q];
            if ((q == k - 1 && !cst) || p <= -sl - o3dip)
                ok = 0;
            g = p + o3_old(o, r[(j + i + 1) % k]);
        }
        if (ok)
            return 0;
    }
    return 1;
}
/* A chain found by the search.  Its cuts are sorted and it is dropped if it does not give one sequence, or
   if a smaller first cut finds the same chain (so a repeat is never stored).  Then it is stored packed, or only
   counted in a pass that counts.  unl: its closing join is not listed and gets its value later. */
static void o3h_emit(const O3H *h, O3HT *t, const int *r, const int *vv, int k, int est, int unl) {
    const O3 *o = h->o;
    int c[O3KM], nx[O3KM], ord[O3KM], rank[O3KM], lg = 0, cls;
    for (int i = 0; i < k; i++) {
        int z = i;
        while (z > 0 && r[ord[z - 1]] > r[i]) {
            ord[z] = ord[z - 1];
            z--;
        }
        ord[z] = i;
    }
    for (int z = 0; z < k; z++) {
        c[z] = r[ord[z]];
        rank[ord[z]] = z;
    }
    for (int i = 0; i < k; i++)
        nx[rank[i]] = rank[(i + 1) % k];
    {
        int s = 0, n = 0;
        for (;;) {
            if (n > k)
                return;
            n++;
            if (s == k)
                break;
            s = nx[s] + 1;
        }
        if (n != k + 1)
            return;
    } /* o3_order: one sequence? */
    if (h->Z > 0) {
        lg = 1;
        for (int i = 0; i + 1 < k; i++)
            if (c[i + 1] - c[i] < h->Z) {
                lg = 0;
                break;
            }
    }
    if (lg && est <= O3H_LBAR(h->sl))
        return;
    if (o3hq_skip(est, k, c, nx, h->npass == 1))
        return;
    t->nfound++;
    if (!unl && !o3h_canon(o, r, vv, k)) {
        t->ndup++;
        return;
    }
    cls = o3order ? (lg ? 0 : 1) : 0;
    if (h->npass > 1) { /* a later pass: only what can still lie in lo <= rank < hi */
        u64 w0 = o3h_w0(cls, est), r1 = ((u64)k << 18) | (u64)(c[0] + 1);
        if (!o3h_rlt(w0, r1, h->hi0, h->hi1) || (!unl && o3h_rlt(w0, r1, h->lo0, h->lo1)))
            return;
    }
    if (t->nraw >= t->rcap) {
        o3hv_need(&t->rv, (size_t)(t->nraw + 1) * sizeof(O3R));
        t->raw = (O3R *)t->rv.p;
        t->rcap = (i64)(t->rv.com / sizeof(O3R));
    }
    O3R *x = &t->raw[t->nraw++];
    int kx = -1;
    o3h_packm(x->w, k, c, o3h_nxrank(nx, k));
    if (est <= -32000 || est >= 32000)
        DIE("internal error: segment insertion (estimate %d)", est);
    if (unl) {
        int cl = r[k - 1];
        if (t->kix[cl + 1] < 0) {
            if (t->nkey == t->kcap) {
                t->kcap = t->kcap ? t->kcap + t->kcap / 2 : 1 << 12;
                t->key = realloc(t->key, (size_t)t->kcap * 8);
                if (!t->key)
                    DIE("out of memory");
            }
            t->kix[cl + 1] = (int)t->nkey;
            t->touch[t->ntouch++] = cl + 1;
            t->key[t->nkey++] = ((u64)(cl + 1) << 24) | (u64)(r[0] + 1);
        }
        kx = t->kix[cl + 1];
    }
    x->w[0] = (u64)cls | ((u64)lg << 8) | ((u64)(est + 0x8000) << 16) | ((u64)(kx + 1) << 32);
}
static void o3h_dfs(const O3H *h, O3HT *t, int *r, int *vv, int d, int g);
/* As o3_step, for the bounded lists: the new join r[d] -> y worth v, then the join before y is cut.  A chain
   that closes goes to o3h_emit. */
static inline void o3h_step(const O3H *h, O3HT *t, int *r, int *vv, int d, int g, i64 y, int v) {
    const O3 *o = h->o;
    int c = (int)y - 1, p = g - v, sl = o->slack;
    if (p <= -sl - o3dip || c == r[d])
        return;
    for (int z = 0; z < d; z++)
        if (r[z] == c)
            return;
    r[d + 1] = c;
    vv[d] = v;
    p += o3_old(o, c);
    if (d + 2 >= 3) {
        i64 y0 = (i64)r[0] + 1;
        int v2 = c < 0 || y0 >= o->N ? 0 : t->cl[c + 1] == 255 ? -1 : t->cl[c + 1];
        if (v2 >= 0) {
            if (p - v2 > -sl) {
                vv[d + 1] = v2;
                o3h_emit(h, t, r, vv, d + 2, p - v2, 0);
            }
        } else if (p - (o->th + 1) > -sl)
            o3h_emit(h, t, r, vv, d + 2, p - (o->th + 1), 1);
    }
    if (d + 2 < o->kc)
        o3h_dfs(h, t, r, vv, d + 1, p);
}
/* As o3_dfs, for the bounded lists. */
static void o3h_dfs(const O3H *h, O3HT *t, int *r, int *vv, int d, int g) {
    const O3 *o = h->o;
    i64 N = o->N;
    int x = r[d], lim = g + o->slack + o3dip;
    t->nnode[d]++;
    if (t->ntried++ > t->budget)
        return;
    if (x < 0) {
        for (i64 y = 1; y < N; y++)
            o3h_step(h, t, r, vv, d, g, y, 0);
        return;
    }
    const JG *out = &o->out;
    for (i64 f = out->off[x], e1 = out->off[x + 1]; f < e1 && out->c[f] < lim; f++)
        o3h_step(h, t, r, vv, d, g, out->to[f], out->c[f]);
    if (x < N - 1)
        o3h_step(h, t, r, vv, d, g, N, 0);
}
/* the store is over its size: it keeps the lowest ranks, seven eighths of its size; from now on only ranks below the new hi come in */
static void o3h_cut(O3H *h) {
    double t0 = wall();
    o3r_sort(h->s, h->sn);
    h->tsort += wall() - t0;
    i64 q = h->scap - h->scap / 8;
    u64 r0 = h->s[q].w[0], r1 = O3H_R1(&h->s[q]);
    while (q > 0 && h->s[q - 1].w[0] == r0 && O3H_R1(&h->s[q - 1]) == r1)
        q--;
    if (!q) {
        while (q < h->sn && h->s[q].w[0] == r0 && O3H_R1(&h->s[q]) == r1)
            q++;
        if (q == h->sn) {
            h->scap = h->sn + h->sn / 2;
            return;
        }
        r0 = h->s[q].w[0];
        r1 = O3H_R1(&h->s[q]);
    }
    h->hi0 = r0;
    h->hi1 = r1;
    h->more = 1;
    h->sn = q;
    h->ncut++;
}
/* a share of the first cuts has been searched: values, final estimates, and into the store */
static void o3h_share(O3H *h, O3HT *T) {
    O3 *o = h->o;
    i64 nk = 0, nadd = 0;
    int th = h->th, sl = h->sl, first = h->npass == 1;
    for (int t = 0; t < h->nthr; t++) {
        T[t].base = nk;
        nk += T[t].nkey;
    }
    u64 *pk = malloc((size_t)(nk + 1) * 8);
    unsigned char *pv = malloc((size_t)nk + 1);
    if (!pk || !pv)
        DIE("out of memory");
    for (int t = 0; t < h->nthr; t++)
        if (T[t].nkey)
            memcpy(pk + T[t].base, T[t].key, (size_t)T[t].nkey * 8);
    {
        i64 nh = 0;
        double t0 = wall();
        o3h_values(o, &o->P, pk, nk, pv, &nh);
        h->tval += wall() - t0;
        if (first) {
            h->nval += nk;
            h->nhit += nh;
        }
    }
#pragma omp parallel for schedule(static, 1) num_threads(h->nthr)
    for (int t = 0; t < h->nthr; t++) {
        O3HT *c = &T[t];
        O3R *out = c->raw;
        i64 m = 0;
        for (i64 i = 0; i < c->nraw; i++) {
            O3R x = c->raw[i];
            int est = (int)((x.w[0] >> 16) & 0xFFFF) - 0x8000, lg = (int)(x.w[0] >> 8) & 1, cls = (int)(x.w[0] & 3),
                k = (int)(x.w[1] >> 54) & 7;
            i64 kx = (i64)(x.w[0] >> 32) - 1;
            if (kx >= 0) {
                int e0 = est;
                est += th + 1 - pv[c->base + kx];
                c->nun++;
                if (lg ? est <= O3H_LBAR(sl) : est <= -sl) {
                    c->ndrop++;
                    continue;
                }
                if (e0 > 0 && est == 0 && o3hq_skip_r(&x)) {
                    c->ndrop++;
                    continue;
                } /* --or3-eq-keep */
                c->nkept++;
            }
            c->byk[k]++;
            c->nlong += lg;
            u64 w0 = o3h_w0(cls, est), r1 = x.w[1] >> 36;
            if (!o3h_rlt(w0, r1, h->hi0, h->hi1) || o3h_rlt(w0, r1, h->lo0, h->lo1))
                continue;
            out[m].w[0] = w0;
            out[m].w[1] = x.w[1];
            out[m].w[2] = x.w[2];
            m++; /* never ahead of what is read */
        }
        c->nout = m;
    }
    for (int t = 0; t < h->nthr; t++)
        nadd += T[t].nout;
    o3hv_need(&h->sv, (size_t)(h->sn + nadd + 1) * sizeof(O3R));
    h->s = (O3R *)h->sv.p;
    o3h_mem(h);
    for (int t = 0; t < h->nthr; t++) {
        if (T[t].nout)
            memcpy(h->s + h->sn, T[t].raw, (size_t)T[t].nout * sizeof(O3R));
        h->sn += T[t].nout;
        T[t].nraw = T[t].nkey = 0;
    }
    free(pk);
    free(pv);
    if (h->sn > h->scap)
        o3h_cut(h);
}
/* the chains with lo <= rank, as many ranks as the store holds */
static void o3h_pass(O3H *h, u64 lo0, u64 lo1) {
    O3 *o = h->o;
    i64 N = o->N, next = 0;
    int nthr = h->nthr;
    double t0 = wall();
    h->lo0 = lo0;
    h->lo1 = lo1;
    h->hi0 = h->hi1 = ~0ULL;
    h->more = 0;
    h->sn = h->si = 0;
    h->npass++;
    if (h->sv.low)
        o3hv_open(&h->sv, (size_t)h->scap * 4 * sizeof(O3R));
    O3HT *T = calloc((size_t)nthr, sizeof(O3HT));
    if (!T)
        DIE("out of memory");
    for (int t = 0; t < nthr; t++) {
        T[t].cl = malloc((size_t)N + 2);
        T[t].kix = malloc((size_t)(N + 2) * sizeof(int));
        T[t].touch = malloc((size_t)(N + 2) * sizeof(int));
        if (!T[t].cl || !T[t].kix || !T[t].touch)
            DIE("out of memory");
        memset(T[t].cl, 255, (size_t)N + 2);
        for (i64 z = 0; z < N + 2; z++)
            T[t].kix[z] = -1;
        T[t].budget = o->budget / nthr;
        o3hv_open(&T[t].rv, (size_t)(h->rawcap + 4096) * sizeof(O3R));
    }
    while (next <= N) {
        h->rawn = 0;
#pragma omp parallel num_threads(nthr)
        {
            O3HT *t = &T[omp_get_thread_num()];
            int r[O3KM + 1], vv[O3KM + 1];
            const JG *in = &o->in;
            for (;;) {
                if (__atomic_load_n(&h->rawn, __ATOMIC_RELAXED) >= h->rawcap)
                    break;
                i64 i0 = __atomic_fetch_add(&next, 4, __ATOMIC_RELAXED), n0 = t->nraw;
                if (i0 > N)
                    break;
                for (i64 i = i0; i < i0 + 4 && i <= N; i++) {
                    i64 a = i - 1;
                    r[0] = (int)a;
                    int g = o3_old(o, a);
                    if (g <= -o->slack)
                        continue;
                    i64 y0 = a + 1, f0 = y0 < N ? in->off[y0] : 0, f1 = y0 < N ? in->off[y0 + 1] : 0;
                    for (i64 f = f0; f < f1; f++)
                        t->cl[in->to[f] + 1] = in->c[f];
                    o3h_dfs(h, t, r, vv, 0, g);
                    for (i64 f = f0; f < f1; f++)
                        t->cl[in->to[f] + 1] = 255;
                    for (int z = 0; z < t->ntouch; z++)
                        t->kix[t->touch[z]] = -1;
                    t->ntouch = 0;
                }
                __atomic_fetch_add(&h->rawn, t->nraw - n0, __ATOMIC_RELAXED);
            }
        }
        o3h_share(h, T);
    }
    {
        double t1 = wall();
        o3r_sort(h->s, h->sn);
        h->tsort += wall() - t1;
    }
    for (i64 i = 1; i < h->sn; i++)
        if (!O3R_LT(&h->s[i - 1], &h->s[i]))
            DIE("internal error: segment insertion (a chain found twice)");
    o3hv_trim(&h->sv, (size_t)(h->sn + 1) * sizeof(O3R));
    for (int t = 0; t < nthr; t++) {
        O3HT *c = &T[t];
        if (h->npass == 1) {
            h->nfound += c->nfound;
            h->ndup += c->ndup;
            h->nun += c->nun;
            h->nkept += c->nkept;
            h->nlong += c->nlong;
            for (int k = 0; k <= O3KM; k++) {
                h->byk[k] += c->byk[k];
                h->nchain += c->byk[k];
                o->nnode[k] += c->nnode[k];
            }
        }
        o->ntried += c->ntried;
        if (c->ntried > c->budget)
            h->over = 1;
        o3hv_close(&c->rv);
        free(c->key);
        free(c->cl);
        free(c->kix);
        free(c->touch);
    }
    free(T);
    h->tpass += wall() - t0;
}
/* ---- the two-pair moves.  The pairs as o3_cross makes them (a join that is not listed counts th + 1) */
#define O3HGEN(a, EMIT)                                                                                         \
    do {                                                                                                        \
        if ((a) < 0) {                                                                                          \
            for (i64 b_ = 0; b_ < N - 1; b_++) {                                                                \
                int v_ = o3_look(o, b_, 0);                                                                     \
                EMIT(-1, b_, o3_old(o, b_) - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0);                                \
            }                                                                                                   \
        } else {                                                                                                \
            for (i64 f_ = out->off[a]; f_ < out->off[(a) + 1]; f_++) {                                          \
                i64 b_ = (i64)out->to[f_] - 1;                                                                  \
                if (b_ > (a)) {                                                                                 \
                    int v_ = o3_look(o, b_, (a) + 1);                                                           \
                    EMIT(a, b_, o3_old(o, a) + o3_old(o, b_) - out->c[f_] - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0); \
                }                                                                                               \
            }                                                                                                   \
            {                                                                                                   \
                int v_ = o3_look(o, N - 1, (a) + 1);                                                            \
                EMIT(a, N - 1, o3_old(o, a) - (v_ < 0 ? U : v_), v_ < 0 ? 2 : 0);                               \
            }                                                                                                   \
            for (i64 f_ = in->off[(a) + 1]; f_ < in->off[(a) + 2]; f_++) {                                      \
                i64 b_ = in->to[f_];                                                                            \
                if (b_ > (a) && b_ < N - 1 && o3_look(o, a, b_ + 1) < 0)                                        \
                    EMIT(a, b_, o3_old(o, a) + o3_old(o, b_) - U - in->c[f_], 1);                               \
            }                                                                                                   \
        }                                                                                                       \
    } while (0)
static inline i64 o3h_lba(const O3X *X, i64 lo, i64 hi, i64 a) {
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (X[m].a < a)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
static inline i64 o3h_lbb(const O3X *Y, i64 lo, i64 hi, i64 b) {
    while (lo < hi) {
        i64 m = (lo + hi) >> 1;
        if (Y[m].b < b)
            lo = m + 1;
        else
            hi = m;
    }
    return lo;
}
/* the groups of equal e of kind q: gs[i] .. gs[i + 1] has e = emax - i */
static void o3h_groups(O3H *h, int q) {
    const O3X *X = h->X[q];
    i64 n = h->nx[q], at = 0;
    h->emax[q] = n ? X[0].e : 0;
    h->ngr[q] = n ? X[0].e - X[n - 1].e + 1 : 0;
    h->gs[q] = malloc((size_t)(h->ngr[q] + 2) * 8);
    if (!h->gs[q])
        DIE("out of memory");
    for (int i = 0; i <= h->ngr[q]; i++) {
        while (at < n && X[at].e > h->emax[q] - i)
            at++;
        h->gs[q][i] = at;
    }
    h->gs[q][h->ngr[q]] = n;
    h->ntop[q] = 0;
    while (h->ntop[q] < n && 2 * X[h->ntop[q]].e > h->bar[q])
        h->ntop[q]++;
}
/* A two-pair move made of the pairs x and y.  fill 0: counted by estimate and first cut.  fill 1: written,
   if its first cut lies in the window A0 .. A1. */
static inline void o3h_found(O3H *h, int q, int fill, u64 w0, i64 A0, i64 A1, const O3X *x, const O3X *y) {
    i64 ia = (i64)x->a + 1;
    if (!fill) {
        __atomic_fetch_add(&h->cnt[q][x->e + y->e - h->elo[q]][ia], 1, __ATOMIC_RELAXED);
        return;
    }
    if (ia < A0 || ia >= A1)
        return;
    i64 z = __atomic_fetch_add(&h->pos[ia - A0], 1, __ATOMIC_RELAXED);
    O3R *r = (O3R *)h->gv.p + z;
    int c[4] = {x->a, y->a, x->b, y->b};
    r->w[0] = w0;
    o3h_packm(r->w, 4, c, O3H_NXTP);
}
/* The moves of kind q: counted for every estimate and first cut (fill 0), or those with estimate E and first cut in
   A0 <= a + 1 < A1 written to their places (fill 1; w0: their class and estimate).  g is the pair with 2e above the
   bar: as the first pair it takes every pair that crosses it, as the second pair only those with 2e at or below
   the bar (for a narrow window those are looked for among the pairs that begin in the window).  Not long (kind 0, Z > 0): the crossing pair lies within Z of the first cut, or within Z before the
   third, or its own second cut lies within Z behind the third; the three cases do not overlap. */
static void o3h_tp(O3H *h, int q, int fill, int E, u64 w0, i64 A0, i64 A1) {
    const O3X *X = h->X[q], *Y = h->Y[q];
    const i64 *gs = h->gs[q];
    int bar = h->bar[q], emax = h->emax[q], ngr = h->ngr[q];
    i64 Z = h->Z, ng = h->ntop[q];
#pragma omp parallel for schedule(dynamic, 8) num_threads(h->nthr)
    for (i64 i = 0; i < ng; i++) {
        const O3X *g = &X[i];
        i64 ga = g->a, gb = g->b;
        for (int role = 0; role < 2; role++) {
            if (fill && (role ? ga + 1 <= A0 : ga + 1 < A0 || ga + 1 >= A1))
                continue; /* the first cut of the move must lie in the window */
            int i0 = 0, i1 = ngr;
            if (fill) {
                i0 = emax - (E - g->e);
                i1 = i0 + 1;
                if (i0 < 0 || i0 >= ngr)
                    continue;
            }
            for (int gi = i0; gi < i1; gi++) {
                int e = emax - gi;
                i64 s = gs[gi], e1 = gs[gi + 1];
                if (g->e + e <= bar)
                    break;
                if (role && 2 * e > bar)
                    continue; /* such a pair makes the move itself, as its first pair */
                if (s == e1)
                    continue;
                if (fill && role &&
                    A1 - A0 < (Z > 0 ? 3 * Z : gb - ga)) { /* g second, a narrow window: the pairs that begin in it */
                    i64 ahi = A1 - 1 < ga ? A1 - 1 : ga;
                    for (i64 j = o3h_lba(X, s, e1, A0 - 1); j < e1 && X[j].a < ahi; j++) {
                        i64 xa = X[j].a, xb = X[j].b;
                        int lg = Z > 0 && ga - xa >= Z && xb - ga >= Z && gb - xb >= Z;
                        if (xb <= ga || xb >= gb || (q ? !lg : lg))
                            continue;
                        o3h_found(h, q, fill, w0, A0, A1, &X[j], g);
                    }
                    continue;
                }
                if (q) { /* long: all three distances at least Z */
                    if (gb - ga < 2 * Z)
                        continue;
                    if (!role) {
                        for (i64 j = o3h_lba(X, s, e1, ga + Z); j < e1 && X[j].a <= gb - Z; j++)
                            if (X[j].b >= gb + Z)
                                o3h_found(h, q, fill, w0, A0, A1, g, &X[j]);
                    } else {
                        for (i64 j = o3h_lbb(Y, s, e1, ga + Z); j < e1 && Y[j].b <= gb - Z; j++)
                            if (Y[j].a <= ga - Z)
                                o3h_found(h, q, fill, w0, A0, A1, &Y[j], g);
                    }
                } else if (Z <= 0) {
                    if (!role) {
                        for (i64 j = o3h_lba(X, s, e1, ga + 1); j < e1 && X[j].a < gb; j++)
                            if (X[j].b > gb)
                                o3h_found(h, q, fill, w0, A0, A1, g, &X[j]);
                    } else {
                        for (i64 j = o3h_lbb(Y, s, e1, ga + 1); j < e1 && Y[j].b < gb; j++)
                            if (Y[j].a < ga)
                                o3h_found(h, q, fill, w0, A0, A1, &Y[j], g);
                    }
                } else if (!role) { /* g = (a, b) first; the other pair (c, d): a < c < b < d */
                    i64 m1 = ga + Z < gb ? ga + Z : gb, m2 = ga + Z > gb - Z + 1 ? ga + Z : gb - Z + 1;
                    for (i64 j = o3h_lba(X, s, e1, ga + 1); j < e1 && X[j].a < m1; j++)
                        if (X[j].b > gb)
                            o3h_found(h, q, fill, w0, A0, A1, g, &X[j]); /* c - a < Z */
                    for (i64 j = o3h_lba(X, s, e1, m2); j < e1 && X[j].a < gb; j++)
                        if (X[j].b > gb)
                            o3h_found(h, q, fill, w0, A0, A1, g, &X[j]); /* b - c < Z */
                    if (ga + Z <= gb - Z)
                        for (i64 j = o3h_lbb(Y, s, e1, gb + 1); j < e1 && Y[j].b < gb + Z; j++)
                            if (Y[j].a >= ga + Z && Y[j].a <= gb - Z)
                                o3h_found(h, q, fill, w0, A0, A1, g, &Y[j]); /* d - b < Z */
                } else { /* g = (c, d) second; the other pair (a, b): a < c < b < d */
                    i64 m1 = ga + Z < gb ? ga + Z : gb, m2 = ga + Z > gb - Z + 1 ? ga + Z : gb - Z + 1;
                    for (i64 j = o3h_lbb(Y, s, e1, ga + 1); j < e1 && Y[j].b < m1; j++)
                        if (Y[j].a < ga)
                            o3h_found(h, q, fill, w0, A0, A1, &Y[j], g); /* b - c < Z */
                    for (i64 j = o3h_lbb(Y, s, e1, m2); j < e1 && Y[j].b < gb; j++)
                        if (Y[j].a < ga)
                            o3h_found(h, q, fill, w0, A0, A1, &Y[j], g); /* d - b < Z */
                    if (ga + Z <= gb - Z)
                        for (i64 j = o3h_lba(X, s, e1, ga - Z + 1); j < e1 && X[j].a < ga; j++)
                            if (X[j].b >= ga + Z && X[j].b <= gb - Z)
                                o3h_found(h, q, fill, w0, A0, A1, &X[j], g); /* c - a < Z */
                }
            }
        }
    }
}
/* pairs, their exact values where long moves need them, and the count of the two-pair moves by estimate and first cut */
static void o3h_pairs(O3H *h) {
    O3 *o = h->o;
    i64 N = o->N, n = 0;
    int emax = -1000, U = o->th + 1, sl = o->slack, Z = h->Z;
    const JG *out = &o->out, *in = &o->in;
    O3X *X = NULL;
    double t0 = wall();
#pragma omp parallel for schedule(dynamic, 256) num_threads(h->nthr) reduction(max : emax)
    for (i64 a = -1; a < N - 1; a++) {
#define O3EM(A, B, E, W)   \
    do {                   \
        int e_ = (int)(E); \
        if (e_ > emax)     \
            emax = e_;     \
    } while (0)
        O3HGEN(a, O3EM);
#undef O3EM
    }
#pragma omp parallel num_threads(h->nthr)
    {
        O3X *L = NULL;
        i64 ln = 0, lcap = 0;
#pragma omp for schedule(dynamic, 256) nowait
        for (i64 a = -1; a < N - 1; a++) {
#define O3EM(A, B, E, W)                                    \
    do {                                                    \
        int e_ = (int)(E);                                  \
        if (e_ + emax > -sl) {                              \
            if (ln == lcap) {                               \
                lcap = lcap ? lcap * 2 : 1024;              \
                L = realloc(L, (size_t)lcap * sizeof(O3X)); \
                if (!L)                                     \
                    DIE("out of memory");                   \
            }                                               \
            L[ln].a = (int)(A);                             \
            L[ln].b = (int)(B);                             \
            L[ln].e = e_;                                   \
            L[ln].u = (W);                                  \
            ln++;                                           \
        }                                                   \
    } while (0)
            O3HGEN(a, O3EM);
#undef O3EM
        }
#pragma omp critical(o3hx)
        {
            X = realloc(X, (size_t)(n + ln + 1) * sizeof(O3X));
            if (!X)
                DIE("out of memory");
            if (ln)
                memcpy(X + n, L, (size_t)ln * sizeof(O3X));
            n += ln;
        }
        free(L);
    }
    h->bar[0] = -sl;
    h->bar[1] = O3H_LBAR(sl);
    h->cls[0] = o3order ? 2 : 0;
    h->cls[1] = 0;
    if (Z > 0) { /* the pairs wide enough for a long move, with exact V */
        i64 m = 0, nk = 0;
        int em = -1000, em2 = -1000;
        O3X *L;
        for (i64 i = 0; i < n; i++)
            if ((i64)X[i].b - X[i].a >= 2 * (i64)Z) {
                m++;
                if (X[i].e > em)
                    em = X[i].e;
            }
        L = malloc((size_t)(m + 1) * sizeof(O3X));
        if (!L)
            DIE("out of memory");
        m = 0;
        for (i64 i = 0; i < n; i++)
            if ((i64)X[i].b - X[i].a >= 2 * (i64)Z && X[i].e + em > h->bar[1]) {
                L[m++] = X[i];
                nk += X[i].u != 0;
            }
        if (o32pv && nk) {
            u64 *pk = malloc((size_t)(nk + 1) * 8);
            unsigned char *pv = malloc((size_t)nk + 1);
            if (!pk || !pv)
                DIE("out of memory");
            nk = 0;
            for (i64 i = 0; i < m; i++)
                if (L[i].u) {
                    int jx = L[i].u == 1 ? L[i].a : L[i].b, jy = (L[i].u == 1 ? L[i].b : L[i].a) + 1;
                    pk[nk++] = ((u64)(jx + 1) << 24) | (u64)jy;
                }
            o3h_values(o, &o->P, pk, nk, pv, &h->nphit);
            h->npv = nk;
            nk = 0;
            for (i64 i = 0; i < m; i++)
                if (L[i].u) {
                    L[i].e += U - pv[nk++];
                    L[i].u = 0;
                }
            free(pk);
            free(pv);
        }
        for (i64 i = 0; i < m; i++)
            if (L[i].e > em2)
                em2 = L[i].e;
        {
            i64 m2 = 0;
            for (i64 i = 0; i < m; i++)
                if (L[i].e + em2 > h->bar[1])
                    L[m2++] = L[i];
            m = m2;
        }
        h->X[1] = L;
        h->nx[1] = m;
    }
    h->X[0] = X;
    h->nx[0] = n;
    for (int q = 0; q < 2; q++) {
        if (!h->nx[q])
            continue;
        o3xa_sort(h->X[q], h->nx[q]);
        h->Y[q] = malloc((size_t)(h->nx[q] + 1) * sizeof(O3X));
        if (!h->Y[q])
            DIE("out of memory");
        memcpy(h->Y[q], h->X[q], (size_t)h->nx[q] * sizeof(O3X));
        o3xb_sort(h->Y[q], h->nx[q]);
        o3h_groups(h, q);
        h->tpair += wall() - t0;
        t0 = wall();
        h->elo[q] = h->bar[q] + 1;
        h->ne[q] = 2 * h->emax[q] - h->bar[q];
        if (h->ne[q] < 0 || !h->ntop[q])
            h->ne[q] = 0;
        if (!h->ne[q])
            continue;
        h->cnt[q] = calloc((size_t)h->ne[q], sizeof(u32 *));
        if (!h->cnt[q])
            DIE("out of memory");
        for (int e = 0; e < h->ne[q]; e++) {
            h->cnt[q][e] = calloc((size_t)N + 2, sizeof(u32));
            if (!h->cnt[q][e])
                DIE("out of memory");
        }
        o3h_tp(h, q, 0, 0, 0, 0, 0);
        h->tcount += wall() - t0;
        t0 = wall();
    }
    o->nnode[O3KM + 1] = h->ntop[0];
    /* the estimates that have moves, by class and falling estimate */
    h->tb = calloc((size_t)(h->ne[0] + h->ne[1] + 1), sizeof(O3HB));
    if (!h->tb)
        DIE("out of memory");
    for (int q = 0; q < 2; q++)
        for (int e = h->ne[q] - 1; e >= 0; e--) {
            i64 tot = 0;
            for (i64 a = 0; a <= N; a++)
                tot += h->cnt[q][e][a];
            if (!tot) {
                free(h->cnt[q][e]);
                h->cnt[q][e] = NULL;
                continue;
            }
            h->ntp[q] += tot;
            u64 w0 = o3h_w0(h->cls[q], h->elo[q] + e);
            int z = 0;
            while (z < h->ntb && h->tb[z].w0 != w0)
                z++;
            if (z == h->ntb) {
                int at = h->ntb++;
                while (at > 0 && h->tb[at - 1].w0 > w0) {
                    h->tb[at] = h->tb[at - 1];
                    at--;
                }
                memset(&h->tb[at], 0, sizeof(O3HB));
                h->tb[at].w0 = w0;
                z = at;
            }
            h->tb[z].kind[h->tb[z].nk] = q;
            h->tb[z].ei[h->tb[z].nk++] = e;
            h->tb[z].tot += tot;
        }
    h->pos = malloc((size_t)(N + 3) * 8);
    h->off = malloc((size_t)(N + 3) * 8);
    if (!h->pos || !h->off)
        DIE("out of memory");
}
/* the next first cut (ti, ta) that has two-pair moves; 0: none */
static int o3h_seek(O3H *h) {
    for (; h->ti < h->ntb; h->ti++, h->ta = 0) {
        const O3HB *b = &h->tb[h->ti];
        for (; h->ta <= h->N; h->ta++)
            for (int z = 0; z < b->nk; z++)
                if (h->cnt[b->kind[z]][b->ei[z]][h->ta])
                    return 1;
    }
    return 0;
}
/* the next piece of the list: h->g[0 .. gn-1]; 0: the list is at its end */
static int o3h_segment(O3H *h) {
    i64 N = h->N;
    double t0 = wall();
    h->gi = h->gn = 0;
    if (!h->vfy)
        o3hv_drop(&h->sv, (size_t)h->si * sizeof(O3R));
    for (;;) {
        if (h->si >= h->sn && h->more)
            o3h_pass(h, h->hi0, h->hi1);
        int hc = h->si < h->sn, ht = o3h_seek(h);
        if (!hc && !ht)
            return 0;
        u64 t0w = ht ? h->tb[h->ti].w0 : 0, t1w = ht ? ((u64)4 << 18) | (u64)h->ta : 0;
        if (hc && (!ht || o3h_rlt(h->s[h->si].w[0], O3H_R1(&h->s[h->si]), t0w,
                                  t1w))) { /* chains only, as they lie in the store */
            i64 lim = h->si + (1 << 20) < h->sn ? h->si + (1 << 20) : h->sn, e = lim;
            if (ht) {
                i64 lo = h->si, hi = lim;
                while (lo < hi) {
                    i64 m = (lo + hi) >> 1;
                    if (o3h_rlt(h->s[m].w[0], O3H_R1(&h->s[m]), t0w, t1w))
                        lo = m + 1;
                    else
                        hi = m;
                }
                e = lo;
            }
            h->g = h->s + h->si;
            h->gn = e - h->si;
            h->si = e;
            h->nseg++;
            return 1;
        }
        /* a window of first cuts of the estimate tb[ti]: its two-pair moves and the chains of four cuts that lie among them */
        const O3HB *b = &h->tb[h->ti];
        i64 a0 = h->ta, a1 = a0, tot = 0, sc = h->si, nch = 0;
        for (; a1 <= N && (a1 == a0 || tot < h->segmax); a1++) {
            u64 r1 = ((u64)4 << 18) | (u64)a1;
            i64 c = 0;
            if (h->more && !o3h_rlt(b->w0, r1, h->hi0, h->hi1))
                break; /* the chains from here on are not in the store yet */
            for (int z = 0; z < b->nk; z++)
                c += h->cnt[b->kind[z]][b->ei[z]][a1];
            while (sc < h->sn && h->s[sc].w[0] == b->w0 && O3H_R1(&h->s[sc]) == r1) {
                sc++;
                c++;
            }
            h->off[a1 - a0] = tot;
            tot += c;
        }
        h->off[a1 - a0] = tot;
        nch = sc - h->si;
        if (a1 == a0)
            DIE("internal error: segment insertion (a window without a first cut)");
        o3hv_need(&h->gv, (size_t)(tot + 1) * sizeof(O3R));
        o3h_mem(h);
        O3R *gb = (O3R *)h->gv.p;
        for (i64 a = a0; a < a1; a++)
            h->pos[a - a0] = h->off[a - a0];
        for (i64 z = h->si; z < sc; z++) {
            i64 a = (i64)(O3H_R1(&h->s[z]) & O3H_M18);
            gb[h->pos[a - a0]++] = h->s[z];
        }
        for (int z = 0; z < b->nk; z++)
            o3h_tp(h, b->kind[z], 1, h->elo[b->kind[z]] + b->ei[z], b->w0, a0, a1);
        for (i64 a = a0; a < a1; a++)
            if (h->pos[a - a0] != h->off[a - a0 + 1])
                DIE("internal error: segment insertion (two-pair moves of the cut %lld: %lld counted, %lld made)",
                    a - 1, h->off[a - a0 + 1] - h->off[a - a0], h->pos[a - a0] - h->off[a - a0]);
#pragma omp parallel for schedule(dynamic, 16) num_threads(h->nthr)
        for (i64 a = a0; a < a1; a++) {
            i64 m = h->off[a - a0 + 1] - h->off[a - a0];
            if (m > 1)
                o3r_sort_1(gb + h->off[a - a0], m);
        }
        for (i64 i = 1; i < tot; i++)
            if (!O3R_LT(&gb[i - 1], &gb[i]))
                DIE("internal error: segment insertion (a move twice in a window)");
        h->g = gb;
        h->gn = tot;
        h->si = sc;
        h->ta = a1;
        h->nseg++;
        h->nfill += tot - nch;
        h->tfill += wall() - t0;
        (void)nch;
        return 1;
    }
}
static inline int o3h_next(O3H *h, O3R *r) {
    if (h->gi >= h->gn && !o3h_segment(h))
        return 0;
    *r = h->g[h->gi++];
    return 1;
}
static void o3h_rewind(O3H *h) {
    if (h->lo0 || h->lo1)
        o3h_pass(h, 0, 0);
    h->si = 0;
    h->ti = 0;
    h->ta = 0;
    h->gi = h->gn = 0;
}
/* Called by o3_prepare when the tables, the pairs and the threads' tables are ready (t3).  1: the candidates of this
   round come from here (o->nall of them; o->mv is not made). */
static int o3h_begin(O3 *o, double t3) {
    O3H *h = &o3h;
    i64 N = o->N;
    o3h_close(h);
    if (o3h_mb <= 0 || o3old || o3check || o->dstart || N + 2 >= (1 << 18) || N >= (1 << 24) || (O3H_OTHER_LISTS))
        return 0;
    memset(h, 0, sizeof *h);
    h->o = o;
    h->N = N;
    h->Z = o3_longz > 0 ? o3_longz : 0;
    h->sl = o->slack;
    h->th = o->th;
    h->nthr = NTHR;
    i64 M = o3h_mb << 20;
    h->scap = M / 2 / (i64)sizeof(O3R);
    h->segmax = M / 4 / (i64)sizeof(O3R);
    h->rawcap = M / 8 / (i64)sizeof(O3R);
    if (h->scap < 4096)
        h->scap = 4096;
    if (h->segmax < 4096)
        h->segmax = 4096;
    if (h->rawcap < 4096)
        h->rawcap = 4096;
    if (o3h_rec > 0) {
        h->scap = o3h_rec;
        h->segmax = h->rawcap = o3h_rec / 2 + 1;
    }
    o3hv_open(&h->sv, (size_t)h->scap * 4 * sizeof(O3R));
    o3hv_open(&h->gv, (size_t)h->segmax * 4 * sizeof(O3R));
    o3hq_pre(o);
    for (int d = 0; d <= O3KM + 1; d++)
        o->nnode[d] = 0;
    o->ntried = 0;
    o->nc = 0;
    o3h_pass(h, 0, 0);
    o3hq_post(o, o3h_chk);
    double t4 = wall();
    if (o->kc >= 4)
        o3h_pairs(h);
    double t5 = wall();
    h->nall = h->nchain + h->ntp[0] + h->ntp[1];
    h->byk[4] += h->ntp[0] + h->ntp[1];
    o->nall = h->nall;
    o->nc = o3maxcand > 0 && h->nall > o3maxcand ? o3maxcand : h->nall;
    i64 nbat = o->nc;
    if (o->nc > O3H_NCMEMO)
        o->nc = O3H_NCMEMO;
    if (h->over)
        printf("segment insertion: the search for candidates was cut short\n");
    if (!o->quiet || o3dry) {
        printf("segment insertion (th %d, slack %d): chains by number of joins:", o->th, o->slack);
        for (int d = 0; d < o->kc; d++)
            printf(" %lld", o->nnode[d]);
        if (o->kc >= 4)
            printf(", %lld pairs for two pairs", o->nnode[O3KM + 1]);
        printf(
            "; %lld moves, %lld different (%.1fs); %lld joins not listed, %lld valued (%lld known from earlier rounds), %lld moves kept (%.1fs); %lld candidates",
            h->nfound + h->ntp[0] + h->ntp[1], h->nfound - h->ndup + h->ntp[0] + h->ntp[1], t4 - t3, h->nun, h->nval,
            h->nhit, h->nkept, t5 - t4, h->nall);
        if (o3_longz > 0)
            printf(
                ", %lld of the candidates found were long (%d events and more between the cuts), %lld of those with an estimate of 0 or less%s",
                h->nlong + h->ntp[1], o3_longz, 0LL, " left out");
        if (nbat < h->nall)
            printf(", in batches of %lld", nbat);
        printf(" (");
        for (int k = 3; k <= o->kc; k++)
            printf("%s%lld with %d cuts", k > 3 ? ", " : "", h->byk[k], k);
        printf(")\n");
        printf(
            "segment insertion: the candidates are made as the round needs them (room %lld MB): %lld chains (%lld in the store%s; search %.1fs, of that values %.1fs, sorting %.1fs)",
            o3h_mb, h->nchain, h->sn, h->more ? ", the rest by another search" : "", h->tpass, h->tval, h->tsort);
        if (o->kc >= 4)
            printf(
                "; %lld + %lld pairs (%.1fs), %lld two-pair moves that are not long and %lld long ones counted (%.1fs), %lld joins of pairs valued (%lld known)",
                h->nx[0], h->nx[1], h->tpair, h->ntp[0], h->ntp[1], h->tcount, h->npv, h->nphit);
        {
            i64 cn, cp;
            o3h_commit(&cn, &cp);
            printf("; the process has %lld MB committed, %lld MB at its peak", cn, cp);
        }
        printf("\n");
        fflush(stdout);
    }
    h->act = 1;
    if (o3h_chk) {
        h->vfy = 1;
        return 0;
    }
    return 1;
}
/* --or3-hcheck: o->mv is the one list; the list made here must be the same, candidate by candidate */
static void o3h_verify(O3 *o) {
    O3H *h = &o3h;
    O3R r;
    O3M m;
    i64 n = 0, bad = 0;
    if (!h->act || !h->vfy)
        return;
    if (h->nall != o->nall) {
        printf("or3-hcheck: %lld candidates here, %lld in the old list (MISMATCH)\n", h->nall, o->nall);
        bad++;
    }
    while (o3h_next(h, &r)) {
        o3h_unpack(r.w, O3H_EST(r.w[0]), &m);
        if (n < o->nall) {
            const O3M *x = &o->mv[n];
            int d = x->k != m.k || x->est != m.est || x->lg != m.lg || x->tp != m.tp;
            for (int i = 0; i < O3KM; i++)
                d |= x->c[i] != m.c[i] || x->nx[i] != m.nx[i];
            if (d && bad++ < 10) {
                printf("or3-hcheck: candidate %lld differs (MISMATCH): old est %d lg %d tp %d ", n, x->est, x->lg,
                       x->tp);
                o3_print(NULL, x, o->N);
                printf("; new est %d lg %d tp %d ", m.est, m.lg, m.tp);
                o3_print(NULL, &m, o->N);
                printf("\n");
            }
        }
        n++;
    }
    if (n != o->nall)
        bad++;
    printf("or3-hcheck: %lld candidates in the old list, %lld made here, %lld differences%s\n", o->nall, n, bad,
           bad ? " (MISMATCH)" : "");
    fflush(stdout);
    if (bad)
        DIE("or3-hcheck: the two lists of candidates differ");
    o3h_rewind(h);
    h->nseg = h->nfill = 0;
    h->tfill = 0;
    h->vfy = 0;
}
/* Tables, pairs and candidates of ev: o->mv[0 .. nc-1], by falling estimate (--or3-old: by the move), not yet judged */
static void o3_prepare(O3 *o, const Ev *ev) {
    double t1 = wall();
    i64 N = o->N, ng[5] = {0}, hist[16] = {0}, vh[18] = {0}, more = 0, maxm = 0;
    int *old = o->old, th = o->th, sl = o->slack;
    POT *P = &o->P;
    int kept = o->pvalid, same = kept && o->lkeep && o->out.off,
        upd = kept && !same && o->lvalid && o->out.off && !o3old && !o3nolu;
    JG out0, in0;
    i64 sh[4] = {0};
    if (upd) {
        o3_share(&o->P, N, th, o->lperm, o->lchgF, o->lchgB, sh);
        if ((sh[2] + sh[3]) * 100 > (i64)o3lupct * (sh[0] + sh[1]))
            upd = 0;
    }
    out0 = o->out;
    in0 = o->in;
    if (upd || same)
        memset(&o->out, 0, sizeof o->out); /* the lists of the round before: o3_vupdate needs them, or they stay */
    if (same)
        memset(&o->in, 0, sizeof o->in);
    o3_clear(o);
    o->ev = ev;
    o->tprep = t1;
    o->round++;
    o->vhit = 0;
    o->lvalid = 0;
    o->lkeep = 0;
    if (!kept && o->vc) {
        for (u64 z = 0; z <= o->vcmask; z++)
            o->vc[z].key = ~0ULL;
        o->vcn = 0;
    } /* new tables: nothing kept holds */
    if (!kept && o->jc) {
        for (u64 z = 0; z <= o->jcmask; z++)
            o->jc[z].key = ~0ULL;
        o->jcn = 0;
    }
    o->jhit = 0;
    if (!kept)
        o3_pot(ev, N, P);
    o->pvalid = 0;
    double t2 = wall();
    if (!o->quiet) {
        printf("segment insertion, round %d (%.0fs): costs of %lld openings from both ends, %s%.1fs\n", o3_nround + 1,
               O3NOW(), P->off[N], kept ? "kept from the round before, " : "", t2 - t1);
        fflush(stdout);
    }
    og_round(o);
    for (i64 i = 0; i < N; i++) {
        old[i] = i + 1 < N ? (int)(P->fmin[N - 1] - P->fmin[i] - P->gmin[i + 1]) : 0;
        if (i + 1 < N) {
            vh[old[i] <= h ? old[i] : h]++;
            more += old[i] > dist(ev[i].e, ev[i + 1].s);
        }
        if (P->off[i + 1] - P->off[i] > maxm)
            maxm = P->off[i + 1] - P->off[i];
    }
    if (o->round == 1 && !o->quiet) { /* how the cuts are spread over the events */
        int *sz = malloc((size_t)(N + 1) * sizeof(int));
        i64 half = 0, n10 = 0, cum = 0;
        if (!sz)
            DIE("out of memory");
        for (i64 i = 0; i < N; i++)
            sz[i] = (int)(P->off[i + 1] - P->off[i]);
        qsort(sz, (size_t)N, sizeof(int), int_cmp);
        for (i64 i = N - 1; i >= 0; i--) {
            if (2 * cum < P->off[N])
                half++;
            if (10 * cum < P->off[N])
                n10++;
            cum += sz[i];
        }
        printf(
            "segment insertion: %lld events, the largest with %lld openings, the median with %d; the %lld largest have a tenth of all openings, the %lld largest half\n",
            N, maxm, sz[N / 2], n10, half);
        fflush(stdout);
        free(sz);
    }
    char *xl = NULL, *xr = NULL;
    int th2 = h - 1, xt = o3xt;
    i64 nx = 0;
    if (!o3old && xt > 0 && th2 > th) { /* the expensive joins: long lists between their sides (and the two ends) */
        for (; xt <= h; xt++) {
            nx = 0;
            for (int v = xt; v <= h; v++)
                nx += vh[v];
            if (nx <= O3XMAX)
                break;
        }
        xl = calloc((size_t)N + 1, 1);
        xr = calloc((size_t)N + 1, 1);
        if (!xl || !xr)
            DIE("out of memory");
        for (i64 i = 0; i + 1 < N; i++)
            if (old[i] >= xt)
                xl[i] = xr[i + 1] = 1;
        xr[0] = xl[N - 1] = 1;
    }
    if (same) {
        o->out = out0;
        o->in = in0;
    } else if (upd) {
        o3_vupdate(ev, N, P, th, xl, xr, th2, &out0, o->lperm, o->lchgF, o->lchgB, &o->out, &o->in, ng);
        free(out0.off);
        free(out0.to);
        free(out0.c);
        if (o3check) { /* against lists made from nothing */
            JG fo, fi;
            i64 g2[3];
            o3_vbuild(ev, N, P, th, 0, xl, xr, th2, &fo, &fi, g2);
            if (!o3_jg_same(&fo, &o->out, N) || !o3_jg_same(&fi, &o->in, N))
                DIE("internal error: segment insertion (the pairs kept differ from new ones)");
            printf("segment insertion: pairs checked against new ones\n");
            free(fo.off);
            free(fo.to);
            free(fo.c);
            free(fi.off);
            free(fi.to);
            free(fi.c);
        }
    } else
        o3_vbuild(ev, N, P, th, o3old, xl, xr, th2, &o->out, &o->in, ng);
    for (i64 e = 0; e < o->out.off[N]; e++)
        hist[o->out.c[e] & 15]++;
    double t3 = wall();
    if (!o->quiet) {
        if (same)
            printf("segment insertion: the pairs of the round before; %lld pairs of events with V <= %d", o->out.off[N],
                   th);
        else if (upd)
            printf(
                "segment insertion: pairs brought up to date for %lld events with new costs from the front (%lld openings within %d) and %lld from the back (%lld), tables %.1fs, lists %.1fs, turned round %.1fs; %lld pairs of events with V <= %d",
                ng[0], ng[3], th, ng[1], ng[4], o3_lu_t[0], o3_lu_t[1], o3_lu_t[2], o->out.off[N], th);
        else {
            if (sh[0] + sh[1] > 0)
                printf(
                    "segment insertion: the events with new costs have %.0f%% of the openings within %d: pairs made new\n",
                    100.0 * (sh[2] + sh[3]) / (sh[0] + sh[1]), th);
            printf(
                "segment insertion: %lld openings within %d of the best before them, %lld after them; %lld pairs of events with V <= %d",
                ng[0], th, ng[1], o->out.off[N], th);
        }
        if (xl)
            printf(" or between the %lld joins with V >= %d", nx, xt);
        printf(" (");
        for (int c = 0, f = 0; c < 16; c++)
            if (hist[c])
                printf("%s%d: %lld", f++ ? ", " : "", c, hist[c]);
        printf("); present joins by V:");
        for (int c = 0; c <= h; c++)
            if (vh[c])
                printf(" %d:%lld", c, vh[c]);
        printf(" (%lld above their cost); %lld entries looked at, %.1fs\n", more, ng[2], t3 - t2);
        fflush(stdout);
    }
    free(xl);
    free(xr);
    /* one set of tables for every thread that judges */
    o->ntc = NTHR;
    o->tc = calloc((size_t)o->ntc, sizeof(O3T));
    if (!o->tc)
        DIE("out of memory");
    for (int t = 0; t < o->ntc; t++) {
        O3T *c = &o->tc[t];
        bs_init(&c->b, &c->qb, 1);
        c->b.anyskip = 0;
        c->b.ev = ev;
        c->b.N = N;
        free(c->b.ec);
        c->b.ecn = 64;
        c->b.ec = calloc((size_t)c->b.ecn, sizeof(BEv));
        c->T0 = malloc((size_t)maxm + 1);
        c->T1 = malloc((size_t)maxm + 1);
        if (!c->b.ec || !c->T0 || !c->T1)
            DIE("out of memory");
        for (int k = 0; k < c->b.ecn; k++)
            c->b.ec[k].id = -1;
    }
    if (o3h_ctx && o3h_begin(o, t3))
        return; /* the candidates in bounded memory: o->mv is not made */
    free(o->sv);
    o->sv = NULL;
    o->sn = o->scap = 0;
    o->nc = o->ntried = 0;
    o3q_scan(o);
    if (o->ntried > o->budget)
        printf("segment insertion: the search for candidates was cut short\n");
    i64 nraw = o->sn, npend = 0, nval = 0, nkept = 0;
    qsort(o->sv, (size_t)o->sn, sizeof(O3S), o3sk_cmp);
    {
        i64 m = 0;
        for (i64 k = 0; k < o->sn; k++)
            if (!k || o3sk_cmp(&o->sv[k], &o->sv[k - 1]))
                o->sv[m++] = o->sv[k];
        o->sn = m;
    }
    double t4 = wall();
    i64 ndiff = o->sn;
    /* joins that are not listed: their V from the tables */
    i64 npc = 0;
    for (i64 k = 0; k < o->sn; k++) {
        npend += (o->sv[k].ux > -2) + (o->sv[k].ux2 > -2);
        npc += o->sv[k].ux > -2 || o->sv[k].ux2 > -2;
    }
    if (npend && !o3dry) {
        i64 dv = 0, nv = 0, nh = 0;
        if (o3_longz > 0 && npend > 20000) {
            dv += o3_value(o, P, 8, &nv, &nh);
            nval += nv;
            o->vhit += nh;
        }
        dv += o3_value(o, P, 1, &nv, &nh);
        nval += nv;
        o->vhit += nh;
        nkept = npc - dv;
    }
    i64 nlong = 0, nlow = 0;
    if (o3_longz > 0 && !o3dry && !o3old) { /* a long candidate gains what its estimate says: 0 or less is not judged */
        i64 m = 0;
        for (i64 k = 0; k < o->sn; k++) {
            O3S *c = &o->sv[k];
            if (c->lg) {
                nlong++;
                if (c->est <= 0) {
                    nlow++;
                    if (!o3check && c->est <= o3q_lbar(sl))
                        continue;
                }
            }
            o->sv[m++] = *c;
        }
        o->sn = m;
    }
    /* the candidates in full */
    o->nc = o->sn;
    if (o->nc > o->cap) {
        o->cap = o->nc + 16;
        free(o->mv);
        o->mv = malloc((size_t)o->cap * sizeof(O3M));
        if (!o->mv)
            DIE("out of memory");
    }
    for (i64 k = 0; k < o->nc; k++) {
        O3M *m = &o->mv[k];
        const O3S *c = &o->sv[k];
        memset(m, 0, sizeof *m);
        m->k = c->k;
        m->est = c->est;
        m->ux = c->ux;
        m->uy = c->uy;
        m->ux2 = c->ux2;
        m->uy2 = c->uy2;
        m->lg = c->lg;
        m->tp = c->tp;
        for (int i = 0; i < O3KM; i++) {
            m->c[i] = c->c[i];
            m->nx[i] = c->nx[i];
        }
    }
    free(o->sv);
    o->sv = NULL;
    o->sn = o->scap = 0;
    if (!o3old && o->nc)
        qsort(o->mv, (size_t)o->nc, sizeof(O3M), o3e_cmp);
    i64 nall = o->nc;
    if (!o3old && o3maxcand > 0 && o->nc > o3maxcand)
        o->nc = o3maxcand;
    double t5 = wall();
    i64 byk[O3KM + 1] = {0};
    o->nall = nall;
    for (i64 k = 0; k < nall; k++) {
        byk[o->mv[k].k]++;
        o->mv[k].gx = O3BAD;
    }
    if (!o->quiet || o3dry) {
        printf("segment insertion (th %d, slack %d): chains by number of joins:", th, sl);
        for (int d = 0; d < o->kc; d++)
            printf(" %lld", o->nnode[d]);
        if (o->kc >= 4)
            printf(", %lld pairs for two pairs", o->nnode[O3KM + 1]);
        if (o->dstart)
            printf(", only from the %lld cuts near the last moves", o->nstart);
        printf(
            "; %lld moves, %lld different (%.1fs); %lld joins not listed, %lld valued (%lld known from earlier rounds), %lld moves kept (%.1fs); %lld candidates",
            nraw, ndiff, t4 - t3, npend, nval, o->vhit, nkept, t5 - t4, nall);
        if (o3_longz > 0)
            printf(
                ", %lld of the candidates found were long (%d events and more between the cuts), %lld of those with an estimate of 0 or less%s",
                nlong, o3_longz, nlow,
                o3check            ? ""
                : o3q_lbar(sl) < 0 ? " (those below 0 left out, those with 0 stay for the draw)"
                                   : " left out");
        if (o->nc < nall)
            printf(", in batches of %lld", o->nc);
        printf(" (");
        for (int k = 3; k <= o->kc; k++)
            printf("%s%lld with %d cuts", k > 3 ? ", " : "", byk[k], k);
        printf(")\n");
        fflush(stdout);
    }
    if (o3h_ctx)
        o3h_verify(o); /* --or3-hcheck */
}
/* the exact gains of the candidates idx[0 .. n-1]; fwd: with their zones.  Without fwd a gain that is kept from an
   earlier round and still holds is taken (--or3-check: and computed again, and compared). */
static void o3_judge(O3 *o, const i64 *idx, i64 n, int fwd) {
    int keep = !fwd && o->eid && o->lastJ && !o3nojc;
    u64 *key = NULL;
    i64 *todo = NULL, nt = n;
    int *was = NULL;
    if (keep) {
        key = malloc((size_t)(n + 1) * 8);
        todo = malloc((size_t)(n + 1) * 8);
        was = malloc((size_t)(n + 1) * sizeof(int));
        if (!key || !todo || !was)
            DIE("out of memory");
        nt = 0;
        for (i64 q = 0; q < n; q++) {
            O3M *m = &o->mv[idx[q]];
            key[q] = o3_jkey(o, m);
            const O3J *e = o3_jc_find(o, key[q]);
            was[q] = 1 << 30;
            if (e && o3_jc_ok(o, m, e)) {
                o->jhit++;
                if (o3check)
                    was[q] = e->gx;
                else {
                    m->gx = e->gx;
                    key[q] = ~0ULL;
                    continue;
                }
            }
            todo[nt++] = q;
        }
    }
    if (og_use(nt)) {
        if (todo) {
            i64 *ix = malloc((size_t)(nt + 1) * 8);
            if (!ix)
                DIE("out of memory");
            for (i64 q = 0; q < nt; q++)
                ix[q] = idx[todo[q]];
            og_judge(o, ix, nt, fwd);
            free(ix);
        } else
            og_judge(o, idx, nt, fwd);
    } else
#pragma omp parallel for schedule(dynamic, 1) num_threads(NTHR)
        for (i64 q = 0; q < nt; q++) {
            O3T *c = &o->tc[omp_get_thread_num()];
            O3M *m = &o->mv[idx[todo ? todo[q] : q]];
            i64 g = o3_gain(&c->b, &o->P, o->N, m, c->T0, c->T1, &o->memo, c->st, fwd);
            if (fwd && m->gx != O3BAD && g != O3BAD && g != m->gx)
                DIE("internal error: segment insertion (gain %lld, with its zones %lld)", m->gx, g);
            m->gx = g;
        }
    if (keep) {
        for (i64 q = 0; q < n; q++)
            if (key[q] != ~0ULL) {
                O3M *m = &o->mv[idx[q]];
                if (was[q] != 1 << 30 && m->gx != was[q])
                    DIE("internal error: segment insertion (a gain kept from an earlier round is %d, now %lld)", was[q],
                        m->gx);
                o3_jc_put(o, key[q], m);
            }
        free(key);
        free(todo);
        free(was);
    }
}
/* Adds up the counters of the search threads (st[1] is their maximum). */
static void o3_stats(const O3 *o, i64 *st) {
    for (int k = 0; k < 4; k++)
        st[k] = 0;
    for (int t = 0; t < o->ntc; t++) {
        const i64 *s = o->tc[t].st;
        st[0] += s[0];
        if (s[1] > st[1])
            st[1] = s[1];
        st[2] += s[2];
        st[3] += s[3];
    }
}
/* all candidates of ev with their exact gains, the best first; returns the best gain (0: none) */
static i64 o3_round(O3 *o, const Ev *ev) {
    o3_prepare(o, ev);
    if (o3dry)
        return 0;
    double t5 = wall(), tlast = t5;
    i64 N = o->N, npos = 0, nzero = 0, gh[5] = {0}, best = 0, st[4], nbad = 0, njud = 0;
    int sl = o->slack;
    i64 ch = og_chunk(), *idx = malloc((size_t)ch * 8);
    if (!idx)
        DIE("out of memory");
    for (i64 a = 0; a < o->nc; a += ch) { /* in pieces, so that the time limit is seen */
        if (o3sec > 0 && O3NOW() > o3sec)
            break;
        i64 n = o->nc - a < ch ? o->nc - a : ch;
        for (i64 q = 0; q < n; q++)
            idx[q] = a + q;
        o3_judge(o, idx, n, 0);
        njud += n;
        if (!o->quiet && wall() - tlast > 60) {
            tlast = wall();
            printf("segment insertion: %lld of %lld candidates judged (%.0fs)\n", njud, o->nc, tlast - t5);
            fflush(stdout);
        }
    }
    free(idx);
    og_round_report();
    /* what the shorter ones look like: by estimate, and by the largest V of their new joins */
    i64 et[2][24], vt[2][20];
    memset(et, 0, sizeof et);
    memset(vt, 0, sizeof vt);
    for (i64 k = 0; k < njud; k++) {
        const O3M *c = &o->mv[k];
        i64 g = c->gx;
        int mxv = 0, nu = 0, e = c->est + sl;
        if (e < 0)
            e = 0;
        if (e > 23)
            e = 23;
        if (g == O3BAD) {
            nbad++;
            continue;
        }
        if (g > 0)
            npos++;
        if (g == 0)
            nzero++;
        if (g >= -4 && g < 0)
            gh[-g]++;
        for (int i = 0; i < c->k; i++) {
            i64 x = c->c[i], y = (i64)c->c[c->nx[i]] + 1;
            int v = x < 0 || y >= N ? 0 : o3_look(o, x, y);
            if (v < 0)
                nu++;
            else if (v > mxv)
                mxv = v;
        }
        et[0][e]++;
        vt[0][nu ? 15 + (nu > 3 ? 3 : nu) : mxv]++;
        if (g > 0) {
            et[1][e]++;
            vt[1][nu ? 15 + (nu > 3 ? 3 : nu) : mxv]++;
        }
    }
    if (o->nc)
        qsort(o->mv, (size_t)o->nc, sizeof(O3M), o3m_cmp);
    if (o->nc && o->mv[0].gx != O3BAD)
        best = o->mv[0].gx;
    o3_stats(o, st);
    if (!o->quiet) {
        printf("segment insertion: shorter / judged by estimate:");
        for (int e = 0; e < 24; e++)
            if (et[0][e])
                printf(" %d: %lld/%lld", e - sl, et[1][e], et[0][e]);
        printf("; by the largest V of the new joins:");
        for (int v = 0; v < 15; v++)
            if (vt[0][v])
                printf(" %d: %lld/%lld", v, vt[1][v], vt[0][v]);
        for (int u = 1; u <= 3; u++)
            if (vt[0][15 + u])
                printf(" %d not listed: %lld/%lld", u, vt[1][15 + u], vt[0][15 + u]);
        printf(
            "\nsegment insertion: %lld judged: %lld shorter, %lld equal, one to four longer: %lld %lld %lld %lld; best gain %lld; %.1f layers per candidate, at most %lld after one join, %lld joins computed, %lld from the memo",
            njud, npos, nzero, gh[1], gh[2], gh[3], gh[4], best, njud ? (double)st[0] / njud : 0.0, st[1], st[2],
            st[3]);
        if (nbad)
            printf(", %lld given up", nbad);
        if (njud < o->nc)
            printf(", %lld not judged (time)", o->nc - njud);
        printf(" (%.1fs; round %.1fs)\n", wall() - t5, wall() - o->tprep);
        fflush(stdout);
    }
    return best > 0 ? best : 0;
}
/* Several moves at once.  Every move says which stretch follows each of its cuts; all cuts are different.  Returns 0
   if the stretches do not come out as one sequence; with ev2 the new sequence is written (only for a set that
   has been tested), and slo, shi get the stretches in their new order (old first and last event; room for all
   cuts + 1).  cut: room for all cuts; nxt: as many ints. */
typedef struct {
    int c, nx;
} O3Cut;
static int o3cut_cmp(const void *a, const void *b) {
    int x = ((const O3Cut *)a)->c, y = ((const O3Cut *)b)->c;
    return x < y ? -1 : x > y;
}
/* Several moves at once (see the comment above the type O3Cut): 0 if their blocks do not form one sequence. */
static int o3_compose(const O3M *mv, i64 n, const O3M *extra, i64 N, const Ev *ev, Ev *ev2, O3Cut *cut, int *nxt,
                      i64 *slo, i64 *shi, i64 *nstr) {
    i64 K = 0, cnt = 0, at = 0, s = 0, m2 = 0;
    for (i64 q = 0; q < n + (extra != NULL); q++) {
        const O3M *m = q < n ? &mv[q] : extra;
        for (int i = 0; i < m->k; i++) {
            cut[K].c = m->c[i];
            cut[K].nx = m->c[m->nx[i]];
            K++;
        }
    }
    qsort(cut, (size_t)K, sizeof(O3Cut), o3cut_cmp);
    for (i64 i = 0; i < K; i++) {
        i64 a = 0, z = K;
        while (a < z) {
            i64 mid = (a + z) >> 1;
            if (cut[mid].c < cut[i].nx)
                a = mid + 1;
            else
                z = mid;
        }
        nxt[i] = (int)a + 1;
    }
    for (;;) {
        i64 lo = s ? cut[s - 1].c + 1 : 0, hi = s < K ? cut[s].c : N - 1;
        if (++cnt > K + 1)
            return 0;
        if (ev2 && hi >= lo)
            memcpy(ev2 + at, ev + lo, (size_t)(hi - lo + 1) * sizeof(Ev));
        if (slo && hi >= lo) {
            slo[m2] = lo;
            shi[m2++] = hi;
        }
        at += hi - lo + 1;
        if (s == K)
            break;
        s = nxt[s];
    }
    if (nstr)
        *nstr = m2;
    return cnt == K + 1 && at == N;
}
/* The place of a move: mg events on either side of its cuts and, once it is judged, its zones (--or3-zone Z: only
   their first Z events) and mg events after them.  mark[e + 1] belongs to event e (-1 .. N).  what = 0: is the place free?  1: take it.  2: give it back. */
static int o3_place(char *mark, const O3M *m, i64 N, int mg, int what, int judged) {
    for (int i = 0; i < m->k + (judged ? O3KM : 0); i++) {
        i64 a, b;
        if (i < m->k) {
            a = (i64)m->c[i] - mg;
            b = (i64)m->c[i] + 1 + mg;
        } else {
            int j = i - m->k;
            if (m->zh[j] < m->zl[j])
                continue;
            a = m->zl[j];
            b = (o3zone > 0 && m->zh[j] - m->zl[j] > o3zone ? (i64)m->zl[j] + o3zone : (i64)m->zh[j]) + mg;
        }
        if (a < -1)
            a = -1;
        if (b > N)
            b = N;
        if (what)
            memset(mark + a + 1, what == 1, (size_t)(b - a + 1));
        else
            for (i64 z = a; z <= b; z++)
                if (mark[z + 1])
                    return 0;
    }
    return 1;
}
/* ---- the tables after a round, from the tables before it.  The new sequence is the old one cut into stretches and
   put together in another order (slo[s] .. shi[s]: old first and last event of the s-th stretch in the new
   order).  The costs of the cuts of an event depend on what comes before it (fw) or after it (bw) only
   through the table of its neighbour; so in every stretch fw is computed again from its first event until a table
   is what it was (from there on the old tables hold, and so do the steps of fmin), and bw in the same way from
   its last event backwards.  All stretches at once, each from the old table of its new neighbour; a stretch whose
   neighbour did not get its old table back at that end (a short stretch) is done again afterwards, in order.
   ev, P: before the round; P2: after it (dir 0: off, fw, fmin; dir 1: bw, gmin).  chg[z] is set for every event
   (old place) whose table is not what it was.  Returns the layers computed.
   rsz (o3_tables_skip): rsz[z] >= 0 is the number of cuts event z may take now, if they are not those it had
   in P; such an event is a stretch of its own, its table is always new, and what follows it is done in order. */
static i64 o3_move1(BS *b, const POT *P, POT *P2, i64 N, i64 lo, i64 hi, i64 at, i64 nb, const unsigned char *nt,
                    i64 *d2, int dir, int *dirty, char *chg, const int *rsz) {
    BScr *w = &b->scr[0];
    i64 bnd[18], nl = 0, zr = dir ? lo - 1 : hi + 1; /* zr: where the old table is back (none: beyond the far end) */
    const unsigned char *oldt = dir ? P->bw : P->fw;
    unsigned char *newt = dir ? P2->bw : P2->fw;
    if (nb == -2)
        zr = dir ? hi + 1 : lo - 1; /* the same neighbour as before: nothing changes */
    else
        for (i64 z = dir ? hi : lo; dir ? z >= lo : z <= hi; z += dir ? -1 : 1) {
            unsigned char *T = newt + P2->off[at + z - lo];
            if (nb >= 0) {
                BEv *x = bs_ev(b, nb);
                o3_pool1(w, nt, dir ? x->S : x->E, x->m, bnd);
            }
            BEv *e = bs_ev(b, z);
            int mm = e->m, mn = 1 << 20;
            if (mm > w->mcap) {
                w->mcap = mm + mm / 2 + 64;
                free(w->mv);
                w->mv = malloc((size_t)w->mcap * sizeof(int));
                if (!w->mv)
                    DIE("out of memory");
            }
            int *mv = w->mv;
            for (int q = 0; q < mm; q++)
                mv[q] = nb >= 0 ? h : 0;
            if (nb >= 0)
                bs_join(w, bnd, &e, 1, mv, dir);
            for (int q = 0; q < mm; q++) {
                mv[q] += e->D[q];
                if (mv[q] < mn)
                    mn = mv[q];
            }
            for (int q = 0; q < mm; q++)
                T[q] = (unsigned char)(mv[q] - mn < h ? mv[q] - mn : h);
            d2[at + z - lo] = mn;
            nl++;
            if (!(rsz && rsz[z] >= 0) && !memcmp(T, oldt + P->off[z], (size_t)mm)) {
                zr = z;
                break;
            }
            if (chg)
                chg[z] = 1;
            nt = T;
            nb = z;
        }
    if (!dir) { /* the rest of the stretch as before */
        i64 z0 = zr < lo ? lo : zr + 1;
        if (z0 <= hi) {
            memcpy(newt + P2->off[at + z0 - lo], oldt + P->off[z0], (size_t)(P->off[hi + 1] - P->off[z0]));
            for (i64 z = z0; z <= hi; z++)
                d2[at + z - lo] = P->fmin[z] - (z ? P->fmin[z - 1] : 0);
        }
        *dirty = zr == hi + 1;
    } else {
        i64 z1 = zr > hi ? hi : zr - 1;
        if (z1 >= lo) {
            memcpy(newt + P2->off[at], oldt + P->off[lo], (size_t)(P->off[z1 + 1] - P->off[lo]));
            for (i64 z = lo; z <= z1; z++)
                d2[at + z - lo] = P->gmin[z] - (z + 1 < N ? P->gmin[z + 1] : 0);
        }
        *dirty = zr == lo - 1;
    }
    return nl;
}
/* The tables of the new sequence from the old ones.  The new sequence is the blocks slo[s] .. shi[s]
   of the old one.  Inside every block the costs are computed again from its new neighbour, layer by layer, until
   a layer comes out as it was; the rest is copied.  dir 0: costs from the front (fw, fmin); 1: from the back (bw,
   gmin).  chg marks the events whose costs changed.  rsz: the new number of cuts of an event that changed it.
   Returns the number of layers computed. */
static i64 o3_tables_move(O3 *o, const POT *P, POT *P2, const i64 *slo, const i64 *shi, i64 ns, int dir, char *chg,
                          const int *rsz) {
    i64 N = o->N, nlay = 0, *at = malloc((size_t)(ns + 1) * 8), *d2 = malloc((size_t)(N + 1) * 8);
    int *dirty = calloc((size_t)ns + 1, sizeof(int));
    if (!at || !d2 || !dirty)
        DIE("out of memory");
    at[0] = 0;
    for (i64 s = 0; s < ns; s++)
        at[s + 1] = at[s] + shi[s] - slo[s] + 1;
    if (at[ns] != N)
        DIE("internal error: segment insertion (stretches)");
    if (!dir) {
        P2->off = malloc((size_t)(N + 1) * 8);
        P2->fmin = malloc((size_t)(N + 1) * 8);
        if (!P2->off || !P2->fmin)
            DIE("out of memory");
        P2->off[0] = 0;
        for (i64 s = 0; s < ns; s++)
            for (i64 z = slo[s]; z <= shi[s]; z++)
                P2->off[at[s] + z - slo[s] + 1] =
                    P2->off[at[s] + z - slo[s]] + (rsz && rsz[z] >= 0 ? rsz[z] : P->off[z + 1] - P->off[z]);
        P2->fw = malloc((size_t)P2->off[N] + 1);
        if (!P2->fw)
            DIE("out of memory");
    } else {
        P2->gmin = malloc((size_t)(N + 1) * 8);
        P2->bw = malloc((size_t)P2->off[N] + 1);
        if (!P2->gmin || !P2->bw)
            DIE("out of memory");
    }
#pragma omp parallel for schedule(dynamic, 1) num_threads(NTHR) reduction(+ : nlay)
    for (i64 s = 0; s < ns; s++) {
        BS *b = &o->tc[omp_get_thread_num()].b;
        i64 nb; /* the new neighbour (old place), -1: none, -2: the old one */
        if (!dir)
            nb = s ? shi[s - 1] : slo[0] == 0 ? -2 : -1;
        else
            nb = s + 1 < ns ? slo[s + 1] : shi[s] == N - 1 ? -2 : -1;
        if (rsz && nb >= 0 && rsz[nb] >= 0)
            continue; /* after an event with new cuts: done below, from its new table */
        if (rsz && nb == -2 && rsz[slo[s]] >= 0)
            nb = -1;
        nlay += o3_move1(b, P, P2, N, slo[s], shi[s], at[s], nb, nb >= 0 ? (dir ? P->bw : P->fw) + P->off[nb] : NULL,
                         d2, dir, &dirty[s], chg, rsz);
    }
    if (!dir) {
        for (i64 s = 1; s < ns; s++)
            if (dirty[s - 1] || (rsz && rsz[shi[s - 1]] >= 0))
                nlay += o3_move1(&o->tc[0].b, P, P2, N, slo[s], shi[s], at[s], shi[s - 1], P2->fw + P2->off[at[s] - 1],
                                 d2, 0, &dirty[s], chg, rsz);
    } else {
        for (i64 s = ns - 2; s >= 0; s--)
            if (dirty[s + 1] || (rsz && rsz[slo[s + 1]] >= 0))
                nlay += o3_move1(&o->tc[0].b, P, P2, N, slo[s], shi[s], at[s], slo[s + 1], P2->bw + P2->off[at[s + 1]],
                                 d2, 1, &dirty[s], chg, rsz);
    }
    if (!dir) {
        i64 c = 0;
        for (i64 p = 0; p < N; p++) {
            c += d2[p];
            P2->fmin[p] = c;
        }
    } else {
        i64 c = 0;
        for (i64 p = N - 1; p >= 0; p--) {
            c += d2[p];
            P2->gmin[p] = c;
        }
    }
    free(at);
    free(d2);
    free(dirty);
    return nlay;
}
/* The best cuts of ev from its tables (what co_run does on its way back): every event keeps its cut if that
   reaches the cost the next event needs, else the first plain cut that does, else the first one.  Returns the
   number of cuts changed; *skipchg: how many events gave up their skip (then their cuts are no longer
   those of P); skq: their places. */
static i64 o3_reopen(Ev *ev, const POT *P, i64 N, int *skipchg, int *skq) {
    i64 chg = 0, want = 0;
    u64 ns = 0;
    int *j0 = malloc((size_t)N * sizeof(int));
    if (!j0)
        DIE("out of memory");
#pragma omp parallel for schedule(dynamic, 64) num_threads(NTHR)
    for (i64 p = 0; p < N; p++) { /* the place of the present cut among those the event may take */
        const Ev *x = &ev[p];
        i64 o0 = co_cur(x);
        int j = 0;
        const Trail *T = &TR[x->t];
        if (o0 >= 0)
            for (i64 oo = T->olo; oo < o0; oo++)
                if (!OP[oo].g1 || oSK_t(T, oo) == x->skip)
                    j++;
        j0[p] = o0 < 0 ? -1 : j;
    }
    *skipchg = 0;
    for (i64 p = N - 1; p >= 0; p--) {
        Ev *x = &ev[p];
        const unsigned char *rel = P->fw + P->off[p];
        i64 tgt = p < N - 1 ? want : P->fmin[p], pick = -1;
        int pj = -1;
        if (j0[p] < 0) {
            if (p < N - 1 && P->fmin[p] + dist(x->e, ns) != want)
                DIE("internal error: segment insertion (opening of event %lld)", p);
            ns = x->s;
            want = P->fmin[p];
            continue;
        }
        i64 o0 = co_cur(x);
#define O3COV(j, E) (P->fmin[p] + rel[j] + (p < N - 1 ? dist((E), ns) : 0))
        if (rel[j0[p]] < h && O3COV(j0[p], x->e) == tgt) {
            pick = o0;
            pj = j0[p];
        }
        for (int pass = 0; pass < 2 && pick < 0; pass++) {
            O3It it;
            o3_it(&it, x);
            while (o3_next(&it))
                if (rel[it.j] < h && (pass || !OP[it.o].g1) && O3COV(it.j, o3_E(&it)) == tgt) {
                    pick = it.o;
                    pj = it.j;
                    break;
                }
        }
#undef O3COV
        if (pick < 0)
            DIE("internal error: segment insertion (no opening for event %lld)", p);
        if (pick != o0) {
            i64 sk = x->skip;
            *x = make_event(pick);
            chg++;
            if (x->skip != sk)
                skq[(*skipchg)++] = (int)p;
        }
        ns = x->s;
        want = P->fmin[p] + rel[pj] - oD(pick);
    }
    free(j0);
    return chg;
}
/* Are two sets of tables equal?  (--or3-check) */
static int o3_pot_same(const POT *A, const POT *B, i64 N) {
    return !memcmp(A->off, B->off, (size_t)(N + 1) * 8) && !memcmp(A->fmin, B->fmin, (size_t)N * 8) &&
           !memcmp(A->gmin, B->gmin, (size_t)N * 8) && !memcmp(A->fw, B->fw, (size_t)A->off[N]) &&
           !memcmp(A->bw, B->bw, (size_t)A->off[N]);
}
/* The gains are counted from the sequence with its best cuts: a sequence that comes without them gets them first
   (one that has them stays as it is). */
static i64 o3_first(CO *q, Ev *ev, i64 N) {
    i64 a0 = seq_length(ev, N);
    co_run(q, ev, N, 0, N - 1, 0, NULL);
    i64 a1 = seq_length(ev, N);
    if (a1 < a0) {
        printf("segment insertion: best openings of the sequence as it came: %lld -> %lld\n", a0, a1);
        fflush(stdout);
        if (o3plan)
            write_plan(ev, N, o3plan);
    }
    return a0 - a1;
}
/* ---------- moves of equal length: what o3_full needs (see the comment at o3q_eq) */
typedef struct {
    u64 key;
    int until;
} O3QT;
static O3QT *o3q_tb = NULL;
static i64 o3q_ntb = 0, o3q_tbcap = 0;
static u64 *o3q_tk = NULL;
static i64 o3q_ntk = 0, o3q_tkcap = 0; /* the joins cut lately; their keys in order */
/* a join, by the two events (trail, kind, piece) */
static inline u64 o3q_key(const Ev *x, const Ev *y) {
    u64 a = ((u64)x->t << 34) | ((u64)x->kind << 32) | (x->kind == EV_OPT ? 0 : (u64)x->a & 0xFFFFFFFFULL),
        b = ((u64)y->t << 34) | ((u64)y->kind << 32) | (y->kind == EV_OPT ? 0 : (u64)y->a & 0xFFFFFFFFULL);
    return hmix(a * 0x9E3779B97F4A7C15ULL + b);
}
/* Would move m make a join again that was cut in the last rounds?  (binary search in the sorted keys) */
static int o3q_is_tabu(const Ev *ev, i64 N, const O3M *m) {
    for (int i = 0; i < m->k; i++) {
        i64 x = m->c[i], y = (i64)m->c[m->nx[i]] + 1, a = 0, z = o3q_ntk;
        if (x < 0 || y >= N)
            continue;
        u64 key = o3q_key(&ev[x], &ev[y]);
        while (a < z) {
            i64 mid = (a + z) >> 1;
            if (o3q_tk[mid] < key)
                a = mid + 1;
            else
                z = mid;
        }
        if (a < o3q_ntk && o3q_tk[a] == key)
            return 1;
    }
    return 0;
}
/* the moves of a round are fixed (ev: the sequence before them): the joins they cut are not to be made again for o3q_tabu rounds */
static void o3q_made(const Ev *ev, i64 N, const O3M *sel, i64 nsel) {
    {
        i64 m = 0;
        for (i64 k = 0; k < o3q_ntb; k++)
            if (o3q_tb[k].until >= o3_nround)
                o3q_tb[m++] = o3q_tb[k];
        o3q_ntb = m;
    }
    if (o3q_tabu > 0)
        for (i64 k = 0; k < nsel; k++)
            for (int i = 0; i < sel[k].k; i++) {
                i64 c = sel[k].c[i];
                if (c < 0 || c + 1 >= N)
                    continue;
                if (o3q_ntb == o3q_tbcap) {
                    o3q_tbcap = o3q_tbcap ? 2 * o3q_tbcap : 1024;
                    o3q_tb = realloc(o3q_tb, (size_t)o3q_tbcap * sizeof(O3QT));
                    if (!o3q_tb)
                        DIE("out of memory");
                }
                o3q_tb[o3q_ntb].key = o3q_key(&ev[c], &ev[c + 1]);
                o3q_tb[o3q_ntb++].until = o3_nround + o3q_tabu;
            }
    if (o3q_ntb + 1 > o3q_tkcap) {
        o3q_tkcap = o3q_ntb + 1024;
        free(o3q_tk);
        o3q_tk = malloc((size_t)o3q_tkcap * 8);
        if (!o3q_tk)
            DIE("out of memory");
    }
    for (i64 k = 0; k < o3q_ntb; k++)
        o3q_tk[k] = o3q_tb[k].key;
    o3q_ntk = o3q_ntb;
    if (o3q_ntk > 1)
        qsort(o3q_tk, (size_t)o3q_ntk, 8, u64_cmp);
}
/* the plan to a new file that then takes the place of the old one: a plan file is never half written */
#if defined(_WIN32)
__declspec(dllimport) int __stdcall MoveFileExA(const char *, const char *, unsigned);
static int o3q_replace(const char *from, const char *to) {
    return MoveFileExA(from, to, 1 | 8) != 0;
}
#else
static int o3q_replace(const char *from, const char *to) {
    return rename(from, to) == 0;
}
#endif
/* Writes the plan beside its file and moves it into place, so that the file always holds a whole plan. */
static void o3q_plan(const Ev *ev, i64 N, const char *path) {
    char tmp[4300];
    snprintf(tmp, sizeof tmp, "%s.new", path);
    write_plan(ev, N, tmp);
    if (!o3q_replace(tmp, path)) {
        write_plan(ev, N, path);
        remove(tmp);
    }
}
/* the state of a round: zix: the candidates with estimate 0, by the move (after the draw: the long ones drawn, nzl of
   them); nz of them, nzlong of them long, npos candidates with an estimate above 0; nfree with a free place when
   they were drawn, ne drawn; last: this batch is the one with the draw */
typedef struct {
    int on, last, done;
    i64 *zix, zcap, nz, nzlong, npos, nfree, ne, nzl, njz, *pool, pcap;
    double t0;
} O3Q;
static const O3M *o3q_mv;
static int o3q_kcmp(const void *a, const void *b) {
    return o3k_cmp(&o3q_mv[*(const i64 *)a], &o3q_mv[*(const i64 *)b]);
}
/* a new round: the candidates with estimate 0.  Returns how many of them can be added to the last batch. */
static i64 o3q_begin(O3Q *z, const O3 *o) {
    const O3M *mv = o->mv;
    i64 nall = o->nall;
    z->on = o3q_eq > 0 && !o3old;
    z->last = z->done = 0;
    z->nz = z->nzlong = z->npos = z->nfree = z->ne = z->nzl = z->njz = 0;
    if (!z->on)
        return 0;
    if (nall + 1 > z->zcap) {
        z->zcap = nall + 1024;
        free(z->zix);
        z->zix = malloc((size_t)z->zcap * 8);
        if (!z->zix)
            DIE("out of memory");
    }
    for (i64 k = 0; k < nall; k++) {
        if (mv[k].est > 0)
            z->npos++;
        if (mv[k].est == 0) {
            z->zix[z->nz++] = k;
            z->nzlong += mv[k].lg != 0;
        }
    }
    o3q_mv = mv;
    if (z->nz > 1)
        qsort(z->zix, (size_t)z->nz, 8, o3q_kcmp);
    return o3q_eq < z->nz ? o3q_eq : z->nz;
}
/* the draw, with the last batch (ord[0 .. n-1] so far): E of the candidates with estimate 0 whose place is free.
   Those to be judged are added to ord; the long ones are kept in zix.  Returns the new n. */
static i64 o3q_draw(O3Q *z, const O3 *o, i64 N, char *mark, int mg, i64 *ord, i64 n) {
    const O3M *mv = o->mv;
    i64 m = 0, t;
    z->last = z->done = 1;
    z->t0 = wall();
    for (i64 k = 0; k < z->nz; k++)
        if (o3_place(mark, &mv[z->zix[k]], N, mg, 0, 0))
            z->zix[m++] = z->zix[k];
    z->nfree = m;
    z->ne = o3q_eq < m ? o3q_eq : m;
    for (i64 k = 0; k < z->ne; k++) {
        i64 j = k + (i64)(o3q_rnd() % (u64)(m - k));
        t = z->zix[k];
        z->zix[k] = z->zix[j];
        z->zix[j] = t;
    }
    for (i64 k = 0; k < z->ne; k++) {
        i64 c = z->zix[k];
        if (mv[c].lg && !o3check)
            z->zix[z->nzl++] = c;
        else {
            ord[n++] = c;
            z->njz++;
        }
    }
    return n;
}
/* The candidates o->mv[ord[0 .. n-1]] are taken in that order if they keep the length, as o3_full takes the shorter
   ones: judged once more with their zones in lots of nbmax; taken if the gain is 0, cuts and zones are free and the
   moves still give one sequence; at most maxsel moves in all.  st: next to a move taken, judged with their zones,
   long ones judged here for the first time, of those with a gain other than 0, would not give one sequence. */
static i64 o3q_take(O3 *o, i64 N, const i64 *ord, i64 n, i64 maxsel, O3M *sel, i64 nsel, char *mark, char *bm,
                    i64 *batch, i64 *bk, int nbmax, O3Cut *cut, int *nxt, i64 *st) {
    O3M *mv = o->mv;
    int mg = o3margin;
    i64 first = 0;
    char *cs = calloc((size_t)n + 1, 1), *nw = malloc((size_t)nbmax + 1);
    if (!cs || !nw)
        DIE("out of memory");
    while (nsel < maxsel) {
        int nb = 0;
        while (first < n && cs[first])
            first++;
        for (i64 k = first; k < n && nb < nbmax; k++) {
            if (cs[k])
                continue;
            if (!o3_place(mark, &mv[ord[k]], N, mg, 0, 0)) {
                cs[k] = 1;
                st[0]++;
                continue;
            }
            if (!o3_place(bm, &mv[ord[k]], N, mg, 0, 0))
                continue; /* next to one of this lot: later */
            nw[nb] = mv[ord[k]].gx == O3BAD;
            batch[nb] = ord[k];
            bk[nb++] = k;
            o3_place(bm, &mv[ord[k]], N, mg, 1, 0);
        }
        if (!nb)
            break;
        o3_judge(o, batch, nb, 1);
        st[1] += nb;
        for (int q = 0; q < nb; q++) {
            O3M *m = &mv[batch[q]];
            cs[bk[q]] = 1;
            o3_place(bm, m, N, mg, 2, 0);
            if (nw[q]) {
                st[2]++;
                st[3] += m->gx != 0;
            }
            if (nsel >= maxsel || m->gx != 0)
                continue;
            if (!o3_place(mark, m, N, mg, 0, 1)) {
                st[0]++;
                continue;
            }
            if (nsel && !o3_compose(sel, nsel, m, N, NULL, NULL, cut, nxt, NULL, NULL, NULL)) {
                st[4]++;
                continue;
            }
            sel[nsel++] = *m;
            o3_place(mark, m, N, mg, 1, 1);
        }
    }
    free(cs);
    free(nw);
    return nsel;
}
/* after the last batch: the moves of equal length.  Returns the number of moves taken so far. */
static i64 o3q_equal(O3Q *z, O3 *o, const Ev *ev, i64 N, i64 maxsel, O3M *sel, i64 nsel, char *mark, char *bm,
                     i64 *batch, i64 *bk, int nbmax, O3Cut *cut, int *nxt) {
    const O3M *mv = o->mv;
    i64 nall = o->nall, m = 0, m2 = 0, ntabu = 0, st[5] = {0}, nsh = nsel, lim;
    double t1 = wall();
    if (nall + 1 > z->pcap) {
        z->pcap = nall + 1024;
        free(z->pool);
        z->pool = malloc((size_t)z->pcap * 8);
        if (!z->pool)
            DIE("out of memory");
    }
    for (i64 k = 0; k < nall; k++)
        if (mv[k].gx == 0)
            z->pool[m++] = k;
    for (i64 k = 0; k < z->nzl; k++)
        z->pool[m++] = z->zix[k];
    o3q_mv = mv;
    if (m > 1)
        qsort(z->pool, (size_t)m, 8, o3q_kcmp);
    for (i64 k = 0; k < m; k++) {
        if (o3q_is_tabu(ev, N, &mv[z->pool[k]])) {
            ntabu++;
            continue;
        }
        z->pool[m2++] = z->pool[k];
    }
    for (i64 k = m2 - 1; k > 0; k--) {
        i64 j = (i64)(o3q_rnd() % (u64)(k + 1)), y = z->pool[k];
        z->pool[k] = z->pool[j];
        z->pool[j] = y;
    }
    lim = o3q_max > 0 && nsel + o3q_max < maxsel ? nsel + o3q_max : maxsel;
    nsel = o3q_take(o, N, z->pool, m2, lim, sel, nsel, mark, bm, batch, bk, nbmax, cut, nxt, st);
    printf(
        "segment insertion: moves of equal length: %lld candidates with estimate 0 (%lld long), %lld with an estimate above 0; %lld of the %lld with a free place drawn, %lld of them judged, %lld long ones not; %lld of equal length (%lld of them would make a join again that was cut lately); %lld taken after %lld shorter moves; %lld judged with their zones (%lld long ones for the first time, %lld of those with a gain other than 0), %lld next to a move taken, %lld would not give one sequence (%.1fs)\n",
        z->nz, z->nzlong, z->npos, z->ne, z->nfree, z->njz, z->nzl, m, ntabu, nsel - nsh, nsh, st[1], st[2], st[3],
        st[0], st[4], wall() - t1);
    fflush(stdout);
    return nsel;
}
/* ---------- moves of equal length from the list of o3h_batches (see the comment at o3hq_thin).  Z: the candidates
   with estimate 0 as they are read; G: those judged with gain 0; D, L: those drawn, to be judged / long. */
typedef struct {
    O3R *Z, *G, *D, *L;
    i64 nZ, cZ, nG, cG, nD, nL;
} O3HQ;
static O3HQ o3hq;
/* by the move, as o3k_cmp */
static int o3hq_mcmp(const void *a, const void *b) {
    const O3R *x = a, *y = b;
    return x->w[1] != y->w[1] ? (x->w[1] < y->w[1] ? -1 : 1) : x->w[2] != y->w[2] ? (x->w[2] < y->w[2] ? -1 : 1) : 0;
}
/* Appends a packed candidate to a list. */
static inline void o3hq_add(O3R **a, i64 *n, i64 *cap, const O3R *r) {
    if (*n == *cap) {
        *cap = *cap ? *cap + *cap / 2 : 1 << 14;
        *a = realloc(*a, (size_t)*cap * sizeof(O3R));
        if (!*a)
            DIE("out of memory");
    }
    (*a)[(*n)++] = *r;
}
/* a new round (what o3q_begin does when the list is o->mv) */
static i64 o3hq_begin(O3Q *z) {
    z->on = o3q_eq > 0 && !o3old;
    z->last = z->done = 0;
    z->nz = z->nzlong = z->npos = z->nfree = z->ne = z->nzl = z->njz = 0;
    o3hq.nZ = o3hq.nG = o3hq.nD = o3hq.nL = 0;
    return 0;
}
/* a candidate read from the list: 1 = its estimate is 0, it stays out of the batches */
static inline int o3hq_read(O3Q *z, const O3R *r, const O3M *m) {
    if (!z->on)
        return 0;
    if (m->est > 0) {
        z->npos++;
        return 0;
    }
    if (m->est < 0)
        return 0;
    o3hq_add(&o3hq.Z, &o3hq.nZ, &o3hq.cZ, r);
    z->nz++;
    z->nzlong += m->lg != 0;
    return 1;
}
static inline void o3hq_zero(const O3R *r) {
    o3hq_add(&o3hq.G, &o3hq.nG, &o3hq.cG, r);
}
/* the draw (o3q_draw): E of the candidates with estimate 0 whose place is free.  Returns how many are to be judged
   (o3hq.D); the long ones are in o3hq.L. */
static i64 o3hq_draw(O3Q *z, i64 N, char *mark, int mg) {
    O3HQ *q = &o3hq;
    O3M M;
    i64 m = 0;
    z->last = z->done = 1;
    z->t0 = wall();
    if (q->nZ > 1)
        qsort(q->Z, (size_t)q->nZ, sizeof(O3R), o3hq_mcmp);
    for (i64 k = 0; k < q->nZ; k++) {
        o3h_unpack(q->Z[k].w, 0, &M);
        if (o3_place(mark, &M, N, mg, 0, 0))
            q->Z[m++] = q->Z[k];
    }
    z->nfree = m;
    z->ne = o3q_eq < m ? o3q_eq : m;
    for (i64 k = 0; k < z->ne; k++) {
        i64 j = k + (i64)(o3q_rnd() % (u64)(m - k));
        O3R t = q->Z[k];
        q->Z[k] = q->Z[j];
        q->Z[j] = t;
    }
    free(q->D);
    free(q->L);
    q->D = malloc((size_t)(z->ne + 1) * sizeof(O3R));
    q->L = malloc((size_t)(z->ne + 1) * sizeof(O3R));
    if (!q->D || !q->L)
        DIE("out of memory");
    q->nD = q->nL = 0;
    for (i64 k = 0; k < z->ne; k++) {
        o3h_unpack(q->Z[k].w, 0, &M);
        if (M.lg)
            q->L[q->nL++] = q->Z[k];
        else
            q->D[q->nD++] = q->Z[k];
    }
    z->nzl = q->nL;
    z->njz = q->nD;
    return q->nD;
}
/* after the last batch (o3q_equal): the candidates judged with gain 0 and the long ones drawn, by the move, without
   those under the tabu, in random order, taken by o3q_take.  hl: the count of long candidates of o3h_batches. */
static i64 o3hq_equal(O3Q *z, O3 *o, const Ev *ev, i64 N, i64 maxsel, O3M *sel, i64 nsel, char *mark, char *bm,
                      i64 *batch, i64 *bk, int nbmax, O3Cut *cut, int *nxt, i64 *hl) {
    O3HQ *q = &o3hq;
    i64 m = q->nG + q->nL, m2 = 0, ntabu = 0, st[5] = {0}, nsh = nsel, lim;
    double t1 = wall();
    O3M *mv0 = o->mv;
    O3R *R = malloc((size_t)(m + 1) * sizeof(O3R));
    O3M *P = malloc((size_t)(m + 1) * sizeof(O3M));
    i64 *pool = malloc((size_t)(m + 1) * 8);
    char *wasl = malloc((size_t)m + 1);
    if (!R || !P || !pool || !wasl)
        DIE("out of memory");
    if (q->nG)
        memcpy(R, q->G, (size_t)q->nG * sizeof(O3R));
    for (i64 k = 0; k < q->nL; k++) {
        R[q->nG + k] = q->L[k];
        R[q->nG + k].w[0] |= 1ULL << 63;
    }
    if (m > 1)
        qsort(R, (size_t)m, sizeof(O3R), o3hq_mcmp);
    for (i64 k = 0; k < m; k++) {
        wasl[k] = (char)(R[k].w[0] >> 63);
        o3h_unpack(R[k].w, O3H_EST(R[k].w[0]), &P[k]);
        if (!wasl[k])
            P[k].gx = 0;
    }
    for (i64 k = 0; k < m; k++) {
        if (o3q_is_tabu(ev, N, &P[k])) {
            ntabu++;
            continue;
        }
        pool[m2++] = k;
    }
    for (i64 k = m2 - 1; k > 0; k--) {
        i64 j = (i64)(o3q_rnd() % (u64)(k + 1)), y = pool[k];
        pool[k] = pool[j];
        pool[j] = y;
    }
    lim = o3q_max > 0 && nsel + o3q_max < maxsel ? nsel + o3q_max : maxsel;
    o->mv = P;
    nsel = o3q_take(o, N, pool, m2, lim, sel, nsel, mark, bm, batch, bk, nbmax, cut, nxt, st);
    o->mv = mv0;
    for (i64 k = 0; k < m; k++)
        if (P[k].lg) { /* the long candidates judged, as o3_full counts them at the end of a round */
            if (wasl[k]) {
                if (P[k].gx != O3BAD) {
                    hl[0]++;
                    if (P[k].gx != P[k].est) {
                        hl[1]++;
                        hl[2] += P[k].gx > 0 && P[k].est <= 0;
                    }
                }
            } else if (P[k].gx == O3BAD) {
                hl[0]--;
                if (P[k].est != 0)
                    hl[1]--;
            }
        }
    printf(
        "segment insertion: moves of equal length: %lld candidates with estimate 0 (%lld long), %lld with an estimate above 0; %lld of the %lld with a free place drawn, %lld of them judged, %lld long ones not; %lld of equal length (%lld of them would make a join again that was cut lately); %lld taken after %lld shorter moves; %lld judged with their zones (%lld long ones for the first time, %lld of those with a gain other than 0), %lld next to a move taken, %lld would not give one sequence (%.1fs)\n",
        z->nz, z->nzlong, z->npos, z->ne, z->nfree, z->njz, z->nzl, m, ntabu, nsel - nsh, nsh, st[1], st[2], st[3],
        st[0], st[4], wall() - t1);
    fflush(stdout);
    free(R);
    free(P);
    free(pool);
    free(wasl);
    return nsel;
}
/* ---------- the batches of a round from the list of o3h_begin (see there).  What o3_full does with o.mv, with the
   candidates read a piece at a time: a batch is the next bsz candidates whose place is free; they are judged in
   pieces of og_chunk(), the shorter ones are kept (O3K) and sorted by falling gain, then by the move, and taken as
   in o3_full: judged once more with their zones in lots of nbmax, taken if cuts and zones are free and the moves
   still give one sequence.  hl: long candidates judged, with a gain other than the estimate, of those shorter with
   an estimate of 0 or less (what o3_full counts over o.mv at the end of a round). */
static void o3h_batches(O3 *o, i64 N, i64 bsz, i64 maxsel, O3M *sel, i64 *nselp, i64 *promised, char *mark, char *bm,
                        i64 *batch, i64 *bk, int nbmax, O3Cut *cut, int *nxt, i64 *posp, i64 *njud, i64 *nshort,
                        i64 *ndrop, i64 *ncyc, i64 *nzj, int *late, int *nbat, i64 *hl, O3Q *zq, const Ev *ev) {
    O3H *h = &o3h;
    int mg = o3margin, nojc0 = o3nojc;
    i64 nall = h->nall, ch = og_chunk(), pos = *posp, nsel = *nselp, kcap = 0, kn;
    double tlast = wall();
    if (o3h_max > 0 && nall > o3h_max) {
        printf("segment insertion: only the first %lld of the %lld candidates are looked at (--or3-hmax)\n", o3h_max,
               nall);
        nall = o3h_max;
    }
    if (h->nall > O3H_JCMAX)
        o3nojc = 1; /* too many to keep their gains for the next round */
    O3M *mv0 = o->mv, *C = malloc((size_t)(ch + 1) * sizeof(O3M)), *lot = malloc((size_t)(nbmax + 1) * sizeof(O3M));
    O3R *CR = malloc((size_t)(ch + 1) * sizeof(O3R));
    i64 *idx = malloc((size_t)(ch + nbmax + 1) * 8), *pg = malloc((size_t)(nbmax + 1) * 8);
    O3HV kv;
    O3K *K = NULL;
    char *cs = NULL;
    i64 cscap = 0, kpeak = 0;
    if (!C || !lot || !CR || !idx || !pg)
        DIE("out of memory");
    memset(&kv, 0, sizeof kv);
    o3hv_open(&kv, (size_t)(nall < (1LL << 24) ? nall + 1 : 1LL << 24) * sizeof(O3K));
    for (i64 q = 0; q < ch + nbmax; q++)
        idx[q] = q;
    while (pos < nall && nsel < maxsel && !*late) {
        i64 n = 0, ns, first = 0, sel0 = nsel, drop0 = *ndrop, best = O3BAD, formed = 0;
        double tb = wall();
        kn = 0;
        while (pos < nall && n < bsz && !*late) {
            i64 m = 0;
            O3R r;
            while (pos < nall && n + m < bsz && m < ch) {
                if (!o3h_next(h, &r))
                    DIE("internal error: segment insertion (the list ends at %lld of %lld candidates)", pos, nall);
                pos++;
                o3h_unpack(r.w, O3H_EST(r.w[0]), &C[m]);
                if (o3hq_read(zq, &r, &C[m]))
                    continue; /* estimate 0 with --or3-eq: for the draw */
                if (o3_place(mark, &C[m], N, mg, 0, 0))
                    CR[m++] = r;
                else
                    (*ndrop)++;
            }
            if (!m)
                break;
            if (!formed)
                (*nbat)++;
            formed += m;
            if (o3sec > 0 && O3NOW() > o3sec) {
                *late = 1;
                break;
            }
            o->mv = C;
            o3_judge(o, idx, m, 0);
            n += m;
            for (i64 q = 0; q < m; q++) {
                const O3M *c = &C[q];
                i64 g = c->gx;
                if (g != O3BAD && g > best)
                    best = g;
                if (c->lg && g != O3BAD) {
                    hl[0]++;
                    if (g != c->est) {
                        hl[1]++;
                        hl[2] += g > 0 && c->est <= 0;
                    }
                }
                if (g == 0 && zq->on)
                    o3hq_zero(&CR[q]);
                if (g == O3BAD || g <= 0)
                    continue;
                if (kn >= kcap) {
                    o3hv_need(&kv, (size_t)(kn + 1) * sizeof(O3K));
                    K = (O3K *)kv.p;
                    kcap = (i64)(kv.com / sizeof(O3K));
                    if ((i64)kv.com > kpeak)
                        kpeak = (i64)kv.com;
                }
                if (g >= (1 << 24))
                    DIE("internal error: segment insertion (gain %lld)", g);
                K[kn].w[0] = ((u64)((1 << 24) - g) << 16) | (CR[q].w[0] & 0xFFFF);
                K[kn].w[1] = CR[q].w[1];
                K[kn].w[2] = CR[q].w[2];
                kn++;
            }
            if (wall() - tlast > 60) {
                tlast = wall();
                printf("segment insertion: batch %d: %lld candidates judged, %lld of %lld looked at (%.0fs)\n", *nbat,
                       n, pos, nall, tlast - tb);
                fflush(stdout);
            }
        }
        if (zq->on && pos >= nall && !zq->done &&
            !*late) { /* --or3-eq: the draw, with the last batch; those drawn that are not long are judged with it */
            i64 nd = o3hq_draw(zq, N, mark, mg);
            for (i64 a = 0; a < nd && !*late;) {
                i64 m = nd - a < ch ? nd - a : ch;
                for (i64 q = 0; q < m; q++) {
                    CR[q] = o3hq.D[a + q];
                    o3h_unpack(CR[q].w, 0, &C[q]);
                }
                if (!formed)
                    (*nbat)++;
                formed += m;
                if (o3sec > 0 && O3NOW() > o3sec) {
                    *late = 1;
                    break;
                }
                o->mv = C;
                o3_judge(o, idx, m, 0);
                n += m;
                a += m;
                for (i64 q = 0; q < m; q++) {
                    const O3M *c = &C[q];
                    i64 g = c->gx;
                    if (g != O3BAD && g > best)
                        best = g;
                    if (c->lg && g != O3BAD) {
                        hl[0]++;
                        if (g != c->est) {
                            hl[1]++;
                            hl[2] += g > 0 && c->est <= 0;
                        }
                    }
                    if (g == 0 && zq->on)
                        o3hq_zero(&CR[q]);
                    if (g == O3BAD || g <= 0)
                        continue;
                    if (kn >= kcap) {
                        o3hv_need(&kv, (size_t)(kn + 1) * sizeof(O3K));
                        K = (O3K *)kv.p;
                        kcap = (i64)(kv.com / sizeof(O3K));
                        if ((i64)kv.com > kpeak)
                            kpeak = (i64)kv.com;
                    }
                    if (g >= (1 << 24))
                        DIE("internal error: segment insertion (gain %lld)", g);
                    K[kn].w[0] = ((u64)((1 << 24) - g) << 16) | (CR[q].w[0] & 0xFFFF);
                    K[kn].w[1] = CR[q].w[1];
                    K[kn].w[2] = CR[q].w[2];
                    kn++;
                }
            }
        }
        if (!formed && !zq->last)
            break;
        if (!formed)
            (*nbat)++;
        *njud += n;
        o3k_sort(K, kn);
        ns = kn;
        *nshort += ns;
        if (ns + 1 > cscap) {
            cscap = ns + ns / 2 + 1024;
            free(cs);
            cs = malloc((size_t)cscap);
            if (!cs)
                DIE("out of memory");
        }
        memset(cs, 0, (size_t)ns + 1);
        while (nsel < maxsel) {
            int nb = 0;
            while (first < ns && cs[first])
                first++;
            for (i64 k = first; k < ns && nb < nbmax; k++) {
                if (cs[k])
                    continue;
                O3M *m = &lot[nb];
                o3h_unpack(K[k].w, O3H_EST(K[k].w[0]), m);
                if (!o3_place(mark, m, N, mg, 0, 0)) {
                    cs[k] = 1;
                    (*ndrop)++;
                    continue;
                }
                if (!o3_place(bm, m, N, mg, 0, 0))
                    continue; /* next to one of this lot: later */
                m->gx = (1 << 24) - (i64)(K[k].w[0] >> 16);
                pg[nb] = m->gx;
                bk[nb] = k;
                batch[nb] = nb;
                nb++;
                o3_place(bm, m, N, mg, 1, 0);
            }
            if (!nb)
                break;
            o->mv = lot;
            o3_judge(o, batch, nb, 1);
            *nzj += nb;
            for (int z = 0; z < nb; z++) {
                O3M *m = &lot[z];
                cs[bk[z]] = 1;
                o3_place(bm, m, N, mg, 2, 0);
                if (m->gx == O3BAD && m->lg) {
                    hl[0]--;
                    if (pg[z] != m->est) {
                        hl[1]--;
                        hl[2] -= pg[z] > 0 && m->est <= 0;
                    }
                } /* o3_full counts with the gains as they are at the end */
                if (m->gx == O3BAD || m->gx <= 0)
                    continue;
                if (!o3_place(mark, m, N, mg, 0, 1)) {
                    (*ndrop)++;
                    continue;
                }
                if (nsel && !o3_compose(sel, nsel, m, N, NULL, NULL, cut, nxt, NULL, NULL, NULL)) {
                    (*ncyc)++;
                    continue;
                }
                sel[nsel++] = *m;
                *promised += m->gx;
                o3_place(mark, m, N, mg, 1, 1);
                if (nsel == maxsel)
                    break;
            }
        }
        printf(
            "segment insertion: batch %d: %lld candidates judged, %lld shorter (best gain %lld), %lld moves taken, %lld next to a move taken; %lld of %lld candidates looked at (%.1fs)\n",
            *nbat, n, ns, n && best != O3BAD ? best : 0, nsel - sel0, *ndrop - drop0, pos, nall, wall() - tb);
        fflush(stdout);
        if (zq->last && !*late)
            nsel = o3hq_equal(zq, o, ev, N, maxsel, sel, nsel, mark, bm, batch, bk, nbmax, cut, nxt, hl);
    }
    {
        i64 cn, cp;
        o3h_commit(&cn, &cp);
        printf(
            "segment insertion: the candidates came in %lld pieces (%lld two-pair moves made in %.1fs, %d search%s for chains %.1fs); at most %lld MB for candidates and %lld MB for the shorter ones of a batch; the process has %lld MB committed, %lld MB at its peak\n",
            h->nseg, h->nfill, h->tfill, h->npass, h->npass > 1 ? "es" : "", h->tpass, h->peak >> 20, kpeak >> 20, cn,
            cp);
        fflush(stdout);
    }
    o->mv = mv0;
    *posp = pos;
    *nselp = nsel;
    o3nojc = nojc0;
    free(C);
    free(lot);
    free(CR);
    free(idx);
    free(pg);
    o3hv_close(&kv);
    free(cs);
    o3h_close(h);
}
/* A round: tables, pairs and candidates (by falling estimate).  Then, one batch after the other (--or3-maxcand M:
   M candidates; without it all at once): the candidates of the batch whose cuts are still free are judged, and
   the shorter ones are taken, the best first, if their place is free: a move is judged once more without looking
   ahead, which gives its zones, and taken if its cuts and zones are more than --or3-margin events away from
   those of the moves already taken and the moves together still give one sequence.  A candidate next to a move
   already taken is not judged at all.  The moves are then made together and the whole sequence is cut again;
   that gives the sum of their gains (if it ever gives less, as it can with --or3-zone, the first half of them is
   tried, and so on, and the best of these is made; one move alone gives what it promised).  The plan is written
   after every round that made the word shorter.
   The tables are not made again for the next round: they are brought up to date where the moves changed them
   (o3_tables_move), and the best cuts of the new sequence are read from them (o3_reopen).  --or3-full: as
   before, tables from nothing every round and the cuts by co_run; --or3-check: both, and compared.
   RULE FOR ANYTHING ADDED HERE (other kinds of moves, moves that make the word longer and are undone later, ...):
   what is kept between rounds (tables, pair lists, V of joins not listed, gains of candidates) is valid only
   through the stamps set below (lastF, lastB, lastJ by the names of the events, chgF / chgB / lperm for the pair
   lists).  So every change of the sequence must either be made here, through o3_compose + o3_tables_move, or
   leave o.pvalid = 0 and o.lvalid = 0: then the next round makes the tables new and forgets everything kept. */
static const O3M *o3_ordmv;
/* by falling gain, then by the move */
static int o3ord_cmp(const void *a, const void *b) {
    i64 x = *(const i64 *)a, y = *(const i64 *)b;
    i64 gx = o3_ordmv[x].gx, gy = o3_ordmv[y].gx;
    return gx > gy ? -1 : gx < gy ? 1 : o3k_cmp(&o3_ordmv[x], &o3_ordmv[y]);
}
/* The pass: rounds until one gains nothing.  A round makes or updates the tables and the pair lists,
   finds the candidates, judges them in batches, takes the moves that do not disturb each other all at once, and
   brings tables, names and stamps up to date (see the comment above).  Returns the letters gained. */
static i64 o3_full(Ev *ev, i64 N) {
    O3 o;
    o3_init(&o, N);
    CO q;
    memset(&q, 0, sizeof q);
    enum { MAXSEL = 8192 };
    int nbmax = 4 * NTHR, mg = o3margin;
    Ev *ev2 = malloc((size_t)N * sizeof(Ev)), *evb = malloc((size_t)N * sizeof(Ev));
    i64 total = 0, *batch = malloc((size_t)nbmax * 8), *bk = malloc((size_t)nbmax * 8), *ord = NULL;
    char *cs = NULL;
    O3Cut *cut = malloc((size_t)(MAXSEL + 1) * O3KM * sizeof(O3Cut));
    int *nxt = malloc((size_t)(MAXSEL + 1) * O3KM * sizeof(int));
    char *mark = malloc((size_t)N + 3), *bm = calloc((size_t)N + 3, 1);
    O3M *sel = malloc((size_t)MAXSEL * sizeof(O3M));
    i64 *slo = malloc((size_t)((MAXSEL + 1) * O3KM + 2) * 8), *shi = malloc((size_t)((MAXSEL + 1) * O3KM + 2) * 8);
    char *chgF = malloc((size_t)N + 1), *chgB = malloc((size_t)N + 1);
    int *eid2 = malloc((size_t)N * sizeof(int)), *lperm = malloc((size_t)N * sizeof(int));
    char *dcut = malloc((size_t)N + 2), *chg2 = malloc((size_t)N + 1);
    int focus = 0, *skq = malloc((size_t)(N + 1) * sizeof(int)), *rsz = malloc((size_t)(N + 1) * sizeof(int));
    if (!ev2 || !evb || !batch || !bk || !cut || !nxt || !mark || !bm || !sel || !slo || !shi || !chgF || !chgB ||
        !eid2 || !lperm || !dcut || !chg2 || !skq || !rsz)
        DIE("out of memory");
    if (!o3full) {
        o.eid = malloc((size_t)N * sizeof(int));
        o.lastF = calloc((size_t)N, sizeof(int));
        o.lastB = calloc((size_t)N, sizeof(int));
        o.lastJ = calloc((size_t)N, sizeof(int));
        if (!o.eid || !o.lastF || !o.lastB || !o.lastJ)
            DIE("out of memory");
        for (i64 z = 0; z < N; z++)
            o.eid[z] = (int)z;
    }
    total += o3_first(&q, ev, N);
    o3_longz = o3long;
    O3Q zq;
    memset(&zq, 0, sizeof zq);
    int dry = 0; /* --or3-eq: the candidates with estimate 0 of the round; rounds in a row without a gain */
    o3q_seen = -1;
    for (;;) {
        if (o3_stop()) {
            printf("segment insertion: stopped after %d rounds, %.0fs\n", o3_nround, O3NOW());
            fflush(stdout);
            break;
        }
        if (o3q_eq > 0 && dry >= o3q_patience) {
            printf("segment insertion: %d rounds without a gain\n", dry);
            fflush(stdout);
            break;
        }
        double t0 = wall();
        i64 l0 = seq_length(ev, N), l1;
        o.dstart = focus ? dcut : NULL;
        o3h_ctx = 1;
        o3_prepare(&o, ev);
        o3h_ctx = 0;
        o3_nround++;
        if (o3dry)
            break;
        double t1 = wall(), tlast = t1;
        O3M *mv = o.mv;
        i64 nall = o.nall, bsz = o3maxcand > 0 && o3maxcand < nall ? o3maxcand : nall, pos = 0, nsel = 0, promised = 0,
            njud = 0, nshort = 0, ndrop = 0, ncyc = 0, nzj = 0, st[4];
        int late = 0, nbat = 0;
        int hon = o3h.act;
        i64 hbsz = bsz, hl[3] = {0, 0, 0};
        if (hon)
            bsz = 0; /* hon: the candidates come from o3h_begin, the batches from o3h_batches */
        i64 zroom = hon ? o3hq_begin(&zq) : o3q_begin(&zq, &o);
        ord = realloc(ord, (size_t)(bsz + zroom + 1) * 8);
        cs = realloc(cs, (size_t)(bsz + zroom) + 1);
        if (!ord || !cs)
            DIE("out of memory");
        memset(mark, 0, (size_t)N + 3);
        if (hon)
            o3h_batches(&o, N, hbsz, MAXSEL, sel, &nsel, &promised, mark, bm, batch, bk, nbmax, cut, nxt, &pos, &njud,
                        &nshort, &ndrop, &ncyc, &nzj, &late, &nbat, hl, &zq, ev);
        else
            while (pos < nall && nsel < MAXSEL && !late) {
                i64 n = 0, ns = 0, first = 0, sel0 = nsel, drop0 = ndrop;
                double tb = wall();
                for (; pos < nall && n < bsz; pos++) {
                    if (zq.on && mv[pos].est == 0)
                        continue;
                    if (o3_place(mark, &mv[pos], N, mg, 0, 0))
                        ord[n++] = pos;
                    else
                        ndrop++;
                }
                if (zq.on && pos == nall && !zq.done)
                    n = o3q_draw(&zq, &o, N, mark, mg, ord, n);
                if (!n && !zq.last)
                    break;
                nbat++;
                for (i64 a = 0, ch = og_chunk(); a < n; a += ch) { /* in pieces, so that the time limit is seen */
                    if (o3sec > 0 && O3NOW() > o3sec) {
                        late = 1;
                        n = a;
                        break;
                    }
                    o3_judge(&o, ord + a, n - a < ch ? n - a : ch, 0);
                    if (wall() - tlast > 60) {
                        tlast = wall();
                        printf("segment insertion: batch %d: %lld of %lld candidates judged (%.0fs)\n", nbat,
                               a + ch < n ? a + ch : n, n, tlast - tb);
                        fflush(stdout);
                    }
                }
                njud += n;
                o3_ordmv = mv;
                qsort(ord, (size_t)n, 8, o3ord_cmp);
                while (ns < n && mv[ord[ns]].gx > 0)
                    ns++;
                nshort += ns;
                memset(cs, 0, (size_t)ns + 1);
                while (nsel < MAXSEL) {
                    int nb = 0;
                    while (first < ns && cs[first])
                        first++;
                    for (i64 k = first; k < ns && nb < nbmax; k++) {
                        if (cs[k])
                            continue;
                        if (!o3_place(mark, &mv[ord[k]], N, mg, 0, 0)) {
                            cs[k] = 1;
                            ndrop++;
                            continue;
                        }
                        if (!o3_place(bm, &mv[ord[k]], N, mg, 0, 0))
                            continue; /* next to one of this lot: later */
                        bk[nb] = k;
                        batch[nb++] = ord[k];
                        o3_place(bm, &mv[ord[k]], N, mg, 1, 0);
                    }
                    if (!nb)
                        break;
                    og_judge_zones(&o, batch, nb, mv, ord, cs, first, ns, mark, N, mg);
                    nzj += nb;
                    for (int z = 0; z < nb; z++) {
                        O3M *m = &mv[batch[z]];
                        cs[bk[z]] = 1;
                        o3_place(bm, m, N, mg, 2, 0);
                        if (m->gx == O3BAD || m->gx <= 0)
                            continue;
                        if (!o3_place(mark, m, N, mg, 0, 1)) {
                            ndrop++;
                            continue;
                        }
                        if (nsel && !o3_compose(sel, nsel, m, N, NULL, NULL, cut, nxt, NULL, NULL, NULL)) {
                            ncyc++;
                            continue;
                        }
                        sel[nsel++] = *m;
                        promised += m->gx;
                        o3_place(mark, m, N, mg, 1, 1);
                        if (nsel == MAXSEL)
                            break;
                    }
                }
                printf(
                    "segment insertion: batch %d: %lld candidates judged, %lld shorter (best gain %lld), %lld moves taken, %lld next to a move taken; %lld of %lld candidates looked at (%.1fs)\n",
                    nbat, n, ns, n && mv[ord[0]].gx != O3BAD ? mv[ord[0]].gx : 0, nsel - sel0, ndrop - drop0, pos, nall,
                    wall() - tb);
                fflush(stdout);
                if (zq.last && !late)
                    nsel = o3q_equal(&zq, &o, ev, N, MAXSEL, sel, nsel, mark, bm, batch, bk, nbmax, cut, nxt);
            }
        o3_stats(&o, st);
        printf(
            "segment insertion: %lld moves taken; %lld candidates judged (%lld known from earlier rounds), %lld shorter, %lld judged with their zones, %lld left out next to a move taken, %lld would not give one sequence%s; %.1f layers per candidate, at most %lld after one join, %lld joins computed, %lld from the memo (%.1fs)\n",
            nsel, njud, o.jhit, nshort, nzj, ndrop, ncyc, late ? "; time is up" : "", njud ? (double)st[0] / njud : 0.0,
            st[1], st[2], st[3], wall() - t1);
        fflush(stdout);
        if (o3long > 0 && 2 * st[1] + 1 > o3_longz) {
            o3_longz = (int)(2 * st[1] + 1);
            printf(
                "segment insertion: a zone of %lld events; from now on a candidate is long with %d events and more between its cuts\n",
                st[1], o3_longz);
        }
        if (o3long > 0) { /* did the long candidates gain what their estimates said? */
            i64 nlj = 0, nlbad = 0, nlpos = 0;
            if (hon) {
                nlj = hl[0];
                nlbad = hl[1];
                nlpos = hl[2];
            } else
                for (i64 k = 0; k < nall; k++)
                    if (mv[k].lg && mv[k].gx != O3BAD) {
                        nlj++;
                        if (mv[k].gx != mv[k].est) {
                            nlbad++;
                            nlpos += mv[k].gx > 0 && mv[k].est <= 0;
                        }
                    }
            printf(
                "segment insertion: %lld long candidates judged, %lld with a gain other than their estimate, %lld of them shorter with an estimate of 0 or less\n",
                nlj, nlbad, nlpos);
            fflush(stdout);
        }
        if (!nsel) {
            if (!focus || late)
                break;
            printf("segment insertion: nothing near the moves of the round before; all cuts again\n");
            fflush(stdout);
            focus = 0;
            o.pvalid = 1;
            o.lkeep = 1;
            continue; /* the same sequence: its tables and pairs stay */
        }
        i64 nsel0 = nsel, bestg = -1, bestn = 0, lastn = 0, nstr = 0, nlay = 0, nop = 0;
        double t2 = wall(), tupd = t2;
        POT P2;
        int skipchg = 0, nskip = 0, inc = !o3full;
        memset(&P2, 0, sizeof P2);
        for (
            i64 ns = nsel;;
            ns =
                (ns + 1) /
                2) { /* all of them; if they do not give their sum, the first half, and so on: the best of these is made */
            i64 pr = 0, prh = 0;
            for (i64 k = 0; k < ns; k++) {
                pr += sel[k].gx;
                if (k < (ns + 1) / 2)
                    prh += sel[k].gx;
            }
            lastn = ns;
            if (!o3_compose(sel, ns, NULL, N, ev, ev2, cut, nxt, slo, shi, &nstr))
                DIE("internal error: segment insertion (moves together)");
            if (inc) {
                o3_pfree(&P2);
                memset(chgF, 0, (size_t)N);
                nlay = o3_tables_move(&o, &o.P, &P2, slo, shi, nstr, 0, chgF, NULL);
                l1 = l0 - (o.P.fmin[N - 1] - P2.fmin[N - 1]);
            } else {
                co_run(&q, ev2, N, 0, N - 1, 0, NULL);
                l1 = seq_length(ev2, N);
            }
            if (ns == 1 && l0 - l1 != pr)
                DIE("internal error: segment insertion promised %lld, got %lld", pr, l0 - l1);
            if (l0 - l1 > bestg) {
                bestg = l0 - l1;
                bestn = ns;
                if (!inc) {
                    Ev *t = ev2;
                    ev2 = evb;
                    evb = t;
                }
            }
            if (l0 - l1 >= pr || ns == 1)
                break;
            printf("segment insertion: %lld moves together give %lld instead of %lld\n", ns, l0 - l1, pr);
            fflush(stdout);
            if (bestg >= prh)
                break; /* the first half promises no more than that */
        }
        if (inc) {                /* the tables of the new sequence from the old ones, and the cuts from the tables */
            if (bestn != lastn) { /* not the set tried last: once more */
                if (!o3_compose(sel, bestn, NULL, N, ev, ev2, cut, nxt, slo, shi, &nstr))
                    DIE("internal error: segment insertion (moves together)");
                o3_pfree(&P2);
                memset(chgF, 0, (size_t)N);
                nlay = o3_tables_move(&o, &o.P, &P2, slo, shi, nstr, 0, chgF, NULL);
            }
            free(o.P.fw);
            o.P.fw = NULL; /* the old fw is not needed any more */
            memset(chgB, 0, (size_t)N);
            nlay += o3_tables_move(&o, &o.P, &P2, slo, shi, nstr, 1, chgB, NULL);
            {
                i64 np = 0; /* the names move with the events; whose tables changed is noted for the values kept */
                for (i64 z = 0; z < N; z++) {
                    if (chgF[z])
                        o.lastF[o.eid[z]] = o.round;
                    if (chgB[z])
                        o.lastB[o.eid[z]] = o.round;
                }
                for (i64 s2 = 0; s2 < nstr; s2++)
                    o.lastJ[o.eid[shi[s2]]] = o.round; /* what follows the last event of every stretch is new */
                for (i64 s2 = 0; s2 < nstr; s2++)
                    for (i64 z = slo[s2]; z <= shi[s2]; z++) {
                        lperm[np] = (int)z;
                        eid2[np++] = o.eid[z];
                    }
                int *t = o.eid;
                o.eid = eid2;
                eid2 = t;
            }
            if (P2.gmin[0] != P2.fmin[N - 1] || o.P.fmin[N - 1] - P2.fmin[N - 1] != bestg)
                DIE("internal error: segment insertion (tables: forward %lld, backward %lld, gain %lld)",
                    P2.fmin[N - 1], P2.gmin[0], bestg);
            nop = o3_reopen(ev2, &P2, N, &skipchg, skq);
            nskip = skipchg;
            if (skipchg && skipchg < 1000 &&
                !o3noskip) { /* the tables once more: the same sequence, cut before and after every event that gave up its skip */
                POT P3;
                i64 n2 = 0, prev = 0, nl2;
                memset(&P3, 0, sizeof P3);
                for (i64 z = 0; z < N; z++)
                    rsz[z] = -1;
                qsort(skq, (size_t)skipchg, sizeof(int), int_cmp);
                for (int k = 0; k < skipchg; k++) {
                    i64 p = skq[k];
                    O3It it;
                    int m = 0;
                    o3_it(&it, &ev2[p]);
                    while (o3_next(&it))
                        m++;
                    rsz[p] = m;
                    if (p > prev) {
                        slo[n2] = prev;
                        shi[n2++] = p - 1;
                    }
                    slo[n2] = p;
                    shi[n2++] = p;
                    prev = p + 1;
                }
                if (prev < N) {
                    slo[n2] = prev;
                    shi[n2++] = N - 1;
                }
                for (int t = 0; t < o.ntc; t++) {
                    BS *b = &o.tc[t].b;
                    b->ev = ev2;
                    for (int k = 0; k < b->ecn; k++)
                        b->ec[k].id = -1;
                } /* the events as they are now */
                memset(chg2, 0, (size_t)N);
                nl2 = o3_tables_move(&o, &P2, &P3, slo, shi, n2, 0, chg2, rsz);
                for (i64 p = 0; p < N; p++)
                    if (chg2[p] || rsz[p] >= 0) {
                        chgF[lperm[p]] = 1;
                        o.lastF[o.eid[p]] = o.round;
                    }
                memset(chg2, 0, (size_t)N);
                nl2 += o3_tables_move(&o, &P2, &P3, slo, shi, n2, 1, chg2, rsz);
                for (i64 p = 0; p < N; p++)
                    if (chg2[p] || rsz[p] >= 0) {
                        chgB[lperm[p]] = 1;
                        o.lastB[o.eid[p]] = o.round;
                    }
                if (P3.gmin[0] != P3.fmin[N - 1] || P3.fmin[N - 1] != P2.fmin[N - 1])
                    DIE("internal error: segment insertion (tables after a skip was given up: forward %lld, backward %lld, before %lld)",
                        P3.fmin[N - 1], P3.gmin[0], P2.fmin[N - 1]);
                o3_pfree(&P2);
                P2 = P3;
                nlay += nl2;
                skipchg = 0;
            }
            if (seq_length(ev2, N) != l0 - bestg)
                DIE("internal error: segment insertion (openings from the tables give %lld, not %lld)",
                    seq_length(ev2, N), l0 - bestg);
            tupd = wall();
            if (o3check) { /* against tables made from nothing */
                POT F;
                memset(&F, 0, sizeof F);
                o3_pot(ev2, N, &F);
                if (!skipchg && !o3_pot_same(&F, &P2, N))
                    DIE("internal error: segment insertion (the tables kept differ from new ones)");
                printf("segment insertion: tables checked against new ones%s\n",
                       skipchg ? " (skipped: an event gave up its skip)" : "");
                o3_pfree(&F);
            }
            o3_pfree(&o.P);
            o.P = P2;
            o.pvalid = !skipchg;
            o.lperm = lperm;
            o.lchgF = chgF;
            o.lchgB = chgB;
            o.lvalid = !skipchg; /* for the pairs of the next round */
        } else {
            Ev *t = ev2;
            ev2 = evb;
            evb = t;
        }
        nsel = bestn;
        l1 = l0 - bestg;
        promised = 0;
        for (i64 k = 0; k < nsel; k++)
            promised += sel[k].gx;
        if (l1 > l0 || (l1 == l0 && !zq.on))
            DIE("internal error: segment insertion made the word longer");
        if (zq.on)
            o3q_made(ev, N, sel, nsel);
        if (inc)
            printf(
                "segment insertion: tables and openings brought up to date: %lld stretches, %lld layers, %lld openings changed%s (%.1fs)\n",
                nstr, nlay, nop,
                skipchg ? "; an event gave up its skip: new tables next round"
                : nskip ? "; an event gave up its skip, the tables were brought up to date once more"
                        : "",
                tupd - t2);
        printf("segment insertion: %lld move%s", nsel, nsel > 1 ? "s" : "");
        if (nsel < nsel0)
            printf(" of the %lld taken", nsel0);
        printf(", %lld -> %lld", l0, l1);
        if (l0 - l1 != promised)
            printf(" (%lld promised)", promised);
        printf(":");
        for (i64 k = 0; k < nsel && k < 4; k++) {
            printf(k ? "; " : " ");
            o3_print(&o, &sel[k], N);
            printf(", gain %lld", sel[k].gx);
        }
        printf("%s\n", nsel > 4 ? "; ..." : "");
        memcpy(ev, ev2, (size_t)N * sizeof(Ev));
        total += l0 - l1;
        if (o3plan) {
            if (zq.on)
                o3q_plan(ev, N, o3plan);
            else
                write_plan(ev, N, o3plan);
        }
        dry = l1 < l0 ? 0 : dry + 1;
        focus = 0;
        if (o3focus > 0 && inc &&
            o.pvalid) { /* the cuts near what this round changed: one of the next o3focus events has new costs or a new neighbour */
            i64 near = 1LL << 40;
            o.nstart = 0;
            for (i64 p = N - 1; p >= -1; p--) {
                if (p >= 0 && (chgF[lperm[p]] || chgB[lperm[p]] || o.lastJ[o.eid[p]] == o.round))
                    near = p;
                dcut[p + 1] = near - p <= (i64)o3focus + 1;
                o.nstart += dcut[p + 1];
            }
            focus = 1;
        }
        printf("segment insertion: round %d done in %.0fs, %.0fs since the pass began; plan written\n", o3_nround,
               wall() - t0, O3NOW());
        fflush(stdout);
    }
    o3_longz = 0; /* only this pass */
    free(zq.zix);
    free(zq.pool);
    free(dcut);
    free(chg2);
    free(skq);
    free(rsz);
    free(ev2);
    free(evb);
    free(slo);
    free(shi);
    free(chgF);
    free(chgB);
    free(eid2);
    free(lperm);
    free(batch);
    free(bk);
    free(ord);
    free(cs);
    free(cut);
    free(nxt);
    free(mark);
    free(bm);
    free(sel);
    o3_cofree(&q);
    o3_done(&o);
    return total;
}
/* --or3-old: every candidate is judged; then the shorter ones are taken, the best first: of two moves the one with
   the shorter span must lie inside one of the stretches of the other, 8 events away from its cuts.  The shorter
   spans are made first, so the cuts of the others stay where they were.  The whole sequence is then cut again;
   if it is not as short as promised, only the best move is made. */
static int o3_span_cmp(const void *a, const void *b) {
    const O3M *x = a, *y = b;
    i64 u = x->c[x->k - 1] - x->c[0], v = y->c[y->k - 1] - y->c[0];
    return u < v ? -1 : u > v ? 1 : o3k_cmp(a, b);
}
/* Does the whole of move q lie inside one block of move p, at least mg pieces from its cuts? */
/* the span of q inside one stretch of p */
static int o3_inside(const O3M *q, const O3M *p, i64 N, int mg) {
    i64 a = q->c[0], b = q->c[q->k - 1];
    for (int j = 0; j <= p->k; j++) {
        i64 lo = j ? p->c[j - 1] + 1 : 0, hi = j < p->k ? p->c[j] : N - 1;
        if (a + 1 >= lo + (j ? mg : 0) && b <= hi - (j < p->k ? mg : 0))
            return 1;
    }
    return 0;
}
/* The pass as in the first version (--or3-old): per round the best move, then every further shorter move
   that still fits, each confirmed by the fixed-order pass on the whole sequence. */
static i64 o3_full_old(Ev *ev, i64 N) {
    O3 o;
    o3_init(&o, N);
    CO q;
    memset(&q, 0, sizeof q);
    Ev *ev2 = malloc((size_t)N * sizeof(Ev)), *ev3 = malloc((size_t)N * sizeof(Ev));
    i64 total = 0;
    if (!ev2 || !ev3)
        DIE("out of memory");
    total += o3_first(&q, ev, N);
    for (;;) {
        if (o3_stop()) {
            printf("segment insertion: stopped after %d rounds, %.0fs\n", o3_nround, O3NOW());
            fflush(stdout);
            break;
        }
        double t0 = wall();
        i64 l0 = seq_length(ev, N), l1, g = o3_round(&o, ev), nsel = 0, promised = 0, nshort = 0;
        O3M *mv = o.mv;
        o3_nround++;
        if (g <= 0)
            break;
        while (nshort < o.nc && mv[nshort].gx > 0)
            nshort++;
        for (i64 k = 0; k < nshort; k++) {
            O3M x = mv[k];
            int ok = 1;
            for (i64 z = 0; z < nsel && ok; z++) {
                const O3M *y = &mv[z];
                ok =
                    x.c[x.k - 1] - x.c[0] <= y->c[y->k - 1] - y->c[0] ? o3_inside(&x, y, N, 8) : o3_inside(y, &x, N, 8);
            }
            if (ok) {
                mv[k] = mv[nsel];
                mv[nsel++] = x;
                promised += x.gx;
            }
        }
        O3M first = mv[0];
        qsort(mv, (size_t)nsel, sizeof(O3M), o3_span_cmp);
        memcpy(ev2, ev, (size_t)N * sizeof(Ev));
        for (i64 k = 0; k < nsel; k++) {
            o3_permute(ev2, ev3, N, &mv[k]);
            Ev *t = ev2;
            ev2 = ev3;
            ev3 = t;
        }
        co_run(&q, ev2, N, 0, N - 1, 0, NULL);
        l1 = seq_length(ev2, N);
        if (nsel > 1 && l1 > l0 - promised) { /* they did disturb each other: the best alone */
            printf("segment insertion: %lld moves together give %lld instead of %lld; only the best is made\n", nsel,
                   l0 - l1, promised);
            nsel = 1;
            promised = first.gx;
            mv[0] = first;
            o3_permute(ev, ev2, N, &first);
            co_run(&q, ev2, N, 0, N - 1, 0, NULL);
            l1 = seq_length(ev2, N);
        }
        if (nsel == 1 && l0 - l1 != promised)
            DIE("internal error: segment insertion promised %lld, got %lld", promised, l0 - l1);
        if (l1 >= l0)
            DIE("internal error: segment insertion made the word longer");
        memcpy(ev, ev2, (size_t)N * sizeof(Ev));
        total += l0 - l1;
        printf("segment insertion: %lld move%s of %lld shorter, %lld -> %lld:", nsel, nsel > 1 ? "s" : "", nshort, l0,
               l1);
        for (i64 k = 0; k < nsel && k < 6; k++) {
            printf(k ? "; " : " ");
            o3_print(&o, &mv[k], N);
        }
        printf("%s\n", nsel > 6 ? "; ..." : "");
        if (o3plan)
            write_plan(ev, N, o3plan);
        printf("segment insertion: round %d done in %.0fs, %.0fs since the pass began; plan written\n", o3_nround,
               wall() - t0, O3NOW());
        fflush(stdout);
    }
    free(ev2);
    free(ev3);
    o3_cofree(&q);
    o3_done(&o);
    return total;
}
/* When nothing is shorter: the moves that keep the length lead to other sequences of the same length; these are
   searched breadth first (at most `limit` of them are expanded, each with --bs K if given and a full round of
   segment insertions) until one of them has a shorter neighbour.  Returns the gain; ev changes only then. */
/* of the order only */
static u64 o3_hash(const Ev *ev, i64 N) {
    u64 x = 1469598103934665603ULL;
    for (i64 i = 0; i < N; i++) {
        x = (x ^ ev[i].t) * 1099511628211ULL;
        x = (x ^ (u64)(ev[i].kind == EV_OPT ? 0 : ev[i].kind == EV_SEG ? ev[i].a + 2 : 1)) * 1099511628211ULL;
    }
    return x;
}
/* When no move is shorter: breadth-first search over sequences of equal length, at most `limit` of them,
   until one has a shorter neighbour.  Returns the gain; ev is the new sequence then. */
static i64 o3_plateau(Ev *ev, i64 N, int limit) {
    O3 o;
    o3_init(&o, N);
    o.quiet = 1;
    CO q;
    memset(&q, 0, sizeof q);
    i64 cap = limit + 64, nq = 0, head = 0, nseen = 0, scap = 1 << 16, l0 = seq_length(ev, N), gain = 0;
    double t0 = wall();
    Ev **Q = malloc((size_t)cap * sizeof(Ev *)), *ev2 = malloc((size_t)N * sizeof(Ev));
    u64 *seen = malloc((size_t)scap * 8);
    if (!Q || !ev2 || !seen)
        DIE("out of memory");
    Q[nq] = malloc((size_t)N * sizeof(Ev));
    if (!Q[nq])
        DIE("out of memory");
    memcpy(Q[nq++], ev, (size_t)N * sizeof(Ev));
    seen[nseen++] = o3_hash(ev, N);
    while (head < nq && head < limit && !gain && !o3_stop()) {
        Ev *cur = Q[head++];
        co_run(&q, cur, N, 0, N - 1, 0, NULL); /* it was put there as the move left it */
        if (seq_length(cur, N) != l0)
            DIE("internal error: segment insertion (equal length)");
        if (bsK > 1 && head > 1) {
            BS b;
            CO qb;
            bs_init(&b, &qb, bsK);
            b.anyskip = 0;
            Ev *orig = malloc((size_t)N * sizeof(Ev)), *evo = malloc((size_t)N * sizeof(Ev));
            i64 *perm = malloc((size_t)N * 8), *opt = malloc((size_t)N * 8), moved, chg;
            int passes;
            if (!orig || !evo || !perm || !opt)
                DIE("out of memory");
            memcpy(ev2, cur, (size_t)N * sizeof(Ev));
            i64 g = bs_once(&b, ev2, N, orig, evo, perm, opt, &moved, &chg, &passes);
            free(orig);
            free(evo);
            free(perm);
            free(opt);
            bs_free(&b);
            if (g > 0) {
                gain = g;
                memcpy(ev, ev2, (size_t)N * sizeof(Ev));
                printf("sequences of equal length: number %lld has a shorter one within --bs %d: %lld -> %lld\n", head,
                       bsK, l0, l0 - g);
                break;
            }
        }
        i64 g = o3_round(&o, cur), neq = 0, nz = 0;
        o3_nround++;
        if (g > 0) {
            O3M m = o.mv[0];
            o3_permute(cur, ev2, N, &m);
            co_run(&q, ev2, N, 0, N - 1, 0, NULL);
            i64 l1 = seq_length(ev2, N);
            if (l0 - l1 != g)
                DIE("internal error: segment insertion promised %lld, got %lld", g, l0 - l1);
            gain = g;
            memcpy(ev, ev2, (size_t)N * sizeof(Ev));
            printf("sequences of equal length: number %lld has a shorter neighbour (", head);
            o3_print(&o, &m, N);
            printf("): %lld -> %lld\n", l0, l1);
            if (o3plan)
                write_plan(ev, N, o3plan);
            break;
        }
        for (i64 k = 0; k < o.nc && o.mv[k].gx == 0; k++) {
            const O3M *m = &o.mv[k];
            nz++;
            o3_permute(cur, ev2, N, m);
            u64 hv = o3_hash(ev2, N);
            int dup = 0;
            for (i64 z = 0; z < nseen; z++)
                if (seen[z] == hv) {
                    dup = 1;
                    break;
                }
            if (dup)
                continue;
            if (nseen == scap) {
                scap *= 2;
                seen = realloc(seen, (size_t)scap * 8);
                if (!seen)
                    DIE("out of memory");
            }
            seen[nseen++] = hv;
            neq++;
            if (nq < cap) {
                Q[nq] = malloc((size_t)N * sizeof(Ev));
                if (!Q[nq])
                    DIE("out of memory");
                memcpy(Q[nq++], ev2, (size_t)N * sizeof(Ev));
            }
        }
        printf(
            "sequences of equal length: number %lld of %lld: %lld candidates, %lld of equal length, %lld new (%.0fs)\n",
            head, nq, o.nc, nz, neq, wall() - t0);
        fflush(stdout);
    }
    printf("sequences of equal length: %lld expanded, %lld found, gain %lld (%.0fs)\n", head, nq, gain, wall() - t0);
    fflush(stdout);
    for (i64 k = 0; k < nq; k++)
        free(Q[k]);
    free(Q);
    free(ev2);
    free(seen);
    o3_cofree(&q);
    o3_done(&o);
    return gain;
}

/* ==================== shared base again: the search, the loader, main (it runs --co, --bs, --or3 before the search) ==================== */
/* ---------- shared best sequence */
static CO G_co;
static i64 G_cow[3];
static double G_cosec; /* in the search: windows, windows with a gain, letters gained; seconds */
static Ev *G_ev;
static i64 G_N, G_len;
static int G_dirty;
static double G_t0, G_last_ck, G_last_log;
static i64 G_it[256];
static double wall(void);

/* One search thread.  Until the time or the iteration limit: choose trails to remove, take them out, put each
   back (greedy order or random order, with or without noise), accept or undo by the annealing rule.  A new best
   sequence goes to the shared copy G_ev under the lock gbest; odd threads adopt the shared best at sync time. */
static void search(Ctx *c, const Ev *init_ev, i64 initN, const char *outplan) {
    rseed(c, seed * 1000003ULL + (u64)c->tid * 7919ULL);
    c->rem = calloc((size_t)NT + 1, 1);
    c->pend = malloc(((size_t)NT + 1) * sizeof(u32));
    ctx_load(c, init_ev, initN);
    c->cur = ctx_length(c);
    c->best_len = c->cur;
    double tf = NTHR > 1 ? 0.5 + (double)c->tid / (NTHR - 1) : 1.0, last_sync = wall();
    int runcap = 2 * kmax + 2; /* a run longer than this is not removed as a whole */
    Node *nd;
    CLog clog;
    memset(&clog, 0, sizeof clog);
    while ((maxit < 0 || c->it < maxit) && wall() - G_t0 < tlimit) {
        c->it++;
        if (c->H.n > c->H.cap - 40000 || c->nn > c->ncap - 4000) {
            i64 m = ctx_export(c, c->tmp);
            ctx_load(c, c->tmp, m);
        }
        if (coit > 0 && (c->it + coit * c->tid / NTHR) % coit ==
                            0) { /* cluster optimisation of the whole current sequence; the threads take turns */
            i64 m = ctx_export(c, c->tmp), g;
            int chg;
            double t1 = wall();
#pragma omp critical(co)
            g = co_run(&G_co, c->tmp, m, 0, m - 1, 0, &chg);
            clog.st[0]++;
            clog.st[1] += g > 0;
            clog.st[2] += g > 0 ? g : 0;
            clog.sec += wall() - t1;
            if (g > 0) {
                ctx_load(c, c->tmp, m);
                c->cur -= g;
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
        int *order = c->order, *dj = c->dj, *cand = c->cand, *rs_ = c->rs_, *re_ = c->re_, *rid = c->rid, *rel = c->rel;
        i64 N = 0;
        for (int id = c->first; id >= 0; id = nd[id].next)
            order[N++] = id;
#define EVT(i) (nd[order[i]].v)
        i64 ncand = 0;
        for (i64 i = 0; i + 1 < N; i++) {
            dj[i] = dist(EVT(i).e, EVT(i + 1).s);
            if (dj[i] >= 2)
                cand[ncand++] = (int)i;
        }
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
            int nrun = 0;
            rid[0] = 0;
            for (i64 i = 1; i < N; i++) {
                if (dj[i - 1] >= 2)
                    nrun++;
                rid[i] = nrun;
            }
            nrun++;
            for (i64 i = 0; i < N; i++) {
                if (i == 0 || rid[i] != rid[i - 1])
                    rs_[rid[i]] = (int)i;
                re_[rid[i]] = (int)i;
            }
            int X = -1;
            if (rndu(c) < 0.7) {
                for (int tries = 0; tries < 50; tries++) {
                    int r = (int)rndn(c, nrun);
                    if (re_[r] - rs_[r] + 1 <= 5) {
                        X = r;
                        break;
                    }
                }
            }
            if (X < 0)
                X = (int)rndn(c, nrun);
            i64 xlen = re_[X] - rs_[X] + 1;
            if (xlen > runcap) { /* long run: only a window of it */
                i64 lo = rs_[X] + rndn(c, xlen - k + 1 > 0 ? xlen - k + 1 : 1);
                for (i64 i = lo; i <= re_[X] && i < lo + k; i++)
                    REMOVE(EVT(i).t);
            } else {
                i64 nopt = 0;
                for (int i = rs_[X]; i <= re_[X]; i++)
                    nopt += TR[EVT(i).t].ohi - TR[EVT(i).t].olo;
                int nrel = 0;
                if (nopt <= 600000) {
                    h_reset(&c->RELT, nopt * 4 + 16);
                    for (int i = rs_[X]; i <= re_[X]; i++)
                        for (i64 o = TR[EVT(i).t].olo; o < TR[EVT(i).t].ohi; o++) {
                            u64 S = oS_t(&TR[EVT(i).t], o), E = oE_t(&TR[EVT(i).t], o);
                            h_add(&c->RELT, HKEY(S, 0, 4), 0);
                            h_add(&c->RELT, HKEY(S >> 4, 1, 4), 0);
                            h_add(&c->RELT, HKEY(E, 0, 5), 0);
                            h_add(&c->RELT, HKEY(E & HMASK[h - 1], 1, 5), 0);
                        }
                    for (int r = 0; r < nrun; r++) {
                        if (r == X || re_[r] - rs_[r] + 1 > runcap)
                            continue;
                        u64 e_end = EVT(re_[r]).e, s_st = EVT(rs_[r]).s;
                        if (h_get(&c->RELT, HKEY(e_end, 0, 4)) >= 0 ||
                            h_get(&c->RELT, HKEY(e_end & HMASK[h - 1], 1, 4)) >= 0 ||
                            h_get(&c->RELT, HKEY(s_st, 0, 5)) >= 0 || h_get(&c->RELT, HKEY(s_st >> 4, 1, 5)) >= 0)
                            rel[nrel++] = r;
                    }
                }
                for (int i = rs_[X]; i <= re_[X]; i++)
                    REMOVE(EVT(i).t);
                int want = (int)rndint(c, 1, 2);
                for (int q = 0; q < want && nrel > 0; q++) {
                    int z = (int)rndn(c, nrel), r = rel[z];
                    rel[z] = rel[--nrel];
                    for (int i = rs_[r]; i <= re_[r]; i++)
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
        /* destroy */
        c->nremlog = c->ninslog = 0;
        c->relabeled = 0;
        c->nskp = 0;
        for (i64 i = 0; i < N; i++) {
            int id = order[i];
            if (c->rem[nd[id].v.t]) {
                node_unlink(c, id);
                c->remlog[c->nremlog++] = id;
            } else if (nd[id].v.skip >= 0)
                skp_add(c, nd[id].v.skip);
        }
        for (i64 q = 0; q < nrem; q++)
            c->rem[c->pend[q]] = 0;
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
                i64 pick = 0;
                Ins bi = best_insertion(c, c->pend[0], noise);
                if (greedy) {
                    double br = rndu(c);
                    for (i64 q = 1; q < np; q++) {
                        Ins x = best_insertion(c, c->pend[q], noise);
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
                    node_insert_after(c, c->nd[sp.i].prev, &e1);
                    node_insert_after(c, sp.jm, &e2);
                } else {
                    Ev x = make_event(bi.opt);
                    node_insert_after(c, bi.after, &x);
                    if (x.skip >= 0)
                        skp_add(c, x.skip);
                }
                c->pend[pick] = c->pend[--np];
            }
            nl = ctx_length(c);
            i64 d = nl - c->cur;
            accept = d <= 0 || rndu(c) < exp(-(double)d / temp);
        }
        if (accept) {
            c->cur = nl;
            c->acc++;
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
            for (int q = c->ninslog - 1; q >= 0; q--)
                node_unlink(c, c->inslog[q]);
            for (int q = c->nremlog - 1; q >= 0; q--)
                node_relink(c, c->remlog[q]);
            if (c->relabeled)
                relabel(c);
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
    {
        G_it[c->tid] = c->it;
        for (int k = 0; k < 3; k++)
            G_cow[k] += clog.st[k];
        G_cosec += clog.sec;
    }
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

/* ==================== own part of this file, 4: cuts at vertices only (--gap3), in the loader ==================== */
/* ---------- --gap3: cuts at vertices only.  The loader keeps only the plain cuts at a step of weight 3 (gap 3, nothing
   extra to write) and no cut that drops a duplicate, and no trail is written in two segments.  Every pass then
   works on these cuts alone.  For a selection that transports, a sequence of its closed trails cut at vertices is,
   join for join, the top level of the problem one n higher (arrange/lift13.py), so with this option the passes
   optimise exactly what lifts.  A sequence that comes with other events is brought into the model by gap3_events
   below.
   --gap3-list FILE: of these only the vertices whose word (the h letters the piece begins and ends with) is in
   FILE, one word per line in the letters of the base word.  arrange/mkverts.py writes the list of the vertices at
   which the lift can cut a trail. */
static int gap3 = 0;
static const char *g3file = NULL;
static u64 *g3v = NULL;
static i64 g3n = 0;
static int g3_cmp(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return x < y ? -1 : x > y;
}
/* reads the list of --gap3-list: one h-word per line; sorted and without repeats afterwards */
static void gap3_load(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f)
        DIE("cannot open %s", path);
    char line[256];
    i64 cap = 1 << 16, m = 0;
    g3v = malloc((size_t)cap * 8);
    if (!g3v)
        DIE("out of memory");
    while (fgets(line, sizeof line, f)) {
        u64 v = 0;
        int k = 0;
        for (; line[k] && line[k] != '\n' && line[k] != '\r' && line[k] != ' '; k++) {
            const char *p = strchr(AL, line[k]);
            if (!p || k >= 16)
                DIE("%s: bad word %s", path, line);
            v = (v << 4) | (u64)(p - AL);
        }
        if (!k)
            continue;
        if (k != h)
            DIE("%s: a word of %d letters, the openings of this word have %d", path, k, h);
        if (g3n == cap) {
            cap *= 2;
            g3v = realloc(g3v, (size_t)cap * 8);
            if (!g3v)
                DIE("out of memory");
        }
        g3v[g3n++] = v;
    }
    fclose(f);
    qsort(g3v, (size_t)g3n, 8, g3_cmp);
    for (i64 k = 0; k < g3n; k++)
        if (!k || g3v[k] != g3v[k - 1])
            g3v[m++] = g3v[k];
    g3n = m;
    if (!g3n)
        DIE("%s: no words", path);
}
/* is the h-word w in the list? */
static inline int g3_listed(u64 w) {
    i64 a = 0, b = g3n;
    while (a < b) {
        i64 mid = (a + b) >> 1;
        if (g3v[mid] < w)
            a = mid + 1;
        else
            b = mid;
    }
    return a < g3n && g3v[a] == w;
}
/* cuts of trail t in window order; writes them to out (if not NULL) and returns their number */
static i64 trail_options(i64 t, i64 *wp, const u64 *dupb, Opt *out, i64 *hist, i64 *shist) {
    if (TR[t].fixed)
        return 0;
    i64 R = TR[t].R, m = trail_windows(&TR[t], wp), k = 0;
    for (i64 i = 0; i < m && m >= 2; i++) {
        i64 i1 = i + 1 == m ? 0 : i + 1, i2 = i1 + 1 == m ? 0 : i1 + 1;
        i64 g = (wp[i1] - wp[i] + R) % R;
        if (g >= 2 + gap3 &&
            (g > 3 || !g3v ||
             g3_listed(hw_cyc(&TR[t], wp[i1])))) { /* --gap3: only gap 3; --gap3-list: only the vertices listed */
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
        if (use_skip && !gap3 && m >= 3) {
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

/* --gap3: the cut of trail t at the nearest vertex at or after place st of its cyclic word; -1: it has none */
static i64 gap3_near(u32 t, i64 st) {
    const Trail *T = &TR[t];
    i64 best = -1, bd = 0;
    for (i64 o = T->olo; o < T->ohi; o++) {
        i64 d = ((i64)OP[o].start - st) % T->R;
        if (d < 0)
            d += T->R;
        if (best < 0 || d < bd) {
            best = o;
            bd = d;
        }
    }
    return best;
}
/* --gap3: the events of a sequence as cuts at vertices.  A cut stays (the loader has only those at vertices).  A
   piece that is its trail cut at a vertex becomes that cut (the same letters).  Any other piece or segment becomes
   the cut of its trail at the nearest vertex after its start, and if the trail was written in several events the
   others go.  Pieces that are no trail, and trails without a vertex, stay as they are.
   cnt: moved to a vertex, dropped, left.  Returns the new number of events. */
static i64 gap3_events(Ev *ev, i64 N, i64 *cnt) {
    char *seen = calloc((size_t)NT + 1, 1);
    i64 m = 0;
    if (!seen)
        DIE("out of memory");
    for (i64 i = 0; i < N; i++) {
        Ev x = ev[i];
        const Trail *T = &TR[x.t];
        i64 o = -1;
        if (x.kind == EV_OPT) {
            seen[x.t] = 1;
            ev[m++] = x;
            continue;
        }
        if (T->fixed || T->ohi == T->olo) {
            cnt[2]++;
            ev[m++] = x;
            continue;
        }
        if (seen[x.t]) {
            cnt[1]++;
            continue;
        }
        seen[x.t] = 1;
        if (x.kind == EV_PIECE && T->c == W + PS[x.a] && x.l == T->R + h)
            for (i64 z = T->olo; z < T->ohi; z++)
                if (!OP[z].start && x.s == oS_t(T, z) && x.e == oE_t(T, z)) {
                    o = z;
                    break;
                }
        if (o < 0) {
            o = gap3_near(x.t, x.kind == EV_SEG ? x.a : 0);
            cnt[0]++;
        }
        ev[m++] = make_event(o);
    }
    free(seen);
    return m;
}

/* Reads the options, loads the base word, splits it into pieces and closed trails, builds the table of cuts,
   loads the plan, runs the passes that were asked for and the search, and writes the plan and the word. */
int main(int argc, char **argv) {
    if (argc < 3)
        DIE("usage: segins_gpu BASE.txt OUT.txt --plan-in PLAN --time 0 --threads T --or3 C --or3-slack S [--or3-gpu] [--or3-eq E]   (see the comment at the top of segins_gpu.c)");
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
        else if (!strcmp(argv[a], "--coit") && a + 1 < argc)
            coit = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--co"))
            co_first = 1;
        else if (!strcmp(argv[a], "--co-skip"))
            co_first = co_skip = 1;
        else if (!strcmp(argv[a], "--bs") && a + 1 < argc)
            bsK = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--bs-test") && a + 1 < argc)
            bs_ntest = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3") && a + 1 < argc)
            o3cuts = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-slack") && a + 1 < argc)
            o3slack = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-v") && a + 1 < argc)
            o3th = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-plateau") && a + 1 < argc)
            o3plat = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-dry"))
            o3dry = 1;
        else if (!strcmp(argv[a], "--or3-old"))
            o3old = 1;
        else if (!strcmp(argv[a], "--or3-rounds") && a + 1 < argc)
            o3rounds = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-sec") && a + 1 < argc)
            o3sec = atof(argv[++a]);
        else if (!strcmp(argv[a], "--or3-stop") && a + 1 < argc)
            o3stopfile = argv[++a];
        else if (!strcmp(argv[a], "--or3-maxcand") && a + 1 < argc)
            o3maxcand = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-maxlay") && a + 1 < argc)
            o3maxlay = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-margin") && a + 1 < argc)
            o3margin = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-dip") && a + 1 < argc)
            o3dip = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-x") && a + 1 < argc)
            o3xt = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-zone") && a + 1 < argc)
            o3zone = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu"))
            og.on = 1;
        else if (!strcmp(argv[a], "--or3-gpu-check"))
            og.on = og.check = 1;
        else if (!strcmp(argv[a], "--or3-gpu-checkmax") && a + 1 < argc)
            og_chkmax = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-ms") && a + 1 < argc)
            og.ms = atof(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-bt") && a + 1 < argc)
            og.bt = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-blocks") && a + 1 < argc)
            og.nbuser = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-mem") && a + 1 < argc)
            og.memmb = atof(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-min") && a + 1 < argc)
            og_min = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-ptx") && a + 1 < argc)
            og.ptx = argv[++a];
        else if (!strcmp(argv[a], "--or3-gpu-nomemo"))
            og.nomemo = 1;
        else if (!strcmp(argv[a], "--or3-gpu-v"))
            og.verbose = 1;
        else if (!strcmp(argv[a], "--or3-gpu-nozones"))
            og.nozones = 1;
        else if (!strcmp(argv[a], "--or3-gpu-small") && a + 1 < argc)
            og.small = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-chunk") && a + 1 < argc)
            og.chunk = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-gpu-budget") && a + 1 < argc)
            og.fixbudget = atof(argv[++a]);
        else if (!strcmp(argv[a], "--or3-full"))
            o3full = 1;
        else if (!strcmp(argv[a], "--or3-check"))
            o3check = 1;
        else if (!strcmp(argv[a], "--or3-nojc"))
            o3nojc = 1;
        else if (!strcmp(argv[a], "--or3-nolu"))
            o3nolu = 1;
        else if (!strcmp(argv[a], "--or3-order") && a + 1 < argc)
            o3order = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-long") && a + 1 < argc)
            o3long = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-2pv") && a + 1 < argc)
            o32pv = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-noskip"))
            o3noskip = 1;
        else if (!strcmp(argv[a], "--or3-lupct") && a + 1 < argc)
            o3lupct = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-focus") && a + 1 < argc)
            o3focus = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-eq") && a + 1 < argc)
            o3q_eq = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-eq-max") && a + 1 < argc)
            o3q_max = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-eq-tabu") && a + 1 < argc)
            o3q_tabu = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-eq-stop") && a + 1 < argc)
            o3q_patience = atoi(argv[++a]);
        else if (!strcmp(argv[a], "--or3-eq-keep") && a + 1 < argc)
            o3q_keep = atoll(argv[++a]);
        else if ((!strcmp(argv[a], "--or3-eq-seed") || !strcmp(argv[a], "--or3-seed")) && a + 1 < argc) {
            u64 z = strtoull(argv[++a], NULL, 10);
            o3q_seedv = z;
            o3q_s[0] ^= z * 0x2545F4914F6CDD1DULL;
            o3q_s[1] ^= z << 17;
            for (int i = 0; i < 20; i++)
                o3q_rnd();
        } else if (!strcmp(argv[a], "--or3-hmem") && a + 1 < argc)
            o3h_mb = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-hcheck"))
            o3h_chk = 1;
        else if (!strcmp(argv[a], "--or3-hmax") && a + 1 < argc)
            o3h_max = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--or3-hrec") && a + 1 < argc)
            o3h_rec = atoll(argv[++a]);
        else if (!strcmp(argv[a], "--noskip"))
            use_skip = 0;
        else if (!strcmp(argv[a], "--gap3")) {
            gap3 = 1;
            use_split = 0;
        } else if (!strcmp(argv[a], "--gap3-list") && a + 1 < argc) {
            gap3 = 1;
            use_split = 0;
            g3file = argv[++a];
        } else if (!strcmp(argv[a], "--nosplit"))
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
    if (g3file)
        gap3_load(g3file);
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
    i64 N = 0, g3in = 0;
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
                if (o < 0 && gap3) {
                    o = gap3_near(t, st);
                    g3in++;
                    if (o < 0)
                        DIE("--gap3: trail %u of the plan has no cut at a vertex", t);
                } /* cut elsewhere: the nearest vertex after it */
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
    if (gap3) { /* every event becomes a cut at a vertex; if any had to move, the best cuts for this order follow */
        i64 l0 = seq_length(ev, N), g3[3] = {0};
        N = gap3_events(ev, N, g3);
        if (g3v)
            printf("gap3: %lld vertices listed, %lld of them are openings of this word\n", g3n, NO);
        printf(
            "gap3: %lld openings of the input were not at a vertex and were moved to the nearest one after, %lld events of trails written in several were dropped, %lld events left as they are (no trail, or no vertex); model length %lld -> %lld (%lld events)\n",
            g3in + g3[0], g3[1], g3[2], l0, seq_length(ev, N), N);
        fflush(stdout);
        if (g3in + g3[0] + g3[1])
            co_first = 1;
    }
    if (co_first)
        co_full(ev, N);
    if (bsK && bs_ntest)
        bs_test(ev, N, bsK, bs_ntest);
    if (bsK)
        bs_full(ev, N, bsK);
    if (o3cuts > 0) {
        static char pp[4096];
        snprintf(pp, sizeof pp, "%s.plan", argv[2]);
        o3plan = pp;
        o3_t0 = wall();
        og_argv0 = argv[0];
        for (;;) {
            i64 g =
                o3old
                    ? o3_full_old(ev, N)
                    : o3_full(ev, N); /* until nothing is shorter, or stopped; the plan is written after every round */
            if (o3_stop())
                break;
            if (g > 0 && bsK && bs_full(ev, N, bsK) > 0) {
                write_plan(ev, N, pp);
                continue;
            }
            if (o3plat > 0 && o3_plateau(ev, N, o3plat) > 0)
                continue;
            break;
        }
        og_report();
    }
    /* ---------- destroy / repair search */
    char outplan[4096];
    snprintf(outplan, sizeof outplan, "%s.plan", argv[2]);
    G_ev = malloc((size_t)(4 * N + 65536) * sizeof(Ev));
    memcpy(G_ev, ev, (size_t)N * sizeof(Ev));
    G_N = N;
    G_len = seq_length(ev, N);
    G_t0 = G_last_ck = G_last_log = wall();
    if (tlimit > 0 && maxit != 0) { /* with --time 0 no thread loads the sequence */
#pragma omp parallel num_threads(NTHR)
        {
            Ctx *c = calloc(1, sizeof(Ctx));
            c->tid = omp_get_thread_num();
            search(c, ev, N, outplan);
        }
    }
    i64 tot = 0;
    for (int q = 0; q < NTHR; q++)
        tot += G_it[q];
    printf("LNS done: %lld iterations on %d threads, best %lld\n", tot, NTHR, G_len);
    fflush(stdout);
    if (coit > 0)
        printf("cluster optimisation in the search: %lld passes, %lld with a gain, %lld letters, %.1f thread-seconds\n",
               G_cow[0], G_cow[1], G_cow[2], G_cosec);
    if (tot > 0 && (co_first || coit > 0)) {
        co_full(G_ev, G_N);
        G_len = seq_length(G_ev, G_N);
    }
    if (tot > 0 && bsK) {
        bs_full(G_ev, G_N, bsK);
        G_len = seq_length(G_ev, G_N);
    }
    print_stats(G_ev, G_N);
    write_plan(G_ev, G_N, outplan);
    write_word(G_ev, G_N, argv[2], G_len);
    printf("wrote %s length %lld (%.0fs)\n", argv[2], G_len, wall() - t00);
    return 0;
}
