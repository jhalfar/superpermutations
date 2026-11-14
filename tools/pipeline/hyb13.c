/* hyb13.c - a base word for the selection of a word that changes a few trails of a base N (n = 13).

   usage: hyb13 BASE_N.txt WORD.txt NEWBASE.txt

   Both words are parsed as trailsearch.c parses them (pieces split at window gaps >= 4).  BASE_N has only closed
   pieces (trail = piece, R = len - h).  A piece of WORD is closed when it writes its cyclic word once from a gap-3,
   gap-2 or gap-1 opening (trailsearch's closes(k, 0/1/2)).  Every trail is identified by its set of windows
   (order-free sum of a hash of the window ranks, plus R).
     - a closed piece of WORD with the window set of a trail of N is that trail;
     - the other closed pieces of WORD are new trails;
     - a trail of N that shares a window with a new trail is dropped (the word has changed it), the others are kept;
     - open pieces of WORD that hold windows covered by neither are written as they are (trailsearch reads them as
       open paths and never moves them).
   NEWBASE = kept trails of N (in N's order, letter for letter) + new trails (letter for letter from WORD) + those open
   pieces, two separator letters between pieces (a letter that no window across the junction can use, so no new
   window appears and the pieces stay apart).  Checked here: the windows of NEWBASE's pieces cover all n!.
   Memory: both words at 4 bits a letter, two bitmaps of n! bits (about 8.5 GB for n = 13). */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#ifdef _OPENMP
#include <omp.h>
#endif

typedef long long i64;
typedef unsigned long long u64;
#define DIE(...) do { fprintf(stderr, "hyb13: " __VA_ARGS__); fprintf(stderr, "\n"); exit(2); } while (0)
static const int n = 13, h = 10;
static u64 fact[17];

typedef struct { unsigned char *a; i64 len; } Packed;
static inline int G(const Packed *p, i64 i) { return (p->a[i >> 1] >> ((i & 1) << 2)) & 15; }

static Packed load(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) DIE("cannot open %s", path);
    _fseeki64(f, 0, SEEK_END); i64 sz = _ftelli64(f); _fseeki64(f, 0, SEEK_SET);
    Packed p; p.a = calloc((size_t)(sz / 2 + 16), 1); p.len = 0;
    if (!p.a) DIE("out of memory");
    static unsigned char buf[1 << 24];
    size_t r;
    while ((r = fread(buf, 1, sizeof buf, f)) > 0)
        for (size_t i = 0; i < r; i++) {
            int c = buf[i];
            if (c == '\r' || c == '\n') continue;
            int v = c >= '0' && c <= '9' ? c - '0' : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
            if (v < 0 || v >= n) DIE("bad symbol in %s", path);
            p.a[p.len >> 1] |= (unsigned char)(v << ((p.len & 1) << 2));
            p.len++;
        }
    fclose(f);
    return p;
}

/* pieces of a word: start, length, R of the cyclic word (0 = open) */
typedef struct { i64 s, l, R; } Piece;
static Piece *pieces(const Packed *w, i64 *np) {
    i64 cap = 1 << 16, m = 0; Piece *P = malloc(cap * sizeof(Piece));
    int cnt[16] = {0}, distinct = 0; i64 prev = -1, pstart = -1;
    for (i64 i = 0; i < w->len; i++) {
        if (cnt[G(w, i)]++ == 0) distinct++;
        if (i >= n && --cnt[G(w, i - n)] == 0) distinct--;
        if (i < n - 1 || distinct != n) continue;
        i64 p = i - n + 1;
        if (prev < 0) pstart = p;
        else if (p - prev >= 4) {
            if (m == cap) { cap *= 2; P = realloc(P, cap * sizeof(Piece)); }
            P[m].s = pstart; P[m].l = prev + n - pstart; P[m].R = 0; m++; pstart = p;
        }
        prev = p;
    }
    if (m == cap) { cap *= 2; P = realloc(P, cap * sizeof(Piece)); }
    P[m].s = pstart; P[m].l = prev + n - pstart; P[m].R = 0; m++;
    /* closed from a gap-3 / gap-2 / gap-1 opening, as trailsearch's closes(k, ex) */
#pragma omp parallel for schedule(dynamic, 64)
    for (i64 k = 0; k < m; k++)
        for (int ex = 0; ex <= 2 && !P[k].R; ex++) {
            i64 R = P[k].l - h - ex; if (R <= 2 * n) continue;
            int ok = 1;
            for (int j = 0; j < h + ex && ok; j++) ok = G(w, P[k].s + R + j) == G(w, P[k].s + j);
            if (ok) P[k].R = R;
        }
    *np = m;
    return P;
}

static inline int Tc(const Packed *w, const Piece *p, i64 o) { o %= p->R; return G(w, p->s + o); }
/* rank of the window at cyclic offset o (closed piece) or linear offset o (open piece); -1 if not a permutation */
static inline i64 rank_at(const Packed *w, const Piece *p, i64 o) {
    unsigned used = 0; u64 r = 0;
    for (int j = 0; j < n; j++) {
        int c = p->R ? Tc(w, p, o + j) : G(w, p->s + o + j);
        if (used >> c & 1) return -1;
        r += (u64)(c - __builtin_popcount(used & ((1u << c) - 1))) * fact[n - 1 - j];
        used |= 1u << c;
    }
    return (i64)r;
}
static inline i64 nwin(const Piece *p) { return p->R ? p->R : p->l - n + 1; }
static inline u64 mix(u64 x) {
    x += 0x9E3779B97F4A7C15ULL; x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ULL;
    x = (x ^ (x >> 27)) * 0x94D049BB133111EBULL; return x ^ (x >> 31);
}
static u64 sethash(const Packed *w, const Piece *p) {
    u64 s = 0;
    for (i64 o = 0; o < nwin(p); o++) { i64 r = rank_at(w, p, o); if (r >= 0) s += mix((u64)r); }
    return s ^ mix((u64)p->R * 0x100000001ULL);
}
static inline void setbit(u64 *b, u64 r) { __atomic_fetch_or(&b[r >> 6], 1ULL << (r & 63), __ATOMIC_RELAXED); }
static inline int getbit(const u64 *b, u64 r) { return b[r >> 6] >> (r & 63) & 1; }

typedef struct { u64 key; i64 t; } KT;
static int cmpkt(const void *x, const void *y) { u64 a = ((const KT *)x)->key, b = ((const KT *)y)->key; return a < b ? -1 : a > b; }

static double t00;
static double wall(void) { return (double)clock() / CLOCKS_PER_SEC - t00; }

/* How a piece is written into NEWBASE: an open piece and a closed piece of a gap-3 opening (l = R + h) letter for
   letter; a closed piece of a gap-2 / gap-1 opening rotated to a gap-3 opening (a window whose previous window lies 3
   back), so that trailsearch numbers every closed trail in the order of the pieces (it numbers closes(k, 0) pieces
   first) and w2p13 reads it as closed.  rot < 0: no gap-3 opening, written as it is. */
static i64 gap3_opening(const Packed *w, const Piece *p) {
    if (!p->R || p->l == p->R + h) return 0;
    for (i64 o = 0; o < p->R; o++)
        if (rank_at(w, p, o) >= 0 && rank_at(w, p, o + p->R - 3) >= 0) return o;
    return -1;
}
/* written from offset rot of the cyclic word (R + h letters), or letter for letter (open piece, or rot < 0) */
static inline int letter(const Packed *w, const Piece *p, i64 rot, i64 i) {
    return p->R && rot >= 0 ? Tc(w, p, rot + i) : G(w, p->s + i);
}
static inline i64 outlen(const Piece *p, i64 rot) { return rot >= 0 && p->R ? p->R + h : p->l; }
static void put(FILE *f, const Packed *w, const Piece *p, i64 rot) {
    static char buf[1 << 20]; int q = 0;
    for (i64 i = 0, L = outlen(p, rot); i < L; i++) {
        buf[q++] = "0123456789ABCDEF"[letter(w, p, rot, i)];
        if (q == sizeof buf) { fwrite(buf, 1, q, f); q = 0; }
    }
    if (q) fwrite(buf, 1, q, f);
}

int main(int argc, char **argv) {
    if (argc != 4) DIE("usage: hyb13 BASE_N.txt WORD.txt NEWBASE.txt");
    fact[0] = 1; for (int i = 1; i < 17; i++) fact[i] = fact[i - 1] * i;
    u64 NF = fact[n];
    Packed Bn = load(argv[1]), Wd = load(argv[2]);
    i64 nb, nw;
    Piece *PB = pieces(&Bn, &nb), *PW = pieces(&Wd, &nw);
    i64 nbc = 0, nwc = 0, nwo = 0;
    for (i64 k = 0; k < nb; k++) nbc += PB[k].R > 0;
    for (i64 k = 0; k < nw; k++) { nwc += PW[k].R > 0; nwo += PW[k].R == 0; }
    printf("base N: %lld letters, %lld pieces (%lld closed); word: %lld letters, %lld pieces (%lld closed, %lld open) (%.0fs)\n",
           Bn.len, nb, nbc, Wd.len, nw, nwc, nwo, wall()); fflush(stdout);
    if (nbc != nb) DIE("base N has open pieces");
    /* window-set hashes */
    KT *HB = malloc(nb * sizeof(KT)); u64 *HW = malloc(nw * 8);
#pragma omp parallel for schedule(dynamic, 8)
    for (i64 k = 0; k < nb; k++) { HB[k].key = sethash(&Bn, &PB[k]); HB[k].t = k; }
#pragma omp parallel for schedule(dynamic, 8)
    for (i64 k = 0; k < nw; k++) HW[k] = PW[k].R ? sethash(&Wd, &PW[k]) : 0;
    qsort(HB, nb, sizeof(KT), cmpkt);
    printf("hashes (%.0fs)\n", wall()); fflush(stdout);
    char *matchedB = calloc(nb, 1), *isnew = calloc(nw, 1);
    i64 nmatch = 0, nnew = 0, Rnew = 0;
    for (i64 k = 0; k < nw; k++) {
        if (!PW[k].R) continue;
        i64 lo = 0, hi = nb;
        while (lo < hi) { i64 mid = (lo + hi) / 2; if (HB[mid].key < HW[k]) lo = mid + 1; else hi = mid; }
        if (lo < nb && HB[lo].key == HW[k] && PB[HB[lo].t].R == PW[k].R) { matchedB[HB[lo].t] = 1; nmatch++; }
        else { isnew[k] = 1; nnew++; Rnew += PW[k].R; }
    }
    printf("closed pieces of the word: %lld are trails of N, %lld new (sum R %lld)\n", nmatch, nnew, Rnew); fflush(stdout);
    /* windows of the new trails; N trails that touch them are dropped */
    u64 *NEW = calloc(NF / 64 + 1, 8), *COV = calloc(NF / 64 + 1, 8), *DUPN = calloc(NF / 64 + 1, 8);
    if (!NEW || !COV || !DUPN) DIE("out of memory");
    /* windows that two trails of N share (COV as the seen-bitmap first): sharing one of them drops nothing */
#pragma omp parallel for schedule(dynamic, 8)
    for (i64 t = 0; t < nb; t++)
        for (i64 o = 0; o < PB[t].R; o++) {
            i64 r = rank_at(&Bn, &PB[t], o); if (r < 0) continue;
            u64 old = __atomic_fetch_or(&COV[r >> 6], 1ULL << (r & 63), __ATOMIC_RELAXED);
            if (old >> (r & 63) & 1) setbit(DUPN, (u64)r);
        }
    memset(COV, 0, (NF / 64 + 1) * 8);
#pragma omp parallel for schedule(dynamic, 1)
    for (i64 k = 0; k < nw; k++) if (isnew[k])
        for (i64 o = 0; o < nwin(&PW[k]); o++) { i64 r = rank_at(&Wd, &PW[k], o); if (r >= 0) { setbit(NEW, (u64)r); setbit(COV, (u64)r); } }
    char *drop = calloc(nb, 1); i64 ndrop = 0, Rdrop = 0, nkeepun = 0;
#pragma omp parallel for schedule(dynamic, 8) reduction(+:ndrop, Rdrop)
    for (i64 t = 0; t < nb; t++) {
        if (matchedB[t]) continue;
        for (i64 o = 0; o < PB[t].R; o++) { i64 r = rank_at(&Bn, &PB[t], o); if (r >= 0 && getbit(NEW, (u64)r) && !getbit(DUPN, (u64)r)) { drop[t] = 1; break; } }
        if (drop[t]) { ndrop++; Rdrop += PB[t].R; }
    }
    for (i64 t = 0; t < nb; t++) nkeepun += !matchedB[t] && !drop[t];
    printf("trails of N: %lld written whole in the word, %lld written in parts and kept, %lld dropped (sum R %lld) (%.0fs)\n",
           nb - ndrop - nkeepun, nkeepun, ndrop, Rdrop, wall());
    for (i64 t = 0, c = 0; t < nb && c < 40; t++) if (drop[t]) { printf("  dropped N trail %lld (R %lld)\n", t, PB[t].R); c++; }
    fflush(stdout);
#pragma omp parallel for schedule(dynamic, 8)
    for (i64 t = 0; t < nb; t++) if (!drop[t])
        for (i64 o = 0; o < PB[t].R; o++) { i64 r = rank_at(&Bn, &PB[t], o); if (r >= 0) setbit(COV, (u64)r); }
    /* open pieces (and closed pieces that are neither) with uncovered windows */
    char *need = calloc(nw, 1); i64 nneed = 0, Lneed = 0;
    for (i64 k = 0; k < nw; k++) {
        if (isnew[k] || PW[k].R) continue;
        int miss = 0;
        for (i64 o = 0; o < nwin(&PW[k]) && !miss; o++) { i64 r = rank_at(&Wd, &PW[k], o); if (r >= 0 && !getbit(COV, (u64)r)) miss = 1; }
        if (miss) {
            need[k] = 1; nneed++; Lneed += PW[k].l;
            for (i64 o = 0; o < nwin(&PW[k]); o++) { i64 r = rank_at(&Wd, &PW[k], o); if (r >= 0) setbit(COV, (u64)r); }
            if (nneed <= 40) printf("  open piece %lld at letter %lld, %lld letters, kept as an open path\n", k, PW[k].s, PW[k].l);
        }
    }
    u64 cov = 0;
    for (u64 i = 0; i < NF / 64 + 1; i++) cov += (u64)__builtin_popcountll(COV[i]);
    printf("open pieces written as they are: %lld (%lld letters); windows covered %llu of %llu (%.0fs)\n", nneed, Lneed, cov, NF, wall());
    fflush(stdout);
    if (cov != NF) DIE("NOT every permutation is covered; no base written");
    /* write: kept N trails, new trails, open pieces; separator s s with s not the letter missing on either side */
    FILE *f = fopen(argv[3], "wb"); if (!f) DIE("cannot write %s", argv[3]);
    i64 written = 0, npc = 0, nrot = 0, nlit = 0; int last = -1;
    for (int pass = 0; pass < 3; pass++) {
        i64 cnt = pass == 0 ? nb : nw;
        for (i64 k = 0; k < cnt; k++) {
            const Packed *w = pass == 0 ? &Bn : &Wd; const Piece *p = pass == 0 ? &PB[k] : &PW[k];
            if (pass == 0 && drop[k]) continue;
            if (pass == 1 && !isnew[k]) continue;
            if (pass == 2 && !need[k]) continue;
            i64 rot = gap3_opening(w, p);
            if (p->R && p->l != p->R + h) { if (rot >= 0) nrot++; else nlit++; }
            if (last >= 0) {            /* s: not the letter missing from the n - 1 letters on either side */
                int mnext = letter(w, p, rot, n - 1), s = 0;
                while (s == last || s == mnext) s++;
                char sep[2] = { "0123456789ABCDEF"[s], "0123456789ABCDEF"[s] };
                fwrite(sep, 1, 2, f); written += 2;
            }
            put(f, w, p, rot); written += outlen(p, rot); npc++;
            last = letter(w, p, rot, outlen(p, rot) - n);
        }
    }
    fclose(f);
    printf("wrote %s: %lld letters, %lld pieces (%lld kept trails of N, %lld new trails, %lld open paths); "
           "%lld trails rotated to a gap-3 opening, %lld with none (written as they are) (%.0fs)\n",
           argv[3], written, npc, nb - ndrop, nnew, nneed, nrot, nlit, wall());
    return 0;
}
