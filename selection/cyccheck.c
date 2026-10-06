/* cyccheck.c - connector cycles checked on the completion of a selection, with a completion of its own.

   An independent checker: plain C, nothing shared with the Python scripts of this directory.  It reads a selection
   of full and short rows on k = K + 1 symbols and a list of connector cycles, builds the completion on n = K + 2
   symbols from the definition, and reports which closed trails the cycles meet.

   Selection file: one line per 2-loop, "x T": x = the K letters other than the distinguished letter s (s = letter
   K) in the order of the state, T = F (full row, K classes), S (short row, K - 2 classes) or D (loop without a
   row).  Lines that start with # are comments.  (hybrid3.py --fsd and untransport.py --out write this notation.)

   Completion with the new letter z = K + 1 (Pantone, section 3):
     a row S(x, s; L) gives the K inserted slices S(x(i), s; L + 1) (i < L) and S(x(i), s; L) (i >= L), where x(i)
     is x with z inserted in front of x_i, and one repair slice for every missed class [rot^i(x) s], i = L .. K-1:
     the full slice with distinguished letter z that starts at rot^i(x) s z.  A loop without a row has L = 0: K
     repair slices.
   A slice S(y, d; v) on n symbols (y = n - 1 letters) has head = its first h = n - 3 letters = y[0 .. h-1] and
   tail = its last h letters = rot^(v+1)(y)[0 .. h-1]; it has (n + 1) v + 1 letters that are its own.

   The program checks that the number of slices is (n-2)! + Q, that every cyclic class on n symbols lies in exactly
   one slice, and that every head word has out-degree and in-degree one (so the closed trails are forced).  It
   follows the closed trails and prints their number, the sum of their lengths (F3(n) + Q) and the number of small
   trails (K repair slices of one loop without a row).

   Cycles file: one word of h letters per line (# = comment).  The cycle of the word v is v -> rot(v) -> .. -> v;
   it meets a closed trail when one of its h rotations is a head word on that trail.  The last two lines say how
   many cycles there are (with and without z), how many of their rotations are not vertices at all, and how many
   small trails and walk trails are met; the last words are ALL WALK TRAILS MET or NOT ALL WALK TRAILS MET.

   build:  gcc -O2 -o cyccheck cyccheck.c
   usage:  cyccheck SELECTION.txt CYCLES.txt            (n <= 12)
   needs:  a C compiler.
   cost:   measured here for the transportable 11-symbol selection and its 203 cycles (n = 12, 3.8 million slices):
           2 s, 0.2 GB. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

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
static int K, n, h, m1; /* m1 = n - 1 = letters of y */
typedef struct {
    u8 y[13];
    u8 d, v;
} Sl;
static Sl *SL;
static i64 NS;
static u32 *nxt; /* slice whose head is the tail of this slice */

/* head word of a slice (first h letters of y), 4 bits per letter */
static inline u64 head_key(const Sl *s) {
    u64 k = 0;
    for (int i = 0; i < h; i++)
        k = (k << 4) | s->y[i];
    return k;
}
/* tail word of a slice: the first h letters of y rotated by v + 1 */
static inline u64 tail_key(const Sl *s) {
    u64 k = 0;
    for (int i = 0; i < h; i++)
        k = (k << 4) | s->y[(s->v + 1 + i) % m1];
    return k;
}
/* order of 64-bit keys, for qsort */
static int cmp64(const void *a, const void *b) {
    u64 x = *(const u64 *)a, y = *(const u64 *)b;
    return x < y ? -1 : x > y;
}

/* append the slice S(y, d; v) to the list */
static void add_slice(const u8 *y, int d, int v) {
    memcpy(SL[NS].y, y, m1);
    SL[NS].d = (u8)d;
    SL[NS].v = (u8)v;
    NS++;
}

/* rank of the cyclic class of the n letters p (rotated so that letter 0 comes first), 0 .. (n-1)! - 1 */
static u64 class_rank(const u8 *p) {
    int z0 = 0;
    while (p[z0] != 0)
        z0++;
    u8 q[16];
    for (int i = 0; i < n - 1; i++)
        q[i] = p[(z0 + 1 + i) % n];
    u64 r = 0;
    for (int i = 0; i < n - 1; i++) {
        int c = 0;
        for (int j = i + 1; j < n - 1; j++)
            if (q[j] < q[i])
                c++;
        r = r * (u64)(n - 1 - i) + (u64)c;
    }
    return r;
}

/* closed trails */
static u32 *TS; /* slices in trail order */
static i64 *T0;
static i64 NT; /* trail t = TS[T0[t] .. T0[t+1]) */

/* read the selection, build and check the completion, follow the closed trails, then look up every rotation of
   every cycle among the head words */
int main(int argc, char **argv) {
    if (argc < 3)
        DIE("usage: cyccheck SELECTION.txt CYCLES.txt");
    FILE *f = fopen(argv[1], "r");
    if (!f)
        DIE("cannot open %s", argv[1]);
    char line[256];
    i64 cap = 1 << 16, NR = 0;
    u8 *RX = malloc(cap * 16);
    char *RT = malloc(cap);
    int map[256];
    for (int c = 0; c < 256; c++)
        map[c] = -1;
    for (int c = 0; c < 16; c++)
        map[(u8)AL[c]] = c;
    K = 0;
    while (fgets(line, sizeof line, f)) {
        if (line[0] == '#' || line[0] == '\n' || line[0] == '\r') {
            while (!strchr(line, '\n') && fgets(line, sizeof line, f)) {
            } /* the rest of a long comment line */
            continue;
        }
        int l = 0;
        while (line[l] && line[l] != ' ' && line[l] != '\t')
            l++;
        if (!K)
            K = l;
        else if (l != K)
            DIE("bad line %s", line);
        char ty = line[l + 1];
        if (ty != 'F' && ty != 'S' && ty != 'D')
            DIE("bad type in %s", line);
        if (NR == cap) {
            cap *= 2;
            RX = realloc(RX, cap * 16);
            RT = realloc(RT, cap);
        }
        unsigned mask = 0;
        for (int i = 0; i < K; i++) {
            int v = map[(u8)line[i]];
            if (v < 0 || v >= K)
                DIE("bad letter in %s", line);
            RX[NR * 16 + i] = (u8)v;
            mask |= 1u << v;
        }
        if (mask != (1u << K) - 1)
            DIE("not an ordering of the %d letters: %s", K, line);
        RT[NR++] = ty;
    }
    fclose(f);
    n = K + 2;
    h = n - 3;
    m1 = n - 1;
    int s = K, z = K + 1;
    if (n > 12)
        DIE("n <= 12 only");
    u64 fact[16];
    fact[0] = 1;
    for (int i = 1; i < 16; i++)
        fact[i] = fact[i - 1] * (u64)i;
    if ((u64)NR != fact[K - 1])
        DIE("%lld rows, expected (k-2)! = %llu", NR, fact[K - 1]);
    i64 nF = 0, nS = 0, nD = 0;
    for (i64 r = 0; r < NR; r++) {
        if (RT[r] == 'F')
            nF++;
        else if (RT[r] == 'S')
            nS++;
        else
            nD++;
    }
    printf("selection on k = %d symbols: %lld loops, full %lld, short %lld, without slice %lld; Q = %lld\n", K + 1, NR,
           nF, nS, nD, 2 * nS);
    /* completion */
    SL = malloc((size_t)(NR * K + 2 * nS + 16) * sizeof(Sl));
    NS = 0;
    for (i64 r = 0; r < NR; r++) {
        const u8 *x = RX + r * 16;
        int L = RT[r] == 'F' ? K : RT[r] == 'S' ? K - 2 : 0;
        u8 y[16];
        if (L)
            for (int i = 0; i < K; i++) {
                for (int a = 0; a < i; a++)
                    y[a] = x[a];
                y[i] = (u8)z;
                for (int a = i; a < K; a++)
                    y[a + 1] = x[a];
                add_slice(y, s, i < L ? L + 1 : L);
            }
        for (int i = L; i < K; i++) {
            for (int a = 0; a < K; a++)
                y[a] = x[(i + a) % K];
            y[K] = (u8)s;
            add_slice(y, z, K + 1);
        }
    }
    if ((u64)NS != fact[n - 2] + (u64)(2 * nS))
        DIE("slice count %lld is not (n-2)! + Q", NS);
    printf("completion on n = %d symbols: %lld slices = (n-2)! + Q\n", n, NS);
    /* every cyclic class exactly once */
    {
        u64 NC = fact[n - 1];
        u64 *bm = calloc((size_t)(NC >> 6) + 1, 8);
        u64 cnt = 0;
        u8 p[16];
        for (i64 a = 0; a < NS; a++)
            for (int j = 0; j < SL[a].v; j++) {
                for (int i = 0; i < m1; i++)
                    p[i] = SL[a].y[(j + i) % m1];
                p[m1] = SL[a].d;
                u64 r = class_rank(p), bit = 1ULL << (r & 63);
                if (bm[r >> 6] & bit)
                    DIE("a cyclic class lies in two slices");
                bm[r >> 6] |= bit;
                cnt++;
            }
        if (cnt != NC)
            DIE("%llu classes covered, expected (n-1)! = %llu", cnt, NC);
        printf("every one of the %llu cyclic classes lies in exactly one slice\n", NC);
        free(bm);
    }
    /* endpoint graph: next slice */
    {
        u64 *hk = malloc((size_t)NS * 8);
        for (i64 a = 0; a < NS; a++)
            hk[a] = (head_key(&SL[a]) << 24) | (u64)a;
        qsort(hk, (size_t)NS, 8, cmp64);
        for (i64 a = 1; a < NS; a++)
            if ((hk[a] >> 24) == (hk[a - 1] >> 24))
                DIE("a head word has out-degree 2");
        nxt = malloc((size_t)NS * 4);
        u8 *indeg = calloc((size_t)NS, 1);
        for (i64 a = 0; a < NS; a++) {
            u64 key = tail_key(&SL[a]);
            i64 lo = 0, hi = NS - 1;
            while (lo < hi) {
                i64 mid = (lo + hi) >> 1;
                if ((hk[mid] >> 24) < key)
                    lo = mid + 1;
                else
                    hi = mid;
            }
            if ((hk[lo] >> 24) != key)
                DIE("a tail word is not a head word: the endpoint graph is not balanced");
            nxt[a] = (u32)(hk[lo] & 0xFFFFFF);
            if (indeg[nxt[a]]++)
                DIE("a head word has in-degree 2");
        }
        free(hk);
        free(indeg);
        printf("endpoint graph: every vertex has in-degree and out-degree one\n");
    }
    /* trails */
    {
        u8 *seen = calloc((size_t)NS, 1);
        TS = malloc((size_t)NS * 4);
        T0 = malloc((size_t)(NS + 1) * 8);
        NT = 0;
        i64 q = 0;
        for (i64 a = 0; a < NS; a++)
            if (!seen[a]) {
                T0[NT++] = q;
                i64 b = a;
                do {
                    seen[b] = 1;
                    TS[q++] = (u32)b;
                    b = nxt[b];
                } while (b != a);
            }
        T0[NT] = q;
        free(seen);
    }
    /* R = cyclic length of a closed trail: every slice adds (n + 1) v + 1 letters of its own */
    i64 sumR = 0, maxR = 0, minR = 1LL << 60;
    for (i64 t = 0; t < NT; t++) {
        i64 R = 0;
        for (i64 a = T0[t]; a < T0[t + 1]; a++)
            R += (n + 1) * SL[TS[a]].v + 1;
        sumR += R;
        if (R > maxR)
            maxR = R;
        if (R < minR)
            minR = R;
    }
    u64 F3 = fact[n] + fact[n - 1] + fact[n - 2];
    printf("closed trails %lld; sum R = %lld = F3(%d) + %lld; R from %lld to %lld\n", NT, sumR, n, sumR - (i64)F3, minR,
           maxR);
    {
        i64 small = 0;
        for (i64 t = 0; t < NT; t++) {
            if (T0[t + 1] - T0[t] == K) {
                int allz = 1;
                for (i64 a = T0[t]; a < T0[t + 1]; a++)
                    if (SL[TS[a]].d != z)
                        allz = 0;
                small += allz;
            }
        }
        printf("trails of K repair slices (loops without slice): %lld\n", small);
    }
    /* cycles: sort the head words, mark the trail of every head word that is a rotation of a cycle */
    {
        FILE *c = fopen(argv[2], "r");
        if (!c)
            DIE("cannot open %s", argv[2]);
        u64 *hk = malloc((size_t)NS * 8);
        for (i64 a = 0; a < NS; a++)
            hk[a] = (head_key(&SL[a]) << 24) | (u64)a;
        qsort(hk, (size_t)NS, 8, cmp64);
        u32 *tr_of = malloc((size_t)NS * 4);
        for (i64 t = 0; t < NT; t++)
            for (i64 a = T0[t]; a < T0[t + 1]; a++)
                tr_of[TS[a]] = (u32)t;
        if (NT <= 0)
            DIE("no closed trails");
        u8 *small = calloc((size_t)NT, 1), *met = calloc((size_t)NT, 1);
        for (i64 t = 0; t < NT; t++) {
            int allz = (T0[t + 1] - T0[t] == K);
            for (i64 a = T0[t]; a < T0[t + 1] && allz; a++)
                if (SL[TS[a]].d != z)
                    allz = 0;
            small[t] = (u8)allz;
        }
        i64 nc = 0, nz = 0, notv = 0;
        char ln[256];
        while (fgets(ln, sizeof ln, c)) {
            if (ln[0] == '#' || ln[0] == '\n' || ln[0] == '\r') {
                while (!strchr(ln, '\n') && fgets(ln, sizeof ln, c)) {
                } /* the rest of a long comment line */
                continue;
            }
            u8 w[16];
            unsigned mask = 0;
            int hasz = 0;
            for (int i = 0; i < h; i++) {
                int v = map[(u8)ln[i]];
                if (v < 0 || v == s || v > z || ((mask >> v) & 1))
                    DIE("bad cycle %s", ln);
                mask |= 1u << v;
                w[i] = (u8)v;
                if (v == z)
                    hasz = 1;
            }
            nc++;
            nz += hasz;
            for (int j = 0; j < h; j++) {
                u64 key = 0;
                for (int i = 0; i < h; i++)
                    key = (key << 4) | w[(j + i) % h];
                i64 lo = 0, hi = NS - 1;
                while (lo < hi) {
                    i64 mid = (lo + hi) >> 1;
                    if ((hk[mid] >> 24) < key)
                        lo = mid + 1;
                    else
                        hi = mid;
                }
                if ((hk[lo] >> 24) == key)
                    met[tr_of[hk[lo] & 0xFFFFFF]] = 1;
                else
                    notv++;
            }
        }
        fclose(c);
        i64 ns = 0, nw = 0, ms = 0, mw = 0;
        for (i64 t = 0; t < NT; t++) {
            if (small[t]) {
                ns++;
                ms += met[t];
            } else {
                nw++;
                mw += met[t];
            }
        }
        printf("cycles %lld (%lld with z, %lld without); rotations that are not vertices: %lld\n", nc, nz, nc - nz,
               notv);
        printf("small trails met: %lld of %lld; walk trails met: %lld of %lld -> %s\n", ms, ns, mw, nw,
               mw == nw ? "ALL WALK TRAILS MET" : "NOT ALL WALK TRAILS MET");
    }
    return 0;
}
