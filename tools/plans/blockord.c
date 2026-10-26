/* blockord.c - internal order of one block segment for liftB.
   The segment of d (its 440 small units of R and the 14 level-4 walks of its block) is the same for every d up to a
   relabelling of the letters, and overlaps are invariant under relabelling, so its internal join cost is the same for
   every d: the order is optimised once, on d = 0.  Cost of an order = exact DP over the openings (as lift17: join cost
   h - overlap of the last h letters of one unit and the first h of the next), free at both ends of the segment.
   Search: start from the order of d's trails in the lower plan (R only) with the walk units inserted greedily, then
   relocation of single units and of runs of 2..RUN units to the best place (forward / backward DP arrays make every
   trial insertion O(candidates x h)), until no move improves.
   usage: blockord SEL LOWERPLAN(n = 15) OUT.order [--run R] [--d D]      (env GENB_BLOCK; L = 4)
   Prints the cost of the start order and of the final one. */
#define GEN15_NO_MAIN
#include "../../recipes/n17/genBt.c"

static u64 packh(const u8 *w) { u64 v = 0; for (int i = 0; i < HH; i++) v = v << 4 | w[i]; return v; }
typedef struct { int k; int g[3]; int w; int b; int n; u64 *S, *E; } BU;   /* k 0 = D (g), 1 = W (walk w, index b) */
static BU bu[1000]; static int NB;
static void bu_cands(BU *u) {
    if (u->k == 0) {
        u8 y[24], r[24]; int g[5] = {u->g[0], u->g[1], u->g[2], 0, 0}; small_y(0, g, y);
        u->n = HH; u->S = malloc(8 * HH); u->E = malloc(8 * HH);
        for (int j = 0; j < HH; j++) { rot(r, y, HH, j); u->S[j] = packh(r); rot(r, y, HH, j - 1); u->E[j] = packh(r); }
    } else {
        load_walk(u->w); u64 a = wbeg(u->w), m = wlen(u->w); u8 b[24], t[24]; int n = 0;
        u->S = malloc(16 * m); u->E = malloc(16 * m);
        for (u64 i = 0; i < m; i++) {
            if (rty(wrow[a + i])) continue;
            unpackK(wrow[a + i], b);
            u->S[n] = packh(b); t[0] = b[K - 1]; memcpy(t + 1, b, HH - 1); u->E[n] = packh(t); n++;
            u->S[n] = packh(b + 1); u->E[n] = packh(b); n++;
        }
        u->n = n;
    }
}
/* best[c] = min over a of fa[a] + cost(E_a, S_c), cost = h - largest overlap */
static inline int ovl(u64 e, u64 s) { for (int q = HH; q >= 1; q--) if ((e & ((1ULL << (4 * q)) - 1)) == (s >> (4 * (HH - q)))) return q; return 0; }
static void fwd(const BU *A, const int *fa, const BU *B, int *out) {
    int mn = 1 << 30; for (int a = 0; a < A->n; a++) if (fa[a] < mn) mn = fa[a];
    for (int c = 0; c < B->n; c++) {
        int best = mn + HH;
        for (int a = 0; a < A->n; a++) { if (fa[a] >= best) continue; int v = fa[a] + HH - ovl(A->E[a], B->S[c]); if (v < best) best = v; }
        out[c] = best;
    }
}
static void bwd(const BU *A, int *out, const BU *B, const int *gb) {   /* out[a] = min over c of cost(E_a, S_c) + gb[c] */
    int mn = 1 << 30; for (int c = 0; c < B->n; c++) if (gb[c] < mn) mn = gb[c];
    for (int a = 0; a < A->n; a++) {
        int best = mn + HH;
        for (int c = 0; c < B->n; c++) { if (gb[c] >= best) continue; int v = gb[c] + HH - ovl(A->E[a], B->S[c]); if (v < best) best = v; }
        out[a] = best;
    }
}
static int *F[1000], *G[1000];
static int seqcost(const int *ord, int n) {          /* forward DP over the order; fills F */
    for (int c = 0; c < bu[ord[0]].n; c++) F[0][c] = 0;
    for (int i = 1; i < n; i++) fwd(&bu[ord[i - 1]], F[i - 1], &bu[ord[i]], F[i]);
    int mn = 1 << 30; for (int c = 0; c < bu[ord[n - 1]].n; c++) if (F[n - 1][c] < mn) mn = F[n - 1][c];
    return mn;
}
static void backdp(const int *ord, int n) {
    for (int c = 0; c < bu[ord[n - 1]].n; c++) G[n - 1][c] = 0;
    for (int i = n - 2; i >= 0; i--) bwd(&bu[ord[i]], G[i], &bu[ord[i + 1]], G[i + 1]);
}
/* cost of inserting the run R (units r[0..m)) between positions k-1 and k of ord (k = 0: front, k = n: back) */
static int tmpA[1 << 16], tmpB[1 << 16];
static int ins_cost(const int *ord, int n, const int *r, int m, int k) {
    int *cur = tmpA, *nx = tmpB;
    if (k == 0) for (int c = 0; c < bu[r[0]].n; c++) cur[c] = 0;
    else fwd(&bu[ord[k - 1]], F[k - 1], &bu[r[0]], cur);
    for (int i = 1; i < m; i++) { fwd(&bu[r[i - 1]], cur, &bu[r[i]], nx); int *t = cur; cur = nx; nx = t; }
    const BU *last = &bu[r[m - 1]]; int best = 1 << 30;
    if (k == n) { for (int c = 0; c < last->n; c++) if (cur[c] < best) best = cur[c]; return best; }
    const BU *B = &bu[ord[k]];
    for (int c = 0; c < B->n; c++) {          /* min over last's cands a: cur[a] + cost(a, c), then + G[k][c] */
        int bb = 1 << 30;
        for (int a = 0; a < last->n; a++) { int v = cur[a] + HH - ovl(last->E[a], B->S[c]); if (v < bb) bb = v; }
        if (bb + G[k][c] < best) best = bb + G[k][c];
    }
    return best;
}

/* greedy edge start (--greedy T): states = (unit, opening); edges of cost h - q <= T between states of different
   units, taken cheapest first when both units are still free at that side, their openings agree with the ones already
   fixed and no cycle closes; the chains are then concatenated nearest-neighbour (cost from the fixed tail state). */
static int ufp[1000]; static int ufind(int x) { while (ufp[x] != x) x = ufp[x] = ufp[ufp[x]]; return x; }
static int greedy_order(int T, int *ord) {
    int off[1001]; off[0] = 0; for (int u = 0; u < NB; u++) off[u + 1] = off[u] + bu[u].n;
    int NS = off[NB]; int *su = malloc(4 * NS), *ss = malloc(4 * NS); u64 *SS = malloc(8 * NS), *EE = malloc(8 * NS);
    for (int u = 0; u < NB; u++) for (int c = 0; c < bu[u].n; c++) { su[off[u] + c] = u; ss[off[u] + c] = c; SS[off[u] + c] = bu[u].S[c]; EE[off[u] + c] = bu[u].E[c]; }
    int outU[1000], inU[1000], fixd[1000], outS[1000], inS[1000];
    for (int u = 0; u < NB; u++) { outU[u] = inU[u] = fixd[u] = -1; ufp[u] = u; }
    int hb = 1; while ((1 << hb) < 2 * NS) hb++;
    int hsz = 1 << hb; int *head = malloc(4 * hsz), *nxt = malloc(4 * NS);
    long acc = 0;
    for (int q = HH; q >= HH - T; q--) {
        u64 mask = (1ULL << (4 * q)) - 1;
        for (int i = 0; i < hsz; i++) head[i] = -1;
        for (int b = 0; b < NS; b++) { u64 k = SS[b] >> (4 * (HH - q)); int h_ = (int)((k * 0x9E3779B97F4A7C15ULL) >> (64 - hb)); nxt[b] = head[h_]; head[h_] = b; }
        for (int a = 0; a < NS; a++) {
            int ua = su[a]; if (outU[ua] >= 0 || (fixd[ua] >= 0 && fixd[ua] != ss[a])) continue;
            u64 k = EE[a] & mask; int h_ = (int)((k * 0x9E3779B97F4A7C15ULL) >> (64 - hb));
            for (int b = head[h_]; b >= 0; b = nxt[b]) {
                if ((SS[b] >> (4 * (HH - q))) != k) continue;
                int ub = su[b]; if (ub == ua || inU[ub] >= 0 || (fixd[ub] >= 0 && fixd[ub] != ss[b])) continue;
                if (ufind(ua) == ufind(ub)) continue;
                outU[ua] = ub; inU[ub] = ua; fixd[ua] = ss[a]; fixd[ub] = ss[b]; ufp[ufind(ua)] = ufind(ub); acc++;
                break;
            }
        }
    }
    (void)outS; (void)inS;
    /* chains; concatenate nearest neighbour */
    int used[1000] = {0}, n = 0, nch = 0; int cur = -1;
    for (;;) {
        int best = 1 << 30, bh = -1;
        for (int u = 0; u < NB; u++) {
            if (inU[u] >= 0 || used[u]) continue;
            if (cur < 0) { bh = u; break; }
            int c = 1 << 30; u64 e = bu[cur].E[fixd[cur] >= 0 ? fixd[cur] : 0];
            for (int t = 0; t < bu[u].n; t++) if (fixd[u] < 0 || fixd[u] == t) { int v = HH - ovl(e, bu[u].S[t]); if (v < c) c = v; }
            if (c < best) { best = c; bh = u; }
        }
        if (bh < 0) break;
        nch++;
        for (int u = bh; u >= 0; u = outU[u]) { ord[n++] = u; used[u] = 1; cur = u; }
    }
    if (n != NB) DIE("greedy: %d of %d units in chains", n, NB);
    fprintf(stderr, "greedy edge (T = %d): %ld edges taken, %d chains\n", T, acc, nch);
    free(su); free(ss); free(SS); free(EE); free(head); free(nxt);
    return n;
}
/* lower bound: every unit but the first is entered by a join; sum over units of the cheapest join into it (any
   state, from any state of another unit), minus the largest of them */
static void inbound(void) {
    int hist[16] = {0}; long sum = 0; int mx = 0;
    for (int u = 0; u < NB; u++) {
        int best = HH;
        for (int c = 0; c < bu[u].n && best > 0; c++)
            for (int v = 0; v < NB; v++) { if (v == u) continue;
                for (int a = 0; a < bu[v].n; a++) { int x = HH - ovl(bu[v].E[a], bu[u].S[c]); if (x < best) best = x; } }
        hist[best]++; sum += best; if (best > mx) mx = best;
    }
    fprintf(stderr, "lower bound (cheapest join into each unit): %ld; histogram:", sum - mx);
    for (int q = 0; q <= HH; q++) if (hist[q]) fprintf(stderr, " %d:%d", q, hist[q]);
    fprintf(stderr, "\n");
}
/* --dump FILE T: the state graph for blockilp.py: "U nunits", per unit "u kind ncands label", then edges "a b cost"
   (global state ids = unit offset + candidate) of cost <= T between states of different units */
static void dump_graph(const char *path, int T) {
    FILE *o = fopen(path, "w"); if (!o) DIE("cannot write %s", path);
    int off[1001]; off[0] = 0; for (int u = 0; u < NB; u++) off[u + 1] = off[u] + bu[u].n;
    int NS = off[NB]; fprintf(o, "U %d %d\n", NB, NS);
    for (int u = 0; u < NB; u++) { if (bu[u].k == 0) fprintf(o, "u %d %d D %d %d %d\n", u, bu[u].n, bu[u].g[0], bu[u].g[1], bu[u].g[2]); else fprintf(o, "u %d %d W %d\n", u, bu[u].n, bu[u].b); }
    int *su = malloc(4 * NS); u64 *SS = malloc(8 * NS), *EE = malloc(8 * NS);
    for (int u = 0; u < NB; u++) for (int c = 0; c < bu[u].n; c++) { su[off[u] + c] = u; SS[off[u] + c] = bu[u].S[c]; EE[off[u] + c] = bu[u].E[c]; }
    int hb = 1; while ((1 << hb) < 2 * NS) hb++;
    int hsz = 1 << hb; int *head = malloc(4 * hsz), *nxt = malloc(4 * NS); long ne = 0;
    char *done = calloc((size_t)NS, 1);
    for (int a = 0; a < NS; a++) {
        /* edges out of a, best cost per target unit only */
        (void)done;
    }
    static int bestc[1000]; static int bestb[1000];
    for (int q = HH; q >= HH - T; q--) {
        for (int i = 0; i < hsz; i++) head[i] = -1;
        for (int b = 0; b < NS; b++) { u64 k = SS[b] >> (4 * (HH - q)); int h_ = (int)((k * 0x9E3779B97F4A7C15ULL) >> (64 - hb)); nxt[b] = head[h_]; head[h_] = b; }
        u64 mask = (1ULL << (4 * q)) - 1;
        for (int a = 0; a < NS; a++) {
            u64 k = EE[a] & mask; int h_ = (int)((k * 0x9E3779B97F4A7C15ULL) >> (64 - hb));
            for (int b = head[h_]; b >= 0; b = nxt[b]) {
                if ((SS[b] >> (4 * (HH - q))) != k || su[b] == su[a]) continue;
                /* only the largest overlap of the pair (a, b): skip if a longer one exists */
                int ov = ovl(EE[a], SS[b]); if (ov != q) continue;
                fprintf(o, "%d %d %d\n", a, b, HH - q); ne++;
            }
        }
    }
    (void)bestc; (void)bestb;
    fclose(o); free(su); free(SS); free(EE); free(head); free(nxt); free(done);
    fprintf(stderr, "dump: %d units, %d states, %ld edges of cost <= %d\n", NB, NS, ne, T);
}
/* --start FILE: start order from an order file */
static int read_start(const char *path, int *ord) {
    FILE *f = fopen(path, "r"); if (!f) DIE("cannot open %s", path);
    char line[256]; int n = 0;
    while (fgets(line, sizeof line, f)) {
        int a, b, c, u = -1;
        if (sscanf(line, "D %d %d %d", &a, &b, &c) == 3) { for (int i = 0; i < NB; i++) if (bu[i].k == 0 && bu[i].g[0] == a && bu[i].g[1] == b && bu[i].g[2] == c) u = i; }
        else if (sscanf(line, "W %d", &a) == 1) { for (int i = 0; i < NB; i++) if (bu[i].k == 1 && bu[i].b == a) u = i; }
        else continue;
        if (u < 0) DIE("start: unknown unit %s", line);
        ord[n++] = u;
    }
    fclose(f);
    if (n != NB) DIE("start order has %d units, expected %d", n, NB);
    return n;
}
static void write_order(const char *path, const int *ord, int n, int cur, int cost0) {
    FILE *o = fopen(path, "w"); if (!o) DIE("cannot write %s", path);
    fprintf(o, "# blockord: segment order of the block (d = 0), cost %d (start %d), %d units\n", cur, cost0, n);
    for (int i = 0; i < n; i++) { const BU *u = &bu[ord[i]]; if (u->k == 0) fprintf(o, "D %d %d %d\n", u->g[0], u->g[1], u->g[2]); else fprintf(o, "W %d\n", u->b); }
    fclose(o);
}
int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: blockord SEL LOWERPLAN OUT.order [--run R] [--d D]\n"); return 2; }
    t0g = wall(); gs_new();
    int RUN = 4, D0 = 0, MAXSW = 1000, GT = -1, DT = 6; const char *DUMP = NULL, *START = NULL;
    for (int ai = 4; ai < argc; ai++) {
        if (!strcmp(argv[ai], "--run") && ai + 1 < argc) RUN = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--d") && ai + 1 < argc) D0 = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--sweeps") && ai + 1 < argc) MAXSW = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--greedy") && ai + 1 < argc) GT = atoi(argv[++ai]);
        else if (!strcmp(argv[ai], "--dump") && ai + 2 < argc) { DUMP = argv[++ai]; DT = atoi(argv[++ai]); }
        else if (!strcmp(argv[ai], "--start") && ai + 1 < argc) START = argv[++ai];
        else DIE("unknown option %s", argv[ai]);
    }
    L = 4; NN = 16; K = 14; HH = 13; SL = K; ZL = K + 1;
    read_sel(argv[1]); build_walks();
    if (!blockp) DIE("needs GENB_BLOCK");
    (void)D0;
    /* units of d = 0: the order of its trails in the lower plan, R only */
    FILE *f = fopen(argv[2], "r"); if (!f) DIE("cannot open %s", argv[2]);
    char line[512]; int ord[1000], n = 0;
    while (fgets(line, sizeof line, f)) {
        int d, g1, g2, j;
        if (line[0] != 'D' || sscanf(line, "D %d %d %d %d", &d, &g1, &g2, &j) != 4 || d != 0) continue;
        for (int i = 0; i < 12; i++) { int a = (j + i) % 12; if (!rowless[g1][g2][a]) continue; BU *u = &bu[NB]; u->k = 0; u->g[0] = g1; u->g[1] = g2; u->g[2] = a; ord[n++] = NB++; }
    }
    fclose(f);
    if (n != nrowless) DIE("lower plan gives %d small units of d = 0, expected %d", n, nrowless);
    int nW = 0;
    for (int k = 0; k < nbw; k++) { int v = bst0 + k; for (int a = 0; a < pre1[v + 1] - pre1[v]; a++) { BU *u = &bu[NB]; u->k = 1; u->w = pre1[v] + a; u->b = nW++; NB++; } }
    int maxc = 0;
    for (int i = 0; i < NB; i++) { bu_cands(&bu[i]); if (bu[i].n > maxc) maxc = bu[i].n; }
    for (int i = 0; i < NB; i++) { F[i] = malloc(4 * maxc); G[i] = malloc(4 * maxc); }
    fprintf(stderr, "segment of d = 0: %d small units, %d walk units, max candidates %d (%.1fs)\n", n, nW, maxc, wall() - t0g);
    fprintf(stderr, "small units alone in the lower order: cost %d\n", seqcost(ord, n));
    /* insert the walk units greedily */
    for (int i = n; i < NB; i++) {
        seqcost(ord, n); backdp(ord, n);
        int best = 1 << 30, bk = 0, r = i;
        for (int k = 0; k <= n; k++) { int c = ins_cost(ord, n, &r, 1, k); if (c < best) { best = c; bk = k; } }
        memmove(ord + bk + 1, ord + bk, sizeof(int) * (n - bk)); ord[bk] = i; n++;
    }
    int cost0 = seqcost(ord, n);
    fprintf(stderr, "start order (walk units inserted greedily): cost %d (%.1fs)\n", cost0, wall() - t0g);
    if (getenv("BLOCKORD_BOUND")) inbound();
    if (DUMP) { dump_graph(DUMP, DT); return 0; }
    if (START) { int os[1000]; int ns_ = read_start(START, os); int cs = seqcost(os, ns_); fprintf(stderr, "start file %s: cost %d\n", START, cs); memcpy(ord, os, sizeof(int) * ns_); cost0 = cs; }
    if (GT >= 0) {
        int og[1000]; int ng = greedy_order(GT, og); int cg = seqcost(og, ng);
        fprintf(stderr, "greedy edge order: cost %d (%.1fs)\n", cg, wall() - t0g);
        if (cg < cost0) { memcpy(ord, og, sizeof(int) * ng); cost0 = cg; }
    }
    /* relocation of runs */
    int cur = cost0, improved = 1, sweeps = 0;
    while (improved && sweeps < MAXSW) {
        improved = 0; sweeps++;
        for (int m = 1; m <= RUN; m++) for (int i = 0; i + m <= n; i++) {
            int run[64], rest[1000], nr = 0; memcpy(run, ord + i, sizeof(int) * m);
            for (int t = 0; t < n; t++) if (t < i || t >= i + m) rest[nr++] = ord[t];
            seqcost(rest, nr); backdp(rest, nr);
            int best = cur, bk = -1;
            for (int k = 0; k <= nr; k++) { if (k == i) continue; int c = ins_cost(rest, nr, run, m, k); if (c < best) { best = c; bk = k; } }
            if (bk >= 0) {
                memcpy(ord, rest, sizeof(int) * bk); memcpy(ord + bk, run, sizeof(int) * m); memcpy(ord + bk + m, rest + bk, sizeof(int) * (nr - bk));
                int chk = seqcost(ord, n); if (chk != best) DIE("insertion cost %d, recomputed %d", best, chk);
                cur = best; improved = 1;
            }
        }
        fprintf(stderr, "sweep %d: cost %d (%.1fs)\n", sweeps, cur, wall() - t0g);
        write_order(argv[3], ord, n, cur, cost0);
    }
    write_order(argv[3], ord, n, cur, cost0);
    printf("{\"mode\":\"blockord\",\"units\":%d,\"start_cost\":%d,\"cost\":%d,\"sweeps\":%d,\"seconds\":%.0f}\n", n, cost0, cur, sweeps, wall() - t0g);
    return 0;
}
