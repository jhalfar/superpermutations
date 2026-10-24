/* jt.c (agent n7-j15, 2026-10-09) - joint statements about several pieces for defect 15 on 7 symbols.
 *
 * Geometry as in pproto.c (a file of mine, not in this repository) (written from the definitions): symbols 0..K-1, sigma, tau2, ew,
 * blocks, rows (entry, length), links of weight 3 and 4 between rows of different classes.
 *
 * STATEMENT  J(pieces; V, W; B):
 *   there are no pieces p_1..p_n, p_i a sequence with at most s_i links of weight 4 (spec "S<s>") or a ring (spec "R"),
 *   such that  sum val >= V,  sum wt <= W,  and  sum over classes (number of pieces containing it - 1)^+ <= B,
 *   where a piece has pairwise different classes, L = K-1,
 *     sequence: val = rows - holes - (L-1) links,  wt = holes + L links;      ring: val = rows - holes, wt = holes.
 *
 * SEARCH (why "no object found" proves the statement): take a counterexample with the fewest rows in all.
 *   - Renaming symbols: piece 1 starts at the identity word; if it is a ring, in the rotation of the cycle lemma.
 *   - Every sequence piece S of it is a strict record: val(A) < val(S) for every proper prefix A (else replace S by A:
 *     fewer rows, not less value, not more weight, not more shared classes).
 *   - For every cut S = A + B of a sequence piece: val(A) >= 1 if the cut link has weight 3, val(A) - (L-1) >= 1 if it
 *     has weight 4 (else replace S by B).
 *   - Table bound: the rest B is a sequence with t'' links and e holes, so rows(B) <= P_t''(e); the pieces after it
 *     are single objects, so their total value within weight b is at most Best_{i+1}(b) (knapsack over the single
 *     tables).  A prefix is extended only if these bounds allow the total V within W.
 *   - Ring piece, prefix of r rows and d holes: kept iff a target (T, H) exists with H <= weight left, T <= PR(H),
 *     T - H + Best_{i+1}(left - H) >= value needed, r < T, d <= H, d T <= r H (cycle lemma), T - r <= M(H - d).
 *   - Pieces after the first start at every entry (every vertex); a class used by an earlier piece may be entered
 *     while fewer than B classes are shared.
 * Output of "run": FOUND objects (counterexamples, printed) and the counts.  "est": Chen's stratified sampling of
 * the same tree (ESTIMATE of kept prefixes and of rows tried; proves nothing).
 *
 * ADDED in jr.c (agent n7-jrev, PROOF.md): env RMODE=1 potential along the whole concatenation (Lemma JREV),
 *   RMODE=2 potential of piece 1 alone (Lemma PREV); REV=1 the cut is applied (REV=0: objects are only classified by
 *   the sign of delta = dip + peak - final); PA PB PH the potential; ORD=1 the order rule for neighbouring pieces of
 *   the same kind (value not increasing; two pieces: the first has at least half of V); JCAP=file joint tables
 *   (lines "G<i>: v(0) v(1) .." = most value of (non-empty rest of sequence i) + later pieces within weight b,
 *   "J<i>: .." = most value of the pieces i.. within weight b; piece index from 0); STOP1=1 stop at the first object.
 * usage: jt K capsfile run|est V W B piece... [REPS seed]      env: PART NPARTS DEPTH (gate in piece 1), NOCUT=1
 *   capsfile: lines "s: P_s(0) P_s(1) ..." and "R: PR(0) PR(1) ..."; missing entries count as no bound.
 *   NOCUT=1 switches off the table bounds, the record rule and the suffix rule (for tests).
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXP 5040
#define MAXC 720
#define INF 1000000
static int K, NP, NC, L, c5, c6;
static int8_t PERM[MAXP][8];
static int *RK;
static int16_t SIG[MAXP], SIGI[MAXP], T2[MAXP], CLS[MAXP];
static int16_t succ3[MAXP][8], succ4[MAXP][32];
static int nsucc3[MAXP], nsucc4[MAXP];

static int code(const int8_t *w) { int c = 0; for (int i = 0; i < K; i++) c = c * K + w[i]; return c; }
static int ewf(int u, int v) {
    for (int t = 1; t < K; t++) { int ok = 1; for (int i = 0; i + t < K; i++) if (PERM[u][i + t] != PERM[v][i]) { ok = 0; break; } if (ok) return t; }
    return K;
}
static void build(void) {
    NP = 1; for (int i = 2; i <= K; i++) NP *= i;
    L = K - 1; c5 = L - 1; c6 = L;
    int pw = 1; for (int i = 0; i < K; i++) pw *= K;
    RK = (int *)malloc(sizeof(int) * pw); for (int i = 0; i < pw; i++) RK[i] = -1;
    int8_t w[8]; for (int i = 0; i < K; i++) w[i] = (int8_t)i;
    int cnt = 0;
    for (;;) {
        memcpy(PERM[cnt], w, K); RK[code(w)] = cnt; cnt++;
        int i = K - 2; while (i >= 0 && w[i] > w[i + 1]) i--;
        if (i < 0) break;
        int j = K - 1; while (w[j] < w[i]) j--;
        int8_t t = w[i]; w[i] = w[j]; w[j] = t;
        for (int a = i + 1, b = K - 1; a < b; a++, b--) { t = w[a]; w[a] = w[b]; w[b] = t; }
    }
    for (int p = 0; p < NP; p++) {
        int8_t v[8];
        for (int i = 0; i < K - 1; i++) v[i] = PERM[p][i + 1]; v[K - 1] = PERM[p][0];
        SIG[p] = (int16_t)RK[code(v)];
        for (int i = 0; i < K - 2; i++) v[i] = PERM[p][i + 1]; v[K - 2] = PERM[p][0]; v[K - 1] = PERM[p][K - 1];
        T2[p] = (int16_t)RK[code(v)];
    }
    for (int p = 0; p < NP; p++) SIGI[SIG[p]] = (int16_t)p;
    for (int p = 0; p < NP; p++) CLS[p] = -1;
    NC = 0;
    for (int p = 0; p < NP; p++) if (CLS[p] < 0) { int x = p; do { CLS[x] = (int16_t)NC; x = SIG[x]; } while (x != p); NC++; }
    for (int q = 0; q < NP; q++) {
        int u = SIGI[q]; nsucc3[q] = nsucc4[q] = 0;
        for (int v = 0; v < NP; v++) {
            if (CLS[v] == CLS[q]) continue;
            int e = ewf(u, v);
            if (e == 3) succ3[q][nsucc3[q]++] = (int16_t)v;
            if (e == 4) succ4[q][nsucc4[q]++] = (int16_t)v;
        }
    }
}
static inline int link3(int q, int v) { for (int i = 0; i < nsucc3[q]; i++) if (succ3[q][i] == v) return 1; return 0; }

/* ---------- tables ---------- */
#define SM 10
#define WM 128
#define RM 200
#define MAXPC 4
static int P[SM][WM], PRt[WM];
static int V, W, B, npc, ptype[MAXPC], pS[MAXPC], NOCUT = 0;
static int RLO = 0, RHI = WM;      /* env RLO, RHI: only rings with RLO <= holes <= RHI (the statement restricted to such rings) */
static int REV = 0, RMODE = 1, PA = 10, PB = 15, PH = 30, XL, ORD = 0, STOP1 = 0, HALFV = -INF, RP = 0;
static int samekind[MAXPC], pval[MAXPC], basef[MAXPC + 1], d1;
static long long npos, nzero, nneg;
static int SEGt[SM][WM + 1], G1[SM][WM + 1], PKt[MAXPC][SM][WM + 1], Dt[MAXPC + 1][WM + 1];
#define NOFF 160
#define NN 420
static int *CN1t, *A2Pt;
static int Best[MAXPC + 1][WM + 1];          /* Best[i][b]: most value of the pieces i.. within weight b */
static int G[MAXPC][SM][WM + 1];             /* G[i][t'][b']: most value of (rest of sequence i with <= t' links) + later pieces */
static void readcaps(const char *fn) {
    for (int s = 0; s < SM; s++) for (int i = 0; i < WM; i++) P[s][i] = INF;
    for (int i = 0; i < WM; i++) PRt[i] = INF;
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no caps file %s\n", fn); exit(1); }
    char *line = (char *)malloc(1 << 16);
    while (fgets(line, 1 << 16, f)) {
        char *p = strchr(line, ':'); if (!p || line[0] == '#') continue;
        int *row; int i = 0;
        if (line[0] == 'R') row = PRt; else { int t = atoi(line); if (t < 0 || t >= SM) continue; row = P[t]; }
        p++;
        char *tok = strtok(p, " \t\r\n");
        while (tok && i < WM) { row[i++] = atoi(tok); tok = strtok(NULL, " \t\r\n"); }
    }
    fclose(f);
    for (int i = 0; i < WM; i++) if (PRt[i] > P[0][i]) PRt[i] = P[0][i];      /* a ring is a chain */
}
static int cl(long long v) { return v > INF ? INF : (v < -INF ? -INF : (int)v); }
static void mktables(void) {
    for (int b = 0; b <= WM; b++) Best[npc][b] = 0;
    for (int i = npc - 1; i >= 0; i--) {
        for (int b = 0; b <= WM; b++) {
            long long best = -INF;
            for (int w = 0; w <= b && w < WM; w++) {
                long long v = -INF;
                if (ptype[i] == 1) v = (w < RLO || w > RHI) ? -INF : ((NOCUT || PRt[w] >= INF) ? INF : PRt[w] - w);
                else for (int t = 0; t <= pS[i] && c6 * t <= w; t++) { int x = w - c6 * t; long long u = NOCUT ? INF : (P[t][x] >= INF ? INF : P[t][x] - x - c5 * t); if (u > v) v = u; }
                if (v > -INF && Best[i + 1][b - w] > -INF && v + Best[i + 1][b - w] > best) best = v + Best[i + 1][b - w];
            }
            Best[i][b] = cl(best);
        }
        if (ptype[i] == 0) for (int tp = 0; tp <= pS[i]; tp++) for (int b = 0; b <= WM; b++) {
            long long best = -INF;
            for (int t = 0; t <= tp; t++) for (int e = 0; e + c6 * t <= b && e < WM; e++) {
                long long u = NOCUT ? INF : (P[t][e] >= INF ? INF : P[t][e] - e - c5 * t);
                int rest = Best[i + 1][b - e - c6 * t];
                if (rest > -INF && u + rest > best) best = u + rest;
            }
            G[i][tp][b] = cl(best);
        }
    }
}
/* ---------- reversal cut: tables (PROOF.md section 3) ---------- */
static inline int CN1(int need, int om) { int n = need + NOFF; if (n < 0) return -INF; if (n >= NN) return INF; return CN1t[n * (WM + 1) + om]; }
static inline int A2P(int tl, int need, int om) { int n = need + NOFF; if (n < 0) return -INF; if (n >= NN) return INF; return A2Pt[(tl * NN + n) * (WM + 1) + om]; }
static void readjcap(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no joint caps file %s\n", fn); exit(1); }
    char *line = (char *)malloc(1 << 16);
    while (fgets(line, 1 << 16, f)) {
        char k = line[0]; if (k != 'G' && k != 'J') continue;
        int i = atoi(line + 1); char *p = strchr(line, ':'); if (!p || i < 0 || i >= MAXPC) continue;
        int b = 0; char *tok = strtok(p + 1, " \t\r\n");
        while (tok && b <= WM) { int v = atoi(tok);
            if (k == 'J') { if (v < Best[i][b]) Best[i][b] = v; } else for (int tp = 0; tp < SM; tp++) if (v < G[i][tp][b]) G[i][tp][b] = v;
            b++; tok = strtok(NULL, " \t\r\n"); }
    }
    fclose(f);
}
static void mkrev(void) {
    XL = c6 * (PB - PA) + c5 * PA - 2 * PH;
    if (PB < PA || XL < 0 || PA <= 0 || PH < 0) { fprintf(stderr, "potential not admissible (need PB >= PA > 0, PH >= 0, c6(PB-PA)+c5 PA-2PH >= 0)\n"); exit(2); }
    for (int tl = 0; tl < SM; tl++) for (int w = 0; w <= WM; w++) {
        long long best = -INF, best1 = -INF;
        for (int u = 0; u <= tl; u++) for (int e = 0; e + c6 * u <= w && e < WM; e++) {
            int inf = NOCUT || P[u][e] >= INF;
            long long v = inf ? INF : (long long)PA * P[u][e] - PB * e - 2 * PH * u, v1 = inf ? INF : P[u][e] - e - c5 * u;
            if (v > best) best = v; if (v1 > best1) best1 = v1;
        }
        SEGt[tl][w] = cl(best); G1[tl][w] = cl(best1);
    }
    for (int w = 0; w <= WM; w++) Dt[npc][w] = -INF;
    for (int i = npc - 1; i >= 0; i--) {
        for (int tl = 0; tl < SM; tl++) for (int w = 0; w <= WM; w++) {
            long long best = -INF;
            for (int w1 = 0; w1 <= w; w1++) { if (SEGt[tl][w1] <= -INF) continue; long long nx = RMODE == 2 ? 0 : Dt[i + 1][w - w1]; if (nx < 0) nx = 0; if (SEGt[tl][w1] + nx > best) best = SEGt[tl][w1] + nx; }
            PKt[i][tl][w] = cl(best);
        }
        for (int w = 0; w <= WM; w++) {
            if (ptype[i] == 0) { Dt[i][w] = PKt[i][pS[i]][w]; continue; }
            long long best = -INF;
            for (int H = 0; H <= w && H < WM; H++) { if (H < RLO || H > RHI) continue;
                long long v = (NOCUT || PRt[H] >= INF) ? INF : (long long)PA * PRt[H] - PB * H, nx = Dt[i + 1][w - H]; if (nx < 0) nx = 0; if (v + nx > best) best = v + nx; }
            Dt[i][w] = cl(best);
        }
    }
    CN1t = (int *)malloc(sizeof(int) * NN * (WM + 1)); A2Pt = (int *)malloc(sizeof(int) * SM * NN * (WM + 1));
    for (int n = 0; n < NN; n++) for (int om = 0; om <= WM; om++) {
        int need = n - NOFF; long long c = INF;
        for (int wr = 0; wr <= om; wr++) { int bb = Best[RP + 1][om - wr]; if (bb <= -INF) continue; long long v = bb >= INF ? -INF : (long long)PA * (need - bb) - (PB - PA) * wr; if (v < c) c = v; }
        CN1t[n * (WM + 1) + om] = cl(c);
        for (int tl = 0; tl < SM; tl++) { long long c2 = INF;
            for (int wr = 0; wr <= om; wr++) { int bb = Best[RP + 1][om - wr]; if (bb <= -INF || SEGt[tl][wr] <= -INF) continue;
                long long v = (bb >= INF || SEGt[tl][wr] >= INF) ? -INF : (long long)PA * (need - bb) - (PB - PA) * wr - SEGt[tl][wr]; if (v < c2) c2 = v; }
            A2Pt[(tl * NN + n) * (WM + 1) + om] = cl(c2); }
    }
}
/* may the prefix be continued by a link of weight 3 / by a heavy link?  need = value still needed, om = weight left,
   tl = heavy links left in the piece, f = potential without the term of the next link, (pm, pM) = dip and peak before */
static inline int rev_light(int i, int need, int om, int tl, int f, int pm, int pM) {
    int m = pm < f ? pm : f, M = pM > f ? pM : f;
    if (m >= 0) return 1;
    if (RMODE == 1) { int cn = PA * need - (PB - PA) * om; return M + m - f >= cn || m + PKt[i][tl][om] >= cn; }
    if (i != RP) return 1;
    return M + m - f >= CN1(need, om) || m >= A2P(tl, need, om);
}
static inline int rev_heavy(int i, int need, int om, int tl, int f, int pm, int pM) {      /* tl >= 1, om >= c6 */
    int fh = f - PH, m = pm < fh ? pm : fh, M = pM > fh ? pM : fh;
    if (m >= 0) return 1;
    if (RMODE == 1) { int cn = PA * need - (PB - PA) * om + XL; return M + m - f >= cn || m - 2 * PH + PKt[i][tl - 1][om - c6] >= cn; }
    if (i != RP) return 1;
    return M + m - f >= CN1(need + c5, om - c6) - 2 * PH || m >= A2P(tl - 1, need + c5, om - c6);
}
static inline int rev_jump(int i, int need, int om, int f, int mJ, int MJ) {       /* global mode: the jump after piece i */
    if (mJ >= 0) return 1;
    int cn = PA * need - (PB - PA) * om; return MJ + mJ - f >= cn || mJ + Dt[i + 1][om] >= cn;
}
static inline void classify(int dl) { if (dl > 0) npos++; else if (dl < 0) nneg++; else nzero++; }

/* ring keep tables, by (piece, value needed a, weight left b) */
static uint8_t *keepcache[MAXPC][WM + 1][WM + 1];
static uint8_t *getkeep(int i, int a, int b) {
    if (a < 0) a = 0;
    if (a > WM) a = WM;
    uint8_t *k = keepcache[i][a][b];
    if (k) return k;
    k = (uint8_t *)calloc(RM * WM, 1);
    for (int H = 0; H <= b && H < WM; H++) {
        if (Best[i + 1][b - H] <= -INF || H < RLO || H > RHI) continue;
        int Tlo = NOCUT ? 2 : H + a - Best[i + 1][b - H]; if (Tlo < 2) Tlo = 2;
        int Thi = NOCUT ? RM - 1 : PRt[H]; if (Thi > RM - 1) Thi = RM - 1;
        if (Tlo > Thi) continue;
        for (int d = 0; d <= H; d++) for (int r = 1; r < Thi; r++) {
            if (k[r * WM + d]) continue;
            int lo = Tlo > r + 1 ? Tlo : r + 1, hi = Thi;
            if (!NOCUT) {
                if (P[0][H - d] < INF && r + P[0][H - d] < hi) hi = r + P[0][H - d];
                if (d > 0 && (r * H) / d < hi) hi = (r * H) / d;
            }
            if (lo <= hi) k[r * WM + d] = 1;
        }
    }
    keepcache[i][a][b] = k;
    return k;
}

/* ---------- exhaustive search ---------- */
static uint64_t rng_s = 88172645463325252ULL;
static inline uint64_t rng(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s; }
static uint8_t U[MAXC], C[MAXC];
static int dups;
static long long kept[MAXPC], tries[MAXPC], jumps[MAXPC], found, comp[MAXPC];
static int PARTI = 0, NPARTS = 1, DEPTH = 0; static long long fcount = 0;
/* nodes above the gate are visited by every part; they are counted in part 0 only, so the sums over the parts are the counts of the whole tree */
static int P2 = 0, NP2 = 1;    /* env PART2, NPARTS2: second gate, on the start vertex of piece 2 (v mod NPARTS2 = PART2) */
#define CNT(i, r) ((i) > 0 || (((r) >= DEPTH || NPARTS == 1 || PARTI == 0) && P2 == 0))
#define JMP(i, r) ((i) > 0 || (r) >= DEPTH || NPARTS == 1 || PARTI == 0)
static int stk_e[1024], stk_l[1024], stk_p[1024], stk_k[1024], sp;      /* rows of the current object: entry, length, piece, link kind */
static void print_object(void) {
    printf("FOUND:");
    for (int i = 0; i < sp; i++) {
        if (i == 0 || stk_p[i] != stk_p[i - 1]) printf(" | %c", ptype[stk_p[i]] ? 'R' : 'S');
        else if (stk_k[i] == 4) printf(" /");
        printf(" "); for (int j = 0; j < K; j++) printf("%d", PERM[stk_e[i]][j]); printf(":%d", stk_l[i]);
    }
    printf("\n"); fflush(stdout);
}
static void jump(int i, int a, int b, int pm, int pM);
static void seq_node(int i, int a, int b, int q, int r, int d, int t, int recmax, int pm, int pM);
static void ring_node(int i, int a, int b, const uint8_t *kr, int st0, int q, int r, int d, int pm, int pM);
static void finish(void);
static void rows(int i, int a, int b, const uint8_t *kr, int st0, int st, int r, int d, int t, int recmax, int kind, int pm, int pM) {
    int ent[8], isd[8], len = 0, x = st;
    if (CNT(i, r)) tries[i]++;
    while (len < L) {
        int c = CLS[x];
        if (C[c]) break;
        if (U[c]) { if (dups >= B) break; isd[len] = 1; dups++; } else { isd[len] = 0; U[c] = 1; }
        C[c] = 1; ent[len++] = x; x = T2[x];
    }
    for (int l = len; l >= 1; l--) {
        int dd = d + (L - l);
        if (dd + c6 * t <= b) {
            stk_e[sp] = st; stk_l[sp] = l; stk_p[sp] = i; stk_k[sp] = kind; sp++;
            if (ptype[i]) ring_node(i, a, b, kr, st0, ent[l - 1], r + 1, dd, pm, pM);
            else seq_node(i, a, b, ent[l - 1], r + 1, dd, t, recmax, pm, pM);
            sp--;
        }
        int c = CLS[ent[l - 1]]; C[c] = 0; if (isd[l - 1]) dups--; else U[c] = 0;
    }
}
static void seq_node(int i, int a, int b, int q, int r, int d, int t, int recmax, int pm, int pM) {
    int val = r - d - c5 * t, wt = d + c6 * t;
    if (i == 0 && r == DEPTH && NPARTS > 1 && (fcount++ % NPARTS) != PARTI) return;
    int f = basef[i] + PA * r - PB * d - 2 * PH * t;
    if ((val > recmax || NOCUT) && JMP(i, r)) {
        int mJ = pm < f ? pm : f, MJ = pM > f ? pM : f;
        int ordok = !(ORD && samekind[i]) || val <= pval[i - 1];
        if (i == 0 && val < HALFV) ordok = 0;
        if (ORD && i < npc - 1 && samekind[i + 1] && Best[i + 2][b - wt] < INF && 2 * val + Best[i + 2][b - wt] < a) ordok = 0;
        if (i == npc - 1) {
            if (val >= a && ordok) { int dl = (RMODE == 2 && i != RP) ? d1 : mJ + MJ - f; classify(dl); if (!REV || dl >= 0) { found++; if (found <= 10) print_object(); if (STOP1) finish(); } }
        } else if (ordok && Best[i + 1][b - wt] > -INF && val + Best[i + 1][b - wt] >= a) {
            int ok = 1;
            if (RMODE == 2 && i == RP) { d1 = mJ + MJ - f; if (REV && d1 < 0) ok = 0; }
            if (RMODE == 1 && REV && !rev_jump(i, a - val, b - wt, f, mJ, MJ)) ok = 0;
            if (ok) { if (i > 0 || P2 == 0) comp[i]++; pval[i] = val; basef[i + 1] = f; jump(i + 1, a - val, b - wt, mJ, MJ); }
        }
    }
    if (val > recmax) recmax = val;
    if (r >= RM - 1) return;
    int k3 = (NOCUT || val >= 1) && G[i][pS[i] - t][b - wt] > -INF && val + G[i][pS[i] - t][b - wt] >= a;
    int k4 = t < pS[i] && (NOCUT || val - c5 >= 1) && b - wt - c6 >= 0 && G[i][pS[i] - t - 1][b - wt - c6] > -INF && val - c5 + G[i][pS[i] - t - 1][b - wt - c6] >= a;
    if (i == 0 && HALFV > -INF) { if (k3 && val + G1[pS[i] - t][b - wt] < HALFV) k3 = 0; if (k4 && val - c5 + G1[pS[i] - t - 1][b - wt - c6] < HALFV) k4 = 0; }
    if (REV) { if (k3) k3 = rev_light(i, a - val, b - wt, pS[i] - t, f, pm, pM); if (k4) k4 = rev_heavy(i, a - val, b - wt, pS[i] - t, f, pm, pM); }
    if ((k3 || k4) && CNT(i, r)) kept[i]++;
    if (k3) { int m3 = pm < f ? pm : f, M3 = pM > f ? pM : f; for (int j = 0; j < nsucc3[q]; j++) rows(i, a, b, NULL, 0, succ3[q][j], r, d, t, recmax, 3, m3, M3); }
    if (k4) { int fh = f - PH, m4 = pm < fh ? pm : fh, M4 = pM > fh ? pM : fh; for (int j = 0; j < nsucc4[q]; j++) rows(i, a, b, NULL, 0, succ4[q][j], r, d, t + 1, recmax, 4, m4, M4); }
}
static void ring_node(int i, int a, int b, const uint8_t *kr, int st0, int q, int r, int d, int pm, int pM) {
    if (i == 0 && r == DEPTH && NPARTS > 1 && (fcount++ % NPARTS) != PARTI) return;
    if (r >= 2 && link3(q, st0) && d >= RLO && d <= RHI && JMP(i, r)) {
        int val = r - d, f = basef[i] + PA * r - PB * d;
        int mJ = pm < f ? pm : f, MJ = pM > f ? pM : f;
        int ordok = !(ORD && samekind[i]) || val <= pval[i - 1];
        if (i == npc - 1) {
            if (val >= a && ordok) { int dl = RMODE == 2 ? (i > RP ? d1 : 0) : mJ + MJ - f; classify(dl); if (!REV || dl >= 0) { found++; if (found <= 10) print_object(); if (STOP1) finish(); } }
        } else if (ordok && Best[i + 1][b - d] > -INF && val + Best[i + 1][b - d] >= a) {
            int ok = 1;
            if (RMODE == 2 && i == RP) d1 = 0;
            if (RMODE == 1 && REV && !rev_jump(i, a - val, b - d, f, mJ, MJ)) ok = 0;
            if (ok) { if (i > 0 || P2 == 0) comp[i]++; pval[i] = val; basef[i + 1] = f; jump(i + 1, a - val, b - d, mJ, MJ); }
        }
    }
    if (r < RM && kr[r * WM + d]) { if (CNT(i, r)) kept[i]++; for (int j = 0; j < nsucc3[q]; j++) rows(i, a, b, kr, st0, succ3[q][j], r, d, 0, 0, 3, pm, pM); }
}
static double HYB = 0; static long long hyb_n; static int HREP = 1;   /* env HREP: replications per sampled piece */
static void est_piece(int i, int a, int b, const uint64_t *U0, int dups0, double w0, int base, int pm0, int pM0, int pv);
static void jump(int i, int a, int b, int pm, int pM) {
    if (HYB > 0 && i == 1) {
        jumps[i]++;
        if ((rng() >> 11) * (1.0 / 9007199254740992.0) < HYB) { uint64_t u[12]; memset(u, 0, sizeof u); for (int c = 0; c < NC; c++) if (U[c]) u[c >> 6] |= 1ULL << (c & 63); hyb_n++; for (int h = 0; h < HREP; h++) est_piece(1, a, b, u, dups, 1.0 / HYB / HREP, RMODE == 2 ? 0 : basef[1], RMODE == 2 ? 0 : pm, RMODE == 2 ? 0 : pM, pval[0]); }
        return;
    }
    if (RMODE == 2) { pm = pM = 0; basef[i] = 0; }
    uint8_t save[MAXC]; memcpy(save, C, NC); memset(C, 0, NC);
    if (i > 1 || P2 == 0) jumps[i]++;
    const uint8_t *kr = ptype[i] ? getkeep(i, a, b) : NULL;
    for (int v = 0; v < NP; v++) { if (i == 1 && NP2 > 1 && v % NP2 != P2) continue; rows(i, a, b, kr, v, v, 0, 0, 0, -INF, 0, pm, pM); }
    memcpy(C, save, NC);
}

/* ---------- estimator (Chen) ---------- */
typedef struct { uint64_t U[12], C[12]; double w; int pm, pM; int16_t q, st0, recmax; uint8_t r, d, t, dups, set; } St;
static inline int isb(const uint64_t *u, int c) { return (u[c >> 6] >> (c & 63)) & 1; }
static inline void setb(uint64_t *u, int c) { u[c >> 6] |= 1ULL << (c & 63); }
static inline double rnd(void) { return (rng() >> 11) * (1.0 / 9007199254740992.0); }
#define NSTR (SM * WM * 7 * 4)
static St *lev[MAXPC][2];
static int *list[MAXPC][2], nlist[MAXPC][2];
static double e_kept[MAXPC], e_tries[MAXPC], e_jumps[MAXPC], e_comp[MAXPC], e_found;
static double JP = 1.0;
static void offer(int i, int a, const uint64_t *u, const uint64_t *c, int q, int st0, int r, int d, int t, int len, int heavy, int recmax, int dp, double w, int pm, int pM) {
    int val = r - d - c5 * t;
    int idx = (((t * WM + d) * 7 + len) * 2 + heavy) * 2 + (val > recmax);
    St *s = &lev[i][a][idx];
    if (!s->set) { s->set = 1; s->w = 0; list[i][a][nlist[i][a]++] = idx; }
    s->w += w;
    if (rnd() * s->w < w) { memcpy(s->U, u, sizeof s->U); memcpy(s->C, c, sizeof s->C); s->q = (int16_t)q; s->st0 = (int16_t)st0; s->recmax = (int16_t)recmax; s->r = (uint8_t)r; s->d = (uint8_t)d; s->t = (uint8_t)t; s->dups = (uint8_t)dp; s->pm = pm; s->pM = pM; }
}
static void expand(int i, int a, int b, const St *s, int st, int st0, int heavy, int recmax, int pm, int pM) {
    uint64_t u[12], c[12]; memcpy(u, s->U, sizeof u); memcpy(c, s->C, sizeof c);
    int x = st, dp = s->dups, t = s->t + heavy;
    e_tries[i] += s->w;
    for (int l = 1; l <= L; l++) {
        int cc = CLS[x];
        if (isb(c, cc)) break;
        if (isb(u, cc)) { if (dp >= B) break; dp++; } else setb(u, cc);
        setb(c, cc);
        int dd = s->d + (L - l);
        if (dd + c6 * t <= b) offer(i, a, u, c, x, st0, s->r + 1, dd, t, l, heavy, recmax, dp, s->w, pm, pM);
        x = T2[x];
    }
}
static void est_piece(int i, int a, int b, const uint64_t *U0, int dups0, double w0, int base, int pm0, int pM0, int pv) {
    static St root;
    const uint8_t *kr = ptype[i] ? getkeep(i, a, b) : NULL;
    St rt; memcpy(rt.U, U0, sizeof rt.U); memset(rt.C, 0, sizeof rt.C); rt.w = w0; rt.r = 0; rt.d = 0; rt.t = 0; rt.dups = (uint8_t)dups0; (void)root;
    nlist[i][0] = nlist[i][1] = 0;
    if (i == 0) expand(i, 1, b, &rt, 0, 0, 0, -INF, pm0, pM0);
    else for (int v = 0; v < NP; v++) expand(i, 1, b, &rt, v, v, 0, -INF, pm0, pM0);
    for (int r = 1; r < RM - 1; r++) {
        int cur = r & 1, nxt = cur ^ 1;
        if (!nlist[i][cur]) break;
        for (int n = 0; n < nlist[i][cur]; n++) {
            St *s = &lev[i][cur][list[i][cur][n]];
            int d = s->d, t = s->t, q = s->q;
            int pm = s->pm, pM = s->pM;
            if (ptype[i]) {
                if (r >= 2 && link3(q, s->st0) && d >= RLO && d <= RHI) {
                    int val = r - d, f = base + PA * r - PB * d, mJ = pm < f ? pm : f, MJ = pM > f ? pM : f;
                    int ordok = !(ORD && samekind[i]) || val <= pv;
                    if (i == npc - 1) { if (val >= a && ordok && (!REV || RMODE == 2 || mJ + MJ - f >= 0)) e_found += s->w; }
                    else if (ordok && Best[i + 1][b - d] > -INF && val + Best[i + 1][b - d] >= a && !(RMODE == 1 && REV && !rev_jump(i, a - val, b - d, f, mJ, MJ))) {
                        e_comp[i] += s->w;
                        if (JP >= 1.0 || rnd() < JP) est_piece(i + 1, a - val, b - d, s->U, s->dups, s->w / JP, RMODE == 2 ? 0 : f, RMODE == 2 ? 0 : mJ, RMODE == 2 ? 0 : MJ, val);
                    }
                }
                if (kr[r * WM + d]) { e_kept[i] += s->w; for (int j = 0; j < nsucc3[q]; j++) expand(i, nxt, b, s, succ3[q][j], s->st0, 0, 0, pm, pM); }
            } else {
                int val = r - d - c5 * t, wt = d + c6 * t, recmax = s->recmax, f = base + PA * r - PB * d - 2 * PH * t;
                if (val > recmax || NOCUT) {
                    int mJ = pm < f ? pm : f, MJ = pM > f ? pM : f;
                    int ordok = !(ORD && samekind[i]) || val <= pv;
                    if (i == 0 && val < HALFV) ordok = 0;
                    if (ORD && i < npc - 1 && samekind[i + 1] && Best[i + 2][b - wt] < INF && 2 * val + Best[i + 2][b - wt] < a) ordok = 0;
                    if (i == npc - 1) { if (val >= a && ordok && (!REV || (RMODE == 2 && i != RP) || mJ + MJ - f >= 0)) e_found += s->w; }
                    else if (ordok && Best[i + 1][b - wt] > -INF && val + Best[i + 1][b - wt] >= a) {
                        int ok = 1;
                        if (RMODE == 2 && i == RP && REV && mJ + MJ - f < 0) ok = 0;
                        if (RMODE == 1 && REV && !rev_jump(i, a - val, b - wt, f, mJ, MJ)) ok = 0;
                        if (ok) { e_comp[i] += s->w; if (JP >= 1.0 || rnd() < JP) est_piece(i + 1, a - val, b - wt, s->U, s->dups, s->w / JP, RMODE == 2 ? 0 : f, RMODE == 2 ? 0 : mJ, RMODE == 2 ? 0 : MJ, val); }
                    }
                }
                if (val > recmax) recmax = val;
                int k3 = (NOCUT || val >= 1) && G[i][pS[i] - t][b - wt] > -INF && val + G[i][pS[i] - t][b - wt] >= a;
                int k4 = t < pS[i] && (NOCUT || val - c5 >= 1) && b - wt - c6 >= 0 && G[i][pS[i] - t - 1][b - wt - c6] > -INF && val - c5 + G[i][pS[i] - t - 1][b - wt - c6] >= a;
                if (i == 0 && HALFV > -INF) { if (k3 && val + G1[pS[i] - t][b - wt] < HALFV) k3 = 0; if (k4 && val - c5 + G1[pS[i] - t - 1][b - wt - c6] < HALFV) k4 = 0; }
                if (REV) { if (k3) k3 = rev_light(i, a - val, b - wt, pS[i] - t, f, pm, pM); if (k4) k4 = rev_heavy(i, a - val, b - wt, pS[i] - t, f, pm, pM); }
                if (k3 || k4) e_kept[i] += s->w;
                if (k3) { int m3 = pm < f ? pm : f, M3 = pM > f ? pM : f; for (int j = 0; j < nsucc3[q]; j++) expand(i, nxt, b, s, succ3[q][j], 0, 0, recmax, m3, M3); }
                if (k4) { int fh = f - PH, m4 = pm < fh ? pm : fh, M4 = pM > fh ? pM : fh; for (int j = 0; j < nsucc4[q]; j++) expand(i, nxt, b, s, succ4[q][j], 0, 1, recmax, m4, M4); }
            }
        }
        for (int n = 0; n < nlist[i][cur]; n++) lev[i][cur][list[i][cur][n]].set = 0;
        nlist[i][cur] = 0;
    }
    for (int a2 = 0; a2 < 2; a2++) { for (int n = 0; n < nlist[i][a2]; n++) lev[i][a2][list[i][a2][n]].set = 0; nlist[i][a2] = 0; }
    if (i > 0) e_jumps[i] += w0;
}

static time_t T0; static clock_t C0;
static void finish(void) {
    long long tk = 0, tt = 0;
    for (int i = 0; i < npc; i++) { printf("piece %d: kept %lld  rows tried %lld  completed %lld  jumps into it %lld\n", i + 1, kept[i], tries[i], comp[i], jumps[i]); tk += kept[i]; tt += tries[i]; }
    double sec = (double)(clock() - C0) / CLOCKS_PER_SEC;
    printf("delta (RMODE %d) of the objects met: positive %lld  zero %lld  negative %lld\n", RMODE, npos, nzero, nneg);
    printf("gate visits %lld\n", fcount);
    printf("RESULT: found %lld   kept %lld   rows tried %lld   time %.1fs (%.4f us per row tried)\n", found, tk, tt, sec, tt ? 1e6 * sec / tt : 0.0);
    fflush(stdout); exit(0);
}
int main(int argc, char **argv) {
    if (argc < 8) { fprintf(stderr, "usage: jt K capsfile run|est V W B piece... [REPS seed]\n"); return 2; }
    K = atoi(argv[1]); build();
    if (getenv("NOCUT")) NOCUT = atoi(getenv("NOCUT"));
    if (getenv("PART")) PARTI = atoi(getenv("PART"));
    if (getenv("NPARTS")) NPARTS = atoi(getenv("NPARTS"));
    if (getenv("DEPTH")) DEPTH = atoi(getenv("DEPTH"));
    if (getenv("JP")) JP = atof(getenv("JP"));
    if (getenv("PART2")) P2 = atoi(getenv("PART2"));
    if (getenv("NPARTS2")) NP2 = atoi(getenv("NPARTS2"));
    if (getenv("HYB")) HYB = atof(getenv("HYB"));
    if (getenv("HREP")) HREP = atoi(getenv("HREP"));
    if (getenv("RLO")) RLO = atoi(getenv("RLO"));
    if (getenv("RHI")) RHI = atoi(getenv("RHI"));
    if (getenv("REV")) REV = atoi(getenv("REV"));
    if (getenv("RMODE")) RMODE = atoi(getenv("RMODE"));
    if (getenv("PA")) PA = atoi(getenv("PA"));
    if (getenv("PB")) PB = atoi(getenv("PB"));
    if (getenv("PH")) PH = atoi(getenv("PH"));
    if (getenv("ORD")) ORD = atoi(getenv("ORD"));
    if (getenv("RP")) RP = atoi(getenv("RP"));
    if (getenv("STOP1")) STOP1 = atoi(getenv("STOP1"));
    readcaps(argv[2]);
    int est = !strcmp(argv[3], "est");
    V = atoi(argv[4]); W = atoi(argv[5]); B = atoi(argv[6]);
    if (W > WM - 2) { fprintf(stderr, "W too large\n"); return 2; }
    int ai = 7; npc = 0;
    while (ai < argc && (argv[ai][0] == 'R' || argv[ai][0] == 'S') && npc < MAXPC) {
        if (argv[ai][0] == 'R') { ptype[npc] = 1; pS[npc] = 0; } else { ptype[npc] = 0; pS[npc] = atoi(argv[ai] + 1); }
        npc++; ai++;
    }
    int REPS = ai < argc ? atoi(argv[ai]) : 100; long long seed = ai + 1 < argc ? atoll(argv[ai + 1]) : 1;
    mktables();
    for (int i = 1; i < npc; i++) samekind[i] = ptype[i] == ptype[i - 1] && pS[i] == pS[i - 1];
    if (ORD && npc == 2 && samekind[1]) HALFV = V > 0 ? (V + 1) / 2 : -INF;
    if (getenv("JCAP")) readjcap(getenv("JCAP"));
    mkrev();
    if (RP < 0 || RP >= npc) { fprintf(stderr, "RP out of range\n"); return 2; }
    printf("jr: RP=%d REV=%d RMODE=%d potential %d,%d,%d ORD=%d JCAP=%s\n", RP, REV, RMODE, PA, PB, PH, ORD, getenv("JCAP") ? getenv("JCAP") : "-");
    printf("jt K=%d caps=%s V=%d W=%d B=%d pieces", K, argv[2], V, W, B);
    for (int i = 0; i < npc; i++) { if (ptype[i]) printf(" R"); else printf(" S%d", pS[i]); }
    printf("  NOCUT=%d PART=%d/%d DEPTH=%d PART2=%d/%d RLO=%d RHI=%d  table bound of the total: %d\n", NOCUT, PARTI, NPARTS, DEPTH, P2, NP2, RLO, RHI, Best[0][W]);
    fflush(stdout);
    time_t t0 = time(NULL); clock_t c0 = clock(); T0 = t0; C0 = c0;
    if (!est) {
        if (HYB > 0) for (int i = 0; i < npc; i++) for (int a = 0; a < 2; a++) { lev[i][a] = (St *)calloc(NSTR, sizeof(St)); list[i][a] = (int *)malloc(sizeof(int) * NSTR); }
        const uint8_t *kr = ptype[0] ? getkeep(0, V, W) : NULL;
        rows(0, V, W, kr, 0, 0, 0, 0, 0, -INF, 0, 0, 0);
        long long tk = 0, tt = 0;
        for (int i = 0; i < npc; i++) { printf("piece %d: kept %lld  rows tried %lld  completed %lld  jumps into it %lld\n", i + 1, kept[i], tries[i], comp[i], jumps[i]); tk += kept[i]; tt += tries[i]; }
        double sec = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (HYB > 0) { double et = 0, ek = 0; for (int i = 1; i < npc; i++) { et += e_tries[i]; ek += e_kept[i]; } printf("HYBRID (piece 1 exhaustive, the rest ESTIMATED from %lld of %lld completed pieces): rows tried below %.4g  kept below %.4g  found (expected) %.4g\n", hyb_n, jumps[1], et, ek, e_found); }
        printf("delta (RMODE %d) of the objects met: positive %lld  zero %lld  negative %lld\n", RMODE, npos, nzero, nneg);
        printf("gate visits %lld\n", fcount);
        printf("RESULT: found %lld   kept %lld   rows tried %lld   time %.1fs (%.4f us per row tried)\n", found, tk, tt, sec, tt ? 1e6 * sec / tt : 0.0);
    } else {
        rng_s ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) rng();
        for (int i = 0; i < npc; i++) for (int a = 0; a < 2; a++) { lev[i][a] = (St *)calloc(NSTR, sizeof(St)); list[i][a] = (int *)malloc(sizeof(int) * NSTR); }
        double sum = 0, sum2 = 0, sk = 0;
        uint64_t U0[12]; memset(U0, 0, sizeof U0);
        for (int rep = 0; rep < REPS; rep++) {
            double before = 0; for (int i = 0; i < npc; i++) before += e_tries[i];
            est_piece(0, V, W, U0, 0, 1.0, 0, 0, 0, 0);
            double after = 0; for (int i = 0; i < npc; i++) after += e_tries[i];
            double tot = after - before; sum += tot; sum2 += tot * tot;
            if ((rep + 1) % (REPS / 5 > 0 ? REPS / 5 : 1) == 0) { fprintf(stderr, "rep %d: rows tried mean %.4g  t=%lds\n", rep + 1, sum / (rep + 1), (long)(time(NULL) - t0)); }
        }
        double mean = sum / REPS, var = (sum2 / REPS - mean * mean) / (REPS > 1 ? REPS - 1 : 1);
        for (int i = 0; i < npc; i++) { printf("piece %d: kept %.4g  rows tried %.4g  completed %.4g  jumps into it %.4g\n", i + 1, e_kept[i] / REPS, e_tries[i] / REPS, e_comp[i] / REPS, e_jumps[i] / REPS); sk += e_kept[i] / REPS; }
        printf("ESTIMATE: rows tried %.4g  standard error %.3g (%.0f%%)   kept %.4g   found (expected) %.4g   reps %d  time %lds\n", mean, sqrt(var), 100 * sqrt(var) / (mean > 0 ? mean : 1), sk, e_found / REPS, REPS, (long)(time(NULL) - t0));
    }
    return 0;
}
