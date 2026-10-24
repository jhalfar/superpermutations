#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define K 7
#define NP 5040
#define NC 720
#define NY 840
#define L 6
#define INF 1000000
static int8_t PERM[NP][8];
static int *RK;
static int16_t SIG[NP], SIGI[NP], T2[NP], CLS[NP], CYC[NP];
static int16_t succ3[NP][8], succ4[NP][32];
static int nsucc3[NP], nsucc4[NP];
static int16_t CC[NC][7];      /* the 7 two-cycles through a class */
static int16_t YC[NY][6];      /* the 6 classes of a two-cycle */

static int code(const int8_t *w) { int c = 0; for (int i = 0; i < K; i++) c = c * K + w[i]; return c; }
static int ewf(int u, int v) {
    for (int t = 1; t < K; t++) { int ok = 1; for (int i = 0; i + t < K; i++) if (PERM[u][i + t] != PERM[v][i]) { ok = 0; break; } if (ok) return t; }
    return K;
}
static void build(void) {
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
    int nc = 0;
    for (int p = 0; p < NP; p++) if (CLS[p] < 0) { int x = p; do { CLS[x] = (int16_t)nc; x = SIG[x]; } while (x != p); nc++; }
    for (int p = 0; p < NP; p++) CYC[p] = -1;
    int ny = 0;
    for (int p = 0; p < NP; p++) if (CYC[p] < 0) { int x = p, i = 0; do { CYC[x] = (int16_t)ny; YC[ny][i++] = CLS[x]; x = T2[x]; } while (x != p); if (i != 6) exit(9); ny++; }
    if (nc != NC || ny != NY) { fprintf(stderr, "geometry\n"); exit(9); }
    { int fill[NC]; memset(fill, 0, sizeof fill);
      for (int p = 0; p < NP; p++) { int c = CLS[p]; CC[c][fill[c]++] = CYC[p]; }
      for (int c = 0; c < NC; c++) { if (fill[c] != 7) exit(9); for (int i = 0; i < 7; i++) for (int j = 0; j < i; j++) if (CC[c][i] == CC[c][j]) exit(9); } }
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

#define SM 12
#define GM 128
#define RM 256
static int P[SM][400];
static int TS, GTOP, G, LO = -1, CUT = 0;
static uint8_t keepN[SM][GM][RM], keepS[SM][GM][RM];
static int16_t phiN[SM][GM][RM], phiS[SM][GM][RM];   /* least Phi that keeps (only with CUT) */
static int POTA = 2, POTB = 3, POTH = 5;   /* potential of a cut: POTA rows - POTB holes - 2 POTH (links of weight 4 before the cut) - POTH [the cut link has weight 4] */
static int16_t revA1[SM][GM][RM], revA2[SM][GM][RM];   /* CUT bit 4 (Lemma REV): keep iff M + m >= A1 or m >= A2 */

static void readcaps(const char *fn) {
    for (int s = 0; s < SM; s++) for (int i = 0; i < 400; i++) P[s][i] = INF;
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "no caps file %s\n", fn); exit(1); }
    char *line = (char *)malloc(1 << 16);
    while (fgets(line, 1 << 16, f)) {
        char *p = strchr(line, ':'); if (!p || line[0] == '#') continue;
        int t = atoi(line), i = 0; p++;
        if (t < 0 || t >= SM) continue;
        char *tok = strtok(p, " \t\r\n");
        while (tok && i < 400) { P[t][i++] = atoi(tok); tok = strtok(NULL, " \t\r\n"); }
    }
    fclose(f);
}
static void tables(void) {
    G = GTOP - L * TS;
    if (G >= GM) exit(2);
    for (int s = 0; s <= TS; s++) for (int x = 0; x <= G; x++) if (P[s][x] >= INF) { fprintf(stderr, "caps row %d does not reach %d\n", s, G); exit(1); }
    for (int t = 0; t <= TS; t++) for (int d = 0; d < GM; d++) for (int r = 0; r < RM; r++) {
        int a = 0, b = 0, pa = INF, pb = INF;
        for (int x = d > LO ? d : LO + 1; x <= G; x++) {
            int need = P[TS][x] - r - (x - d) + 1;     /* Phi >= need  <=>  r + (x-d) + Phi > P_S(x) */
            if (r + P[TS - t][x - d] > P[TS][x]) { a = 1; if (need < pa) pa = need; }
            if (t < TS && r + P[TS - t - 1][x - d] > P[TS][x]) { b = 1; if (need < pb) pb = need; }
        }
        keepN[t][d][r] = (uint8_t)a; keepS[t][d][r] = (uint8_t)b;
        phiN[t][d][r] = (int16_t)(a ? (pa < -30000 ? -30000 : pa) : 30000);
        phiS[t][d][r] = (int16_t)(b ? (pb < -30000 ? -30000 : pb) : 30000);
        /* Lemma REV: potential f = POTA rows - POTB holes; c(x) = least f of a counterexample at level x;
           rise(E) = most that a later segment with at most E holes can add */
        int a1 = 30000, a2 = 30000, f = POTA * r - POTB * d - 2 * POTH * t;
        int rise = 0;
        for (int x = d; x <= G; x++) {
            for (int sB = 0; sB <= TS - t; sB++) { int v = POTA * P[sB][x - d] - POTB * (x - d) - 2 * POTH * sB; if (v > rise) rise = v; }
            if (x <= LO) continue;
            int ok = (r + P[TS - t][x - d] > P[TS][x]) || (t < TS && r + P[TS - t - 1][x - d] > P[TS][x]);
            if (!ok) continue;
            int c = POTA * (P[TS][x] + 1) - POTB * x - 2 * POTH * TS;
            if (c < a1) a1 = c;
            if (!(CUT & 8)) { if (c - f - rise < a2) a2 = c - f - rise; }
            else {
                /* the peak is a proper prefix with d' holes, d <= d' <= x, and t' >= t links: its potential is at most
                   U(d') = max_t' (POTA P_t'(d') - POTB d') and at most f + seg(d' - d) */
                int best = -30000;
                for (int d2 = d; d2 <= x; d2++) {
                    int U = -30000, sg = -30000;
                    for (int t2 = t; t2 <= TS; t2++) { int v = POTA * P[t2][d2] - POTB * d2 - 2 * POTH * t2; if (v > U) U = v; }
                    for (int sB = 0; sB <= TS - t; sB++) { int v = POTA * P[sB][d2 - d] - POTB * (d2 - d) - 2 * POTH * sB; if (v > sg) sg = v; }
                    int pk = f + sg < U ? f + sg : U;
                    if (pk > best) best = pk;
                }
                if (c - best < a2) a2 = c - best;
            }
        }
        revA1[t][d][r] = (int16_t)(a1 < -30000 ? -30000 : a1); revA2[t][d][r] = (int16_t)(a2 < -30000 ? -30000 : a2);
    }
}
