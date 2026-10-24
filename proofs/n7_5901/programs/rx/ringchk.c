/* ringchk.c (referee n7-ref16b): third program for the exact ring row RX of PROOF_5901.md section 1.3, on 7 symbols.
 * Claim checked: for HLO <= H <= HHI a ring with exactly H holes has at most RX(H) rows (RX = line "R:" of the caps
 * file), given the chain row (line "0:": a chain with exactly x holes has at most P0(x) rows).
 * Search (cycle lemma, PROOF_5900 5.4 step 5 read for a ring ABOVE the row): a ring with T > RX(H) rows and H holes has
 * a rotation, starting at the identity after renaming, in which every prefix of r < T rows and d holes has
 * d T <= r H and T - r <= P0(H - d); and T <= P0(H).  A prefix is kept iff such a target (T, H) exists.
 * Geometry written from the definitions (own code, shared with bf2.c only).   usage: ringchk caps HLO HHI */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define K 7
#define L 6
#define NP 5040
static signed char PM[NP][8]; static int np_;
static short SG[NP], SGI[NP], TAU[NP], CL[NP], s3[NP][6]; static int n3[NP];
static int RK[823543];
static int code(const signed char *w) { int c = 0; for (int i = 0; i < K; i++) c = c * K + w[i]; return c; }
static void gen(signed char *w, int k) { if (k == K) { memcpy(PM[np_], w, K); RK[code(w)] = np_++; return; }
    for (int s = 0; s < K; s++) { int u = 0; for (int i = 0; i < k; i++) if (w[i] == s) u = 1; if (!u) { w[k] = (signed char)s; gen(w, k + 1); } } }
static int ew(int u, int v) { for (int t = 1; t < K; t++) { int ok = 1; for (int i = 0; i + t < K; i++) if (PM[u][i + t] != PM[v][i]) { ok = 0; break; } if (ok) return t; } return K; }
static int P0[200], RX[200], HLO, HHI;
static unsigned char keep[256][128], U[720];
static long long kept, tried, viol, rings;
static int st0;
static void node(int q, int r, int d);
static void row(int e, int r, int d) {
    int x = e, cs[8], len = 0;
    tried++;
    while (len < L) { int c = CL[x]; if (U[c]) break; U[c] = 1; cs[len++] = c;
        int d2 = d + L - len; if (d2 <= HHI) node(x, r + 1, d2); x = TAU[x]; }
    for (int k = 0; k < len; k++) U[cs[k]] = 0;
}
static void node(int q, int r, int d) {
    if (r >= 2) { int cl = 0; for (int j = 0; j < n3[q]; j++) if (s3[q][j] == st0) cl = 1;
        if (cl) { rings++; if (d >= HLO && r > RX[d]) { viol++; if (viol <= 5) printf("VIOLATION: ring with %d rows, %d holes\n", r, d); } } }
    if (r < 256 && keep[r][d]) { kept++; for (int j = 0; j < n3[q]; j++) row(s3[q][j], r, d); }
}
int main(int argc, char **argv) {
    signed char w[8]; gen(w, 0);
    for (int p = 0; p < NP; p++) { signed char v[8];
        for (int i = 0; i < K - 1; i++) v[i] = PM[p][i + 1]; v[K - 1] = PM[p][0]; SG[p] = (short)RK[code(v)];
        for (int i = 0; i < K - 2; i++) v[i] = PM[p][i + 1]; v[K - 2] = PM[p][0]; v[K - 1] = PM[p][K - 1]; TAU[p] = (short)RK[code(v)]; }
    for (int p = 0; p < NP; p++) SGI[SG[p]] = (short)p;
    for (int p = 0; p < NP; p++) CL[p] = -1;
    int nc = 0; for (int p = 0; p < NP; p++) if (CL[p] < 0) { int x = p; do { CL[x] = (short)nc; x = SG[x]; } while (x != p); nc++; }
    for (int q = 0; q < NP; q++) { int u = SGI[q]; n3[q] = 0; for (int v = 0; v < NP; v++) if (CL[v] != CL[q] && ew(u, v) == 3) { if (n3[q] >= 6) return 9; s3[q][n3[q]++] = (short)v; } }
    FILE *f = fopen(argv[1], "r"); char line[1 << 14]; int n0 = 0, nr = 0;
    while (fgets(line, sizeof line, f)) { int *t = NULL, *n = NULL;
        if (!strncmp(line, "0:", 2)) { t = P0; n = &n0; } else if (!strncmp(line, "R:", 2)) { t = RX; n = &nr; } else continue;
        for (char *tok = strtok(line + 2, " \t\r\n"); tok; tok = strtok(NULL, " \t\r\n")) t[(*n)++] = atoi(tok); }
    HLO = atoi(argv[2]); HHI = atoi(argv[3]);
    if (HHI >= n0 || HHI >= nr) return 8;
    for (int r = 1; r < 256; r++) for (int d = 0; d <= HHI; d++) for (int H = d > HLO ? d : HLO; H <= HHI && !keep[r][d]; H++) {
        int lo = RX[H] + 1 > r + 1 ? RX[H] + 1 : r + 1, hi = P0[H];
        if (r + P0[H - d] < hi) hi = r + P0[H - d];
        if (d > 0 && (r * H) / d < hi) hi = (r * H) / d;
        if (lo <= hi) keep[r][d] = 1;
    }
    st0 = 0; row(0, 0, 0);
    printf("ringchk %s holes %d..%d: violations %lld  kept %lld  tried %lld  rings closed %lld  (classes %d, light successors %d)\n", argv[1], HLO, HHI, viol, kept, tried, rings, nc, n3[0]);
    return 0;
}
