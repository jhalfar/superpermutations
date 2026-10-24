// k2.cpp -- second, independent program for the kernel-alone statements on 7 symbols.
// Written from the texts only (PROOF_5899.md 8.1, PROOF_CUTS.md, MODEL.md); agent n7-second, 2026-10-09.
// Geometry is built from the definitions at every start (no table of another program is read).
//
// usage: k2 TABFILE S LO G CUT a b h DEPTH NPARTS PART [OUTFILE]
//   statement: every sequence with exactly S links of weight 4 and LO < x <= G holes has at most P_S(x) rows
//   CUT = 0 plain rule of 8.1;  CUT = 12 plain rule and Lemma REV with the term U (tables A1, A2)
//   DEPTH = gate (rows), NPARTS, PART: kept prefixes with DEPTH rows are numbered; part PART takes number % NPARTS.
//   G = -1 means "last column of row S".
// usage: k2 selftest    (geometry counts and Lemma RV from the definitions)
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cstdint>
#include <ctime>
#include <string>
#include <vector>
#include <algorithm>
#include <chrono>
#ifdef _WIN32
#include <direct.h>
#define MKDIR(p) _mkdir(p)
#define RMDIR(p) _rmdir(p)
#else
#include <sys/stat.h>
#include <unistd.h>
#define MKDIR(p) mkdir(p, 0777)
#define RMDIR(p) rmdir(p)
#endif
// returns false if the part is finished or claimed by another process
static bool claimPart(const char *out) {
    if (!out) return true;
    FILE *f = fopen(out, "r"); if (f) { fclose(f); return false; }
    return MKDIR((std::string(out) + ".claim").c_str()) == 0;
}
static void releasePart(const char *out) { if (out) RMDIR((std::string(out) + ".claim").c_str()); }
using namespace std;
typedef unsigned long long ull;

static const int K = 7, NV = 5040, NC = 720, INF = 1 << 28;
static int8_t PW[NV][K];
static int pidx[1 << 21];
static int clsOf[NV];
static uint16_t rowent[NV][6], rowcls[NV][6];
static uint16_t s3[NV][5], s4[NV][23];

static int codeOf(const int8_t *p) { int c = 0; for (int i = 0; i < K; i++) c = c * 8 + p[i]; return c; }
static int ew(const int8_t *u, const int8_t *v) {
    for (int t = 1; t < K; t++) { bool ok = true; for (int i = t; i < K; i++) if (u[i] != v[i - t]) { ok = false; break; } if (ok) return t; }
    return K;
}
static int sigma(int v) { int8_t w[K]; for (int i = 0; i < K - 1; i++) w[i] = PW[v][i + 1]; w[K - 1] = PW[v][0]; return pidx[codeOf(w)]; }
static int sigmaInv(int v) { int8_t w[K]; w[0] = PW[v][K - 1]; for (int i = 1; i < K; i++) w[i] = PW[v][i - 1]; return pidx[codeOf(w)]; }
static int tau2(int v) { int8_t w[K]; for (int i = 0; i < K - 2; i++) w[i] = PW[v][i + 1]; w[K - 2] = PW[v][0]; w[K - 1] = PW[v][K - 1]; return pidx[codeOf(w)]; }
static int rev(int v) { int8_t w[K]; for (int i = 0; i < K; i++) w[i] = PW[v][K - 1 - i]; return pidx[codeOf(w)]; }

static void buildGeometry() {
    int8_t p[16]; for (int i = 0; i < K; i++) p[i] = i;
    memset(pidx, -1, sizeof pidx);
    int n = 0;
    do { memcpy(PW[n], p, K); pidx[codeOf(p)] = n; n++; } while (next_permutation(p, p + K));
    if (n != NV) { fprintf(stderr, "perm count\n"); exit(2); }
    for (int v = 0; v < NV; v++) clsOf[v] = -1;
    int nc = 0;
    for (int v = 0; v < NV; v++) if (clsOf[v] < 0) { int w = v; for (int i = 0; i < K; i++) { clsOf[w] = nc; w = sigma(w); } if (w != v) { fprintf(stderr, "rotation\n"); exit(2); } nc++; }
    if (nc != NC) { fprintf(stderr, "class count %d\n", nc); exit(2); }
    for (int v = 0; v < NV; v++) { int e = v; for (int j = 0; j < 6; j++) { rowent[v][j] = e; rowcls[v][j] = clsOf[e]; e = tau2(e); } if (e != v) { fprintf(stderr, "tau2 order\n"); exit(2); }
        for (int j = 0; j < 6; j++) for (int i = 0; i < j; i++) if (rowcls[v][i] == rowcls[v][j]) { fprintf(stderr, "2-cycle classes\n"); exit(2); } }
    for (int g = 0; g < NV; g++) {
        int q = sigmaInv(g), n3 = 0, n4 = 0;
        for (int v = 0; v < NV; v++) {
            if (clsOf[v] == clsOf[q]) continue;
            int w = ew(PW[q], PW[v]);
            if (w == 3) { if (n3 >= 5) { fprintf(stderr, "s3 count\n"); exit(2); } s3[g][n3++] = v; }
            else if (w == 4) { if (n4 >= 23) { fprintf(stderr, "s4 count\n"); exit(2); } s4[g][n4++] = v; }
            else if (w < 3) { // weight 2 between classes is the door only
                if (!(w == 2 && v == tau2(g))) { fprintf(stderr, "light edge\n"); exit(2); } }
        }
        if (n3 != 5 || n4 != 23) { fprintf(stderr, "succ counts %d %d\n", n3, n4); exit(2); }
    }
}

static int selftest() {
    // Lemma RV: rho(e) = reverse(sigma^-1(e))
    static int rho[NV];
    for (int e = 0; e < NV; e++) rho[e] = rev(sigmaInv(e));
    long bad = 0;
    for (int e = 0; e < NV; e++) { if (rho[rho[e]] != e) bad++; if (tau2(rho[tau2(e)]) != rho[e]) bad++; }
    static int cmap[NC]; for (int c = 0; c < NC; c++) cmap[c] = -1;
    for (int e = 0; e < NV; e++) { int c = clsOf[e], c2 = clsOf[rho[e]]; if (cmap[c] < 0) cmap[c] = c2; else if (cmap[c] != c2) bad++; }
    static char seen[NC]; memset(seen, 0, sizeof seen);
    for (int c = 0; c < NC; c++) { if (seen[cmap[c]]) bad++; seen[cmap[c]] = 1; }
    long pairs = 0;
    // v weight-w successor of exit of block q  <=>  rho(q) weight-w successor of exit of block rho(v)
    for (int q = 0; q < NV; q++) {
        for (int i = 0; i < 5; i++) { int v = s3[q][i]; pairs++; bool ok = false; for (int j = 0; j < 5; j++) if (s3[rho[v]][j] == rho[q]) ok = true; if (!ok) bad++; }
        for (int i = 0; i < 23; i++) { int v = s4[q][i]; pairs++; bool ok = false; for (int j = 0; j < 23; j++) if (s4[rho[v]][j] == rho[q]) ok = true; if (!ok) bad++; }
    }
    printf("geometry: %d entries, %d classes, 5 successors of weight 3 and 23 of weight 4 for every entry: OK\n", NV, NC);
    printf("Lemma RV: involution, classes, tau2 relation, %ld successor pairs: %s (bad = %ld)\n", pairs, bad ? "FAIL" : "OK", bad);
    return bad ? 1 : 0;
}

// ---------------- tables
static vector<vector<int>> T;
static ull tabHash = 1469598103934665603ULL;
static void loadTables(const char *fn) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
    static char line[1 << 16];
    while (fgets(line, sizeof line, f)) {
        for (char *c = line; *c; c++) if (*c != '\r' && *c != '\n') { tabHash ^= (unsigned char)*c; tabHash *= 1099511628211ULL; }
        char *col = strchr(line, ':'); if (!col) continue;
        if (line[0] < '0' || line[0] > '9') continue; // ring row and others are not used here
        int s = atoi(line);
        if ((int)T.size() <= s) T.resize(s + 1);
        char *p = col + 1, *e;
        for (;;) { long v = strtol(p, &e, 10); if (e == p) break; T[s].push_back((int)v); p = e; }
    }
    fclose(f);
}

static int S, LO, G, CUT, pa, pb, ph, DEPTH; static ull NPARTS, PART;
static const int RMAX = 200, DMAX = 100, SMAX = 12;
static int need3[SMAX][DMAX], need4[SMAX][DMAX], violR[SMAX][DMAX];
static int A1[SMAX][DMAX][RMAX], A2[SMAX][DMAX][RMAX];
static uint8_t MASK[SMAX][DMAX][RMAX];
static uint8_t LNEED[64];

static void buildRule() {
    for (int t = 0; t < SMAX; t++) for (int d = 0; d < DMAX; d++) { need3[t][d] = need4[t][d] = violR[t][d] = INF; }
    for (int t = 0; t <= S; t++) for (int d = 0; d <= G; d++) {
        for (int x = max(d, LO + 1); x <= G; x++) {
            need3[t][d] = min(need3[t][d], T[S][x] - T[S - t][x - d] + 1);
            if (t < S) need4[t][d] = min(need4[t][d], T[S][x] - T[S - t - 1][x - d] + 1);
        }
        if (t == S && d > LO) violR[t][d] = T[S][d] + 1;
    }
    for (int t = 0; t <= S; t++) for (int d = 0; d < DMAX; d++) for (int r = 0; r < RMAX; r++) { A1[t][d][r] = INF; A2[t][d][r] = INF; }
    if (CUT & 4) {
        for (int t = 0; t <= S; t++) {
            vector<int> seg(G + 1), U(G + 1);
            for (int e = 0; e <= G; e++) { int b = -INF; for (int u = 0; u <= S - t; u++) b = max(b, pa * T[u][e] - pb * e - 2 * ph * u); seg[e] = b; }
            for (int y = 0; y <= G; y++) { int b = -INF; for (int u = t; u <= S; u++) b = max(b, pa * T[u][y] - pb * y - 2 * ph * u); U[y] = b; }
            for (int d = 0; d <= G; d++) for (int r = 0; r < RMAX; r++) {
                int f = pa * r - pb * d - 2 * ph * t, a1 = INF, a2 = INF;
                for (int x = max(d, LO + 1); x <= G; x++) {
                    bool al = (r + T[S - t][x - d] > T[S][x]) || (t < S && r + T[S - t - 1][x - d] > T[S][x]);
                    if (!al) continue;
                    int c = pa * (T[S][x] + 1) - pb * x - 2 * ph * S;
                    a1 = min(a1, c);
                    int best = -INF;
                    for (int e = 0; e <= x - d; e++) { int w = (CUT & 8) ? min(U[d + e], f + seg[e]) : f + seg[e]; best = max(best, w); }
                    a2 = min(a2, c - best);
                }
                A1[t][d][r] = a1; A2[t][d][r] = a2;
            }
        }
    }
    memset(MASK, 0, sizeof MASK);
    for (int t = 0; t <= S; t++) for (int d = 0; d <= G; d++) for (int r = 0; r < RMAX; r++) {
        int m = 0;
        for (int k = 0; k < 6 && d + k <= G; k++) { int lim = min(min(need3[t][d + k], need4[t][d + k]), violR[t][d + k]); if (r >= lim) m |= 1 << k; }
        MASK[t][d][r] = m;
    }
    for (int m = 0; m < 64; m++) { int l = 0; for (int k = 5; k >= 0; k--) if (m >> k & 1) l = 6 - k; LNEED[m] = l; }
}

static uint8_t used[NC];
static ull keptBelow, keptTop, placedBelow, placedTop, violBelow, violTop, gateCount;
static bool below; // true while under a gate prefix of this part
static int pathE[RMAX], pathL[RMAX];
static FILE *vlog;

static void node(int g, int r, int d, int t, int mp, int Mp);

static inline void expand(int g, int r, int d, int tn, int m, int M, const uint16_t *succ, int ns) {
    int r1 = r + 1;
    if (r1 >= RMAX) { fprintf(stderr, "RMAX\n"); exit(2); }
    unsigned mask = MASK[tn][d][r1];
    if (!mask) return;
    int lmax = LNEED[mask];
    for (int i = 0; i < ns; i++) {
        int v = succ[i];
        const uint16_t *rc = rowcls[v];
        int l = 0;
        for (; l < lmax; l++) {
            int c = rc[l];
            if (used[c]) break;
            used[c] = 1;
            int k = 5 - l;
            if (mask >> k & 1) { pathE[r] = v; pathL[r] = l + 1; node(rowent[v][l], r1, d + k, tn, m, M); }
        }
        while (l > 0) { --l; used[rc[l]] = 0; }
    }
}

static void node(int g, int r, int d, int t, int mp, int Mp) {
    if (below) placedBelow++; else placedTop++;
    if (r >= violR[t][d]) {
        if (below) violBelow++; else violTop++;
        if (vlog && (below || PART == 0)) { fprintf(vlog, "VIOLATION rows %d holes %d links %d:", r, d, t); for (int i = 0; i < r; i++) { fprintf(vlog, " "); for (int j = 0; j < K; j++) fprintf(vlog, "%d", PW[pathE[i]][j] + 1); fprintf(vlog, ":%d", pathL[i]); } fprintf(vlog, "\n"); fflush(vlog); }
    }
    bool p3 = r >= need3[t][d], p4 = r >= need4[t][d];
    int m3 = mp, M3 = Mp, m4 = mp, M4 = Mp;
    if (CUT & 4) {
        int f = pa * r - pb * d - 2 * ph * t, a1 = A1[t][d][r], a2 = A2[t][d][r];
        if (f < m3) m3 = f; if (f > M3) M3 = f;
        if (f - ph < m4) m4 = f - ph; if (f - ph > M4) M4 = f - ph;
        p3 = p3 && (m3 == 0 || M3 + m3 >= a1 || m3 >= a2);
        p4 = p4 && (m4 == 0 || M4 + m4 >= a1 || m4 >= a2);
    }
    if (!(p3 || p4)) return;
    bool gate = false;
    if (below) keptBelow++;
    else if (r < DEPTH) keptTop++;
    else { ull id = gateCount++; if (id % NPARTS != PART) return; gate = true; below = true; keptBelow++; }
    if (p3) expand(g, r, d, t, m3, M3, s3[g], 5);
    if (p4) expand(g, r, d, t + 1, m4, M4, s4[g], 23);
    if (gate) below = false;
}

int main(int argc, char **argv) {
    if (argc > 12 && !claimPart(argv[12])) return 0;
    buildGeometry();
    if (argc >= 2 && !strcmp(argv[1], "selftest")) return selftest();
    if (argc < 12) { fprintf(stderr, "usage: k2 TABFILE S LO G CUT a b h DEPTH NPARTS PART [OUTFILE]\n"); return 2; }
    loadTables(argv[1]);
    S = atoi(argv[2]); LO = atoi(argv[3]); G = atoi(argv[4]); CUT = atoi(argv[5]);
    pa = atoi(argv[6]); pb = atoi(argv[7]); ph = atoi(argv[8]);
    DEPTH = atoi(argv[9]); NPARTS = strtoull(argv[10], 0, 10); PART = strtoull(argv[11], 0, 10);
    const char *out = argc > 12 ? argv[12] : 0;
    if (S < 0 || S >= SMAX || (int)T.size() <= S) { fprintf(stderr, "no row %d in the tables\n", S); return 2; }
    if (G < 0) G = (int)T[S].size() - 1;
    for (int u = 0; u <= S; u++) if ((int)T[u].size() <= G) { fprintf(stderr, "row %d of the tables is shorter than G\n", u); return 2; }
    if (G >= DMAX - 6) { fprintf(stderr, "G too large\n"); return 2; }
    if (CUT != 0 && CUT != 4 && CUT != 12) { fprintf(stderr, "CUT must be 0, 4 or 12\n"); return 2; }
    if ((CUT & 4) && (pa <= 0 || ph < 0)) { fprintf(stderr, "Lemma REV needs a > 0, h >= 0\n"); return 2; }
    if (NPARTS < 1 || PART >= NPARTS || (DEPTH < 1 && NPARTS > 1)) { fprintf(stderr, "bad parts\n"); return 2; }
    buildRule();
    string tmp;
    if (out) { tmp = string(out) + ".tmp"; vlog = fopen((string(out) + ".viol").c_str(), "w"); }
    auto t0 = chrono::steady_clock::now();
    // the empty prefix: its only successors are the rows that start at 1 2 .. 7
    int id = 0; // identity is the first permutation in lexicographic order
    below = (DEPTH <= 0);
    {
        unsigned mask = MASK[0][0][1];
        int lmax = LNEED[mask];
        for (int l = 0; l < lmax; l++) {
            used[rowcls[id][l]] = 1;
            int k = 5 - l;
            if (mask >> k & 1) { pathE[0] = id; pathL[0] = l + 1; node(rowent[id][l], 1, k, 0, 0, 0); }
        }
    }
    double sec = chrono::duration<double>(chrono::steady_clock::now() - t0).count();
    double cpu = (double)clock() / CLOCKS_PER_SEC;
    if (vlog) { fclose(vlog); if (violBelow + (PART == 0 ? violTop : 0) == 0) remove((string(out) + ".viol").c_str()); }
    FILE *f = out ? fopen(tmp.c_str(), "w") : stdout;
    if (!f) { fprintf(stderr, "cannot write %s\n", tmp.c_str()); return 2; }
    fprintf(f, "k2 statement: tables %016llx S %d LO %d G %d CUT %d potential %d,%d,%d\n", tabHash, S, LO, G, CUT, pa, pb, ph);
    fprintf(f, "gate: depth %d parts %llu gate_count %llu kept_top %llu placed_top %llu violations_top %llu\n", DEPTH, NPARTS, gateCount, keptTop, placedTop, violTop);
    fprintf(f, "part %llu kept_below %llu placed_below %llu violations_below %llu\n", PART, keptBelow, placedBelow, violBelow);
    fprintf(f, "time: wall %.1f cpu %.1f\n", sec, cpu);
    fprintf(f, "END\n");
    if (out) { fclose(f); remove(out); if (rename(tmp.c_str(), out)) { fprintf(stderr, "rename failed\n"); return 2; } releasePart(out); }
    return 0;
}
