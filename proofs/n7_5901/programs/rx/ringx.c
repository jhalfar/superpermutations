// ringx.c: rings on 7 symbols by EXACT number of holes (agent n7-ring16, 2026-10-12).
// Written from the definitions of the proof of 5,900 (proofs/lean/n7_5900/PROOF_5900.md) section 1 and the rule of
// the written proof of 5,899 (not public; [P] in PROOF_5901.md) section 8.2. Shares no code with j2.cpp / jt.c / jr.c / ref.c.
//
//   ringx prove  CAPS LO HI [DEPTH NPARTS PART]
//        static rule: is there a ring with exactly H holes, LO <= H <= HI, and more than R(H) rows?
//        prints kept / tried / found.
//   ringx ladder CAPS LO HI DELTA [DEPTH NPARTS PART]
//        starts from Q(H) = R(H) - DELTA on LO..HI; every ring found with more than Q(H) rows raises Q(H)
//        and is printed. At the end Q(H) is an upper bound for every H in LO..HI (for the whole run, all
//        parts together), exact where a ring was printed.
// CAPS: file with the lines "0: ..." (chain row M) and "R: ..." (ring row).
// Parts: the prefixes with DEPTH rows are split by a hash of the prefix (independent of the tables).
// TOP=FILE (environment): targets only up to the ring row of FILE (counts the ring tree of a joint statement
//   whose lowest target is R(H) + 1 of CAPS and whose cap is the ring row of FILE); not for proofs of a table.
// LONG=1 (environment): longer rows first (same tree, other order; for the ladder).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define NV 5040
#define HM 97
#define RM 240
static unsigned char P[NV][7];
static int *code2idx;
static int cls[NV], t2[NV], suc[NV][5];
static int M[HM], R[HM], Q[HM], TOP[HM], nM, nR;
static int LO, HI, ladder, DEPTH = 0, LONG = 0;
static unsigned long long NPARTS = 1, PART = 0;
static unsigned long long kept, tried, found;
static unsigned char used[720];
static int pe[RM], pl[RM];
static signed char cache[RM][HM];
static int code(const unsigned char *w) { int c = 0; for (int i = 0; i < 7; i++) c = c * 7 + w[i]; return c; }
static int ewf(const unsigned char *u, const unsigned char *v) {
    for (int t = 1; t < 7; t++) { int ok = 1; for (int i = t; i < 7; i++) if (u[i] != v[i - t]) { ok = 0; break; } if (ok) return t; }
    return 7;
}
static void gen(unsigned char *w, int n, int *cnt) {
    if (n == 7) { memcpy(P[*cnt], w, 7); code2idx[code(w)] = *cnt; (*cnt)++; return; }
    for (int s = 0; s < 7; s++) { int ok = 1; for (int i = 0; i < n; i++) if (w[i] == s) ok = 0; if (ok) { w[n] = s; gen(w, n + 1, cnt); } }
}
static int canon(int v) { unsigned char w[7]; int z = 0; while (P[v][z] != 0) z++; for (int i = 0; i < 7; i++) w[i] = P[v][(z + i) % 7]; return code2idx[code(w)]; }
static void geometry(void) {
    code2idx = malloc(sizeof(int) * 823543); unsigned char w[7]; int cnt = 0; gen(w, 0, &cnt);
    if (cnt != NV) { fprintf(stderr, "count\n"); exit(2); }
    int nc = 0;
    for (int v = 0; v < NV; v++) cls[v] = -1;
    for (int v = 0; v < NV; v++) if (canon(v) == v) cls[v] = nc++;   // class = the rotation that starts with symbol 0
    if (nc != 720) { fprintf(stderr, "classes\n"); exit(2); }
    for (int v = 0; v < NV; v++) cls[v] = cls[canon(v)];
    for (int v = 0; v < NV; v++) {
        // tau2: rotate the first 6 letters
        for (int i = 0; i < 5; i++) w[i] = P[v][i + 1];
        w[5] = P[v][0]; w[6] = P[v][6]; t2[v] = code2idx[code(w)];
        // exit of the block entered at v: last letter to the front
        unsigned char u[7]; u[0] = P[v][6]; for (int i = 1; i < 7; i++) u[i] = P[v][i - 1];
        // weight-3 successors: last 4 letters of u, then the first 3 letters of u in any order; not the class of u
        static const int pm[6][3] = {{0,1,2},{0,2,1},{1,0,2},{1,2,0},{2,0,1},{2,1,0}};
        int n = 0;
        for (int p = 0; p < 6; p++) {
            for (int i = 0; i < 4; i++) w[i] = u[3 + i];
            for (int i = 0; i < 3; i++) w[4 + i] = u[pm[p][i]];
            int x = code2idx[code(w)];
            if (ewf(u, w) != 3) { fprintf(stderr, "weight\n"); exit(2); }
            if (cls[x] == cls[v]) continue;
            if (n >= 5) { fprintf(stderr, "succ\n"); exit(2); }
            suc[v][n++] = x;
        }
        if (n != 5) { fprintf(stderr, "succ count\n"); exit(2); }
    }
}
static int readrow(const char *fn, const char *tag, int *dst) {
    FILE *f = fopen(fn, "r"); if (!f) { fprintf(stderr, "cannot open %s\n", fn); exit(2); }
    static char line[1 << 16]; int n = -1; size_t tl = strlen(tag);
    while (fgets(line, sizeof line, f)) if (!strncmp(line, tag, tl)) {
        char *p = line + tl, *e; n = 0;
        for (;;) { long v = strtol(p, &e, 10); if (e == p) break; if (n < HM) dst[n] = (int)v; n++; p = e; }
    }
    fclose(f); if (n < 0) { fprintf(stderr, "row %s missing\n", tag); exit(2); } return n;
}
// the rule of PROOF_5899 8.2 with the window LO..HI: a prefix with r rows and d holes is continued if there are
// H and T with Q(H) < T <= M(H), r < T, d <= H, d T <= r H, T - r <= M(H - d).
static int keepf(int r, int d) {
    int lo = d > LO ? d : LO;
    for (int H = lo; H <= HI; H++) {
        int a = Q[H] + 1; if (a < r + 1) a = r + 1;
        int b = M[H]; if (TOP[H] < b) b = TOP[H]; if (r + M[H - d] < b) b = r + M[H - d];
        if (d > 0 && (r * H) / d < b) b = (r * H) / d;
        if (a <= b) return 1;
    }
    return 0;
}
static void printring(int r, int d) {
    printf("RING rows %d holes %d :", r, d);
    for (int i = 0; i < r; i++) { printf(" "); for (int j = 0; j < 7; j++) printf("%d", P[pe[i]][j] + 1); printf("/%d", pl[i]); }
    printf("\n"); fflush(stdout);
}
static void node(int g, int r, int d);
static void tryrow(int v, int r, int d) {
    tried++;
    if (r + 1 >= RM) { fprintf(stderr, "RM\n"); exit(2); }
    int e = v, l = 0; int c[6], en[6];
    pe[r] = v;
    if (!LONG) {
        for (; l < 6; l++) {
            c[l] = cls[e]; if (used[c[l]]) break; used[c[l]] = 1;
            pl[r] = l + 1;
            node(e, r + 1, d + 5 - l);
            e = t2[e];
        }
        while (l > 0) used[c[--l]] = 0;
    } else {
        for (; l < 6; l++) { c[l] = cls[e]; if (used[c[l]]) break; used[c[l]] = 1; en[l] = e; e = t2[e]; }
        while (l > 0) { pl[r] = l; node(en[l - 1], r + 1, d + 6 - l); used[c[--l]] = 0; }
    }
}
static unsigned long long hashpath(int r) {
    unsigned long long h = 1469598103934665603ULL;
    for (int i = 0; i < r; i++) { h ^= (unsigned long long)(pe[i] * 8 + pl[i]); h *= 1099511628211ULL; h ^= h >> 29; }
    return h;
}
static int below;
static void node(int g, int r, int d) {
    if (d > HI) return;
    if (r >= 2 && d >= LO && r > Q[d]) {
        int cl = 0; for (int j = 0; j < 5; j++) if (suc[g][j] == pe[0]) cl = 1;
        if (cl) {
            if (below || PART == 0) { found++; if (ladder || found <= 20) printring(r, d); }
            if (ladder) { Q[d] = r; memset(cache, 0, sizeof cache); }
        }
    }
    signed char *c = &cache[r][d];
    if (!*c) *c = keepf(r, d) ? 1 : 2;
    if (*c != 1) return;
    int was = below;
    if (!below && r == DEPTH) { if (hashpath(r) % NPARTS != PART) return; below = 1; }
    if (below || PART == 0) kept++;
    for (int j = 0; j < 5; j++) tryrow(suc[g][j], r, d);
    below = was;
}
int main(int argc, char **argv) {
    if (argc < 5) { fprintf(stderr, "usage: ringx prove|ladder CAPS LO HI [DELTA] [DEPTH NPARTS PART]\n"); return 2; }
    ladder = !strcmp(argv[1], "ladder");
    if (getenv("LONG")) LONG = atoi(getenv("LONG"));
    nM = readrow(argv[2], "0:", M); nR = readrow(argv[2], "R:", R);
    LO = atoi(argv[3]); HI = atoi(argv[4]); int a = 5, delta = 0;
    if (ladder) { if (argc < 6) return 2; delta = atoi(argv[a++]); }
    if (argc >= a + 3) { DEPTH = atoi(argv[a]); NPARTS = strtoull(argv[a + 1], 0, 10); PART = strtoull(argv[a + 2], 0, 10); }
    if (LO < 0 || HI >= HM || HI >= nM || HI >= nR || PART >= NPARTS) { fprintf(stderr, "bad arguments\n"); return 2; }
    for (int i = 0; i < HM; i++) { Q[i] = R[i]; TOP[i] = 1 << 20; }
    if (getenv("TOP")) readrow(getenv("TOP"), "R:", TOP);   // TOP=file: only targets T <= the ring row of that file (to count the ring tree of a joint statement)
    for (int i = LO; i <= HI; i++) { Q[i] = R[i] - delta; if (Q[i] < 1) Q[i] = 1; }
    geometry();
    below = (DEPTH == 0);
    tried = 1;
    {   // the first row starts at the word 1234567 (index 0)
        int e = 0, l = 0;
        if (P[0][0] != 0 || P[0][6] != 6) { fprintf(stderr, "first word\n"); return 2; }
        for (; l < 6; l++) { used[cls[e]] = 1; pe[0] = 0; pl[0] = l + 1; node(e, 1, 5 - l); e = t2[e]; }
    }
    printf("%s caps %s holes %d..%d delta %d depth %d parts %llu part %llu long %d\n", argv[1], argv[2], LO, HI, delta, DEPTH, NPARTS, PART, LONG);
    printf("kept %llu tried %llu found %llu\n", kept, tried, found);
    if (ladder) {
        printf("Q:"); for (int i = LO; i <= HI; i++) printf(" %d", Q[i]);
        printf("\nR:"); for (int i = LO; i <= HI; i++) printf(" %d", R[i]);
        printf("\n");
    }
    printf("END\n");
    return 0;
}
