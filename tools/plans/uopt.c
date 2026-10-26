/* uopt.c - local search on an n = 14 unit plan (gen14.c), without the word.  The move shape is the block move of
   my n = 12 block search (relocation of a trail with re-opening of the trails around both places; William Echols's n = 12
   move and Theo H.'s "phase-placement coupling"), here on the units of the 2-lift of selection C.

   Cost of a plan = sum over joins of (h - overlap(E, S)), h = 11 (the rest of the length is fixed).
   Move: take one unit u (or a segment of up to SEG consecutive units) out and put it between two other units;
   the openings of the units next to both places and of the moved units are chosen again by an exact DP over a
   window (W units on each side are free; the units beyond are fixed).  Places are found through an index of the
   current last words (suffix of length q = QMIN..11) and first words (prefix) of all units.
   Accepted if the cost goes down (or stays equal with --eq P, probability P).

   usage: uopt SEL IN.uplan OUT.uplan [--time SEC] [--seed S] [--eq P] [--seg L] [--win W] [--qmin Q] [--places M]
   Writes OUT.uplan at every improvement of 1000 and at the end; prints the exact length. */
#define GEN14_NO_MAIN
#include "../../recipes/n14/gen14.c"

typedef struct { char k; int a, b; } Unit;
static Unit *U; static int NU;
static u64 pack11(const u8 *w) { u64 v = 0; for (int i = 0; i < 11; i++) v = v << 4 | w[i]; return v; }
/* all candidates of all units */
static u64 *CS, *CE; static u32 *CM; static u64 *coff;
static int ncand(int u) { return (int)(coff[u + 1] - coff[u]); }
static void build_cands(void) {
    coff = malloc(8 * (NU + 1)); u64 tot = 0;
    for (int u = 0; u < NU; u++) { coff[u] = tot; if (U[u].k == 'D') tot += 11; else { u32 a = w2start[U[u].a], m = w2start[U[u].a + 1] - a; for (u32 i = 0; i < m; i++) if (!w2ty[a + i]) tot += 2; } }
    coff[NU] = tot;
    CS = malloc(8 * tot); CE = malloc(8 * tot); CM = malloc(4 * tot);
    for (int u = 0; u < NU; u++) {
        u64 n = coff[u];
        if (U[u].k == 'D') {
            u8 y[11], r[11]; ins(y, sel[det[U[u].a]].x, 10, 10, U[u].b);
            for (int j = 0; j < 11; j++) { rot(r, y, 11, j); CS[n] = pack11(r); rot(r, y, 11, j - 1); CE[n] = pack11(r); CM[n] = j; n++; }
        } else {
            u32 a = w2start[U[u].a], m = w2start[U[u].a + 1] - a; u8 b[12], t[11];
            for (u32 i = 0; i < m; i++) {
                if (w2ty[a + i]) continue;
                unpack12(w2row[a + i], b);
                CS[n] = pack11(b); t[0] = b[11]; memcpy(t + 1, b, 10); CE[n] = pack11(t); CM[n] = i * 2; n++;
                CS[n] = pack11(b + 1); CE[n] = pack11(b); CM[n] = i * 2 + 1; n++;
            }
        }
    }
    fprintf(stderr, "candidates %llu\n", (unsigned long long)tot);
}
static inline int jc(u64 E, u64 S) {
    for (int q = 11; q >= 1; q--) if ((E & ((1ULL << (4 * q)) - 1)) == (S >> (4 * (11 - q)))) return 11 - q;
    return 11;
}

/* sequence: linked list over units, chosen candidate (global index) */
static int *nx, *pv; static u64 *cho; static int head, tailu;
static i64 total_cost(void) { i64 c = 0; for (int u = head; nx[u] >= 0; u = nx[u]) c += jc(CE[cho[u]], CS[cho[nx[u]]]); return c; }

/* ---------- small hash for the DP transitions */
#define LB 20
static u64 *lk; static u32 *lf, *li, *ls; static u32 lstamp = 0;
static inline u64 lh(u64 k) { k ^= k >> 29; k *= 0x9E3779B97F4A7C15ULL; return k >> (64 - LB); }
static void lput(u64 k, u32 f, u32 i) { u64 p = lh(k); for (;;) { if (ls[p] != lstamp) { ls[p] = lstamp; lk[p] = k; lf[p] = f; li[p] = i; return; } if (lk[p] == k) { if (f < lf[p]) { lf[p] = f; li[p] = i; } return; } p = (p + 1) & ((1u << LB) - 1); } }
static int lget(u64 k, u32 *f, u32 *i) { u64 p = lh(k); for (;;) { if (ls[p] != lstamp) return 0; if (lk[p] == k) { *f = lf[p]; *i = li[p]; return 1; } p = (p + 1) & ((1u << LB) - 1); } }

/* DP over a chain of units w[0..m-1]; w[0] fixed at candidate c0 (or free if c0 == ~0), w[m-1] fixed at cm (or free);
   returns min cost and the chosen candidates in out[] */
#define MAXW 26
static u32 *dpf[MAXW], *dpb[MAXW]; static size_t dpcap[MAXW];
static u32 dp_chain(const int *w, int m, u64 c0, u64 cm, u64 *out) {
    for (int s = 0; s < m; s++) {
        int u = w[s]; int n = (s == 0 && c0 != ~0ULL) || (s == m - 1 && cm != ~0ULL) ? 1 : ncand(u);
        if ((size_t)n > dpcap[s]) { dpcap[s] = n * 2; dpf[s] = realloc(dpf[s], 4 * dpcap[s]); dpb[s] = realloc(dpb[s], 4 * dpcap[s]); }
    }
#define CAND(s, c) ((s == 0 && c0 != ~0ULL) ? c0 : (s == m - 1 && cm != ~0ULL) ? cm : coff[w[s]] + (c))
#define NC(s) (((s == 0 && c0 != ~0ULL) || (s == m - 1 && cm != ~0ULL)) ? 1 : ncand(w[s]))
    for (int c = 0; c < NC(0); c++) dpf[0][c] = 0;
    for (int s = 1; s < m; s++) {
        int np = NC(s - 1), n = NC(s);
        if ((i64)np * n <= 4096) {
            for (int c = 0; c < n; c++) { u64 S = CS[CAND(s, c)]; u32 best = ~0u, bi = 0;
                for (int p = 0; p < np; p++) { u32 v = dpf[s - 1][p] + jc(CE[CAND(s - 1, p)], S); if (v < best) { best = v; bi = p; } }
                dpf[s][c] = best; dpb[s][c] = bi; }
        } else {
            lstamp++; u32 gmin = ~0u, gi = 0;
            for (int p = 0; p < np; p++) { u64 E = CE[CAND(s - 1, p)]; u32 f = dpf[s - 1][p]; if (f < gmin) { gmin = f; gi = p; }
                for (int q = 1; q <= 11; q++) lput((u64)q << 44 | (E & ((1ULL << (4 * q)) - 1)), f, p); }
            for (int c = 0; c < n; c++) { u64 S = CS[CAND(s, c)]; u32 best = gmin + 11, bi = gi, f, i;
                for (int q = 1; q <= 11; q++) if (lget((u64)q << 44 | (S >> (4 * (11 - q))), &f, &i) && f + 11 - q < best) { best = f + 11 - q; bi = i; }
                dpf[s][c] = best; dpb[s][c] = bi; }
        }
    }
    int n = NC(m - 1); u32 best = ~0u; int bc = 0;
    for (int c = 0; c < n; c++) if (dpf[m - 1][c] < best) { best = dpf[m - 1][c]; bc = c; }
    if (out) { int c = bc; for (int s = m - 1; s >= 0; s--) { out[s] = CAND(s, c); c = dpb[s][c]; } }
    return best;
#undef CAND
#undef NC
}

/* ---------- index of current last words and first words: key (q, word part) -> list of units (lazy, checked) */
#define IB 24
static u64 *ik; static u32 *ihead; static u32 *inext, *iunit; static u32 inn, icap;
static int QMIN = 7;
static void ix_clear(void) { memset(ihead, 0xff, 4ULL << IB); for (u64 p = 0; p < (1ULL << IB); p++) ik[p] = ~0ULL; inn = 0; }
static inline u64 ixh(u64 k) { k ^= k >> 31; k *= 0xD6E8FEB86659FD93ULL; return k >> (64 - IB); }
static void ix_add(u64 key, int u) {
    u64 p = ixh(key);
    while (ik[p] != ~0ULL && ik[p] != key) p = (p + 1) & ((1ULL << IB) - 1);
    if (ik[p] == ~0ULL) { ik[p] = key; }
    if (inn == icap) { icap = icap * 2 + 1024; inext = realloc(inext, 4ULL * icap); iunit = realloc(iunit, 4ULL * icap); }
    inext[inn] = ihead[p]; iunit[inn] = u; ihead[p] = inn++;
}
static u32 ix_first(u64 key) { u64 p = ixh(key); while (ik[p] != ~0ULL) { if (ik[p] == key) return ihead[p]; p = (p + 1) & ((1ULL << IB) - 1); } return ~0u; }
/* key: bit 63 = first-word index, bits 48.. = q, low bits = word part */
static void ix_unit(int u) {
    u64 E = CE[cho[u]], S = CS[cho[u]];
    for (int q = QMIN; q <= 11; q++) {
        ix_add((u64)q << 48 | (E & ((1ULL << (4 * q)) - 1)), u);
        ix_add(1ULL << 63 | (u64)q << 48 | (S >> (4 * (11 - q))), u);
    }
}
static void ix_build(void) { ix_clear(); for (int u = head; u >= 0; u = nx[u]) ix_unit(u); }

/* same group: small units of one loop, or walk units of one W1 group (one n = 13 walk chain) */
static int samegrp(int a, int b) {
    if (U[a].k != U[b].k) return 0;
    if (U[a].k == 'D') return U[a].a == U[b].a;
    return w2walk[U[a].a] == w2walk[U[b].a] && w2a[U[a].a] == w2a[U[b].a];
}
static u64 rng = 88172645463325252ULL;
static inline u64 xr(void) { rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17; return rng; }

static void write_plan(const char *path, const char *note) {
    char tmp[1024]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *o = fopen(tmp, "w"); if (!o) DIE("cannot write %s", tmp);
    fprintf(o, "N14-UNITPLAN 1\n# %s\n", note);
    for (int u = head; u >= 0; u = nx[u]) {
        u32 m = CM[cho[u]];
        if (U[u].k == 'D') fprintf(o, "D %d %d %u\n", U[u].a, U[u].b, m); else fprintf(o, "W %d %u %u\n", U[u].a, m >> 1, m & 1);
    }
    fclose(o); remove(path); rename(tmp, path);
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: uopt SEL IN.uplan OUT.uplan [--time SEC] [--seed S] [--eq P] [--seg L] [--win W] [--qmin Q] [--places M]\n"); return 2; }
    double tlim = 600, peq = 0; int SEG = 1, WIN = 1, PLACES = 24, BLOCK = 0; u64 seed = 1;
    for (int i = 4; i < argc; i++) {
        if (!strcmp(argv[i], "--time")) tlim = atof(argv[++i]);
        else if (!strcmp(argv[i], "--seed")) seed = strtoull(argv[++i], NULL, 10);
        else if (!strcmp(argv[i], "--eq")) peq = atof(argv[++i]);
        else if (!strcmp(argv[i], "--seg")) SEG = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--win")) WIN = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--qmin")) QMIN = atoi(argv[++i]);
        else if (!strcmp(argv[i], "--places")) { PLACES = atoi(argv[++i]); if (PLACES > 32) PLACES = 32; }
        else if (!strcmp(argv[i], "--block")) BLOCK = 1;
        else DIE("unknown option %s", argv[i]);
    }
    if (SEG < 1 || SEG > 4 || WIN < 1 || WIN > 3) DIE("seg 1..4, win 1..3");
    rng ^= seed * 0x9E3779B97F4A7C15ULL; for (int i = 0; i < 10; i++) xr();
    double t0 = wall();
    read_sel(argv[1]); build_w2();
    U = malloc(sizeof(Unit) * 80000); NU = 0;
    u32 *m0 = malloc(4 * 80000);
    FILE *f = fopen(argv[2], "r"); if (!f) DIE("cannot open %s", argv[2]);
    char line[512];
    while (fgets(line, sizeof line, f)) {
        char k; int a, b, c;
        if (line[0] == '#' || !strncmp(line, "N14", 3)) continue;
        if (sscanf(line, " %c %d %d %d", &k, &a, &b, &c) < 4) continue;
        U[NU].k = k; U[NU].a = a; U[NU].b = (k == 'D') ? b : 0;
        m0[NU] = (k == 'D') ? (u32)c : (u32)(b * 2 + c); NU++;
    }
    fclose(f);
    build_cands();
    nx = malloc(4 * NU); pv = malloc(4 * NU); cho = malloc(8 * NU);
    long nS = 0, nW = 0;
    for (int u = 0; u < NU; u++) {
        nx[u] = u + 1 < NU ? u + 1 : -1; pv[u] = u - 1;
        u64 c; for (c = coff[u]; c < coff[u + 1]; c++) if (CM[c] == m0[u]) break;
        if (c == coff[u + 1]) DIE("unit %d: opening not found", u);
        cho[u] = c; if (U[u].k == 'D') nS++; else nW++;
    }
    head = 0; tailu = NU - 1;
    u64 sumR = 87178291200ULL + 6227020800ULL + 479001600ULL + 19588800ULL, base = sumR + 11 + 10 * nS + 11 * nW;
    i64 cost = total_cost();
    fprintf(stderr, "units %d, cost %lld, length %llu (%.0fs)\n", NU, cost, (unsigned long long)(base + cost), wall() - t0);
    lk = malloc(8ULL << LB); lf = malloc(4ULL << LB); li = malloc(4ULL << LB); ls = calloc(1ULL << LB, 4);
    ik = malloc(8ULL << IB); ihead = malloc(4ULL << IB);
    ix_build();
    i64 start_cost = cost, last_write = cost; long tried = 0, acc = 0, eqacc = 0; double lastrep = wall();
    int *perm = malloc(4 * NU); for (int i = 0; i < NU; i++) perm[i] = i;
    int pass = 0;
    char note[512];
    while (wall() - t0 < tlim) {
        for (int i = NU - 1; i > 0; i--) { int j = (int)(xr() % (i + 1)); int t = perm[i]; perm[i] = perm[j]; perm[j] = t; }
        long acc_pass = 0;
        for (int pi = 0; pi < NU && wall() - t0 < tlim; pi++) {
            int u0 = perm[pi]; int L = 1 + (int)(xr() % SEG);
            if (BLOCK) { while (pv[u0] >= 0 && samegrp(pv[u0], u0)) u0 = pv[u0]; L = 1; for (int v = nx[u0]; v >= 0 && samegrp(u0, v) && L < 16; v = nx[v]) L++; if (L < 2 && !(xr() % 4 == 0)) continue; }
            /* segment u0 .. u1 of L units */
            int seg[16]; seg[0] = u0; int ok = 1;
            for (int s = 1; s < L; s++) { int v = nx[seg[s - 1]]; if (v < 0) { ok = 0; break; } seg[s] = v; }
            if (!ok) continue;
            int u1 = seg[L - 1];
            /* removal window: WIN free units on each side; fixed beyond */
            int left[4], right[4], nl = 0, nr = 0, x = pv[u0];
            while (x >= 0 && nl < WIN + 1) { left[nl++] = x; x = pv[x]; }
            x = nx[u1]; while (x >= 0 && nr < WIN + 1) { right[nr++] = x; x = nx[x]; }
            /* current cost of the stretch left[nl-1] .. right[nr-1] */
            int win[MAXW]; int m = 0;
            for (int s = nl - 1; s >= 0; s--) win[m++] = left[s];
            for (int s = 0; s < L; s++) win[m++] = seg[s];
            for (int s = 0; s < nr; s++) win[m++] = right[s];
            i64 curA = 0; for (int s = 0; s + 1 < m; s++) curA += jc(CE[cho[win[s]]], CS[cho[win[s + 1]]]);
            /* after removal */
            int wr[MAXW]; int mr = 0; for (int s = nl - 1; s >= 0; s--) wr[mr++] = left[s]; for (int s = 0; s < nr; s++) wr[mr++] = right[s];
            u64 outR[MAXW]; i64 newA;
            if (mr == 0) newA = 0;
            else {
                u64 c0 = (nl == WIN + 1) ? cho[wr[0]] : ~0ULL, cm = (nr == WIN + 1) ? cho[wr[mr - 1]] : ~0ULL;
                if (mr == 1) { c0 = cho[wr[0]]; cm = ~0ULL; }
                newA = dp_chain(wr, mr, c0, cm, outR);
            }
            i64 gainA = curA - newA;            /* positive = removal saves */
            /* places: units a whose last word matches a first word of the segment's first unit, or units b whose first
               word matches a last word of the segment's last unit */
            int places[64]; int np = 0;
            u64 c0a = coff[u0], c1a = coff[u0 + 1];
            u64 step = (c1a - c0a) > 64 ? (c1a - c0a) / 64 : 1;
            for (int q = 11; q >= QMIN && np < PLACES; q--) {
                for (u64 c = c0a + (xr() % step); c < c1a && np < PLACES; c += step) {
                    u64 key = (u64)q << 48 | (CS[c] >> (4 * (11 - q)));
                    for (u32 e = ix_first(key); e != ~0u && np < PLACES; e = inext[e]) {
                        int a = iunit[e];
                        if ((CE[cho[a]] & ((1ULL << (4 * q)) - 1)) != (CS[c] >> (4 * (11 - q)))) continue;
                        int bad = 0; for (int s = 0; s < m; s++) if (win[s] == a) bad = 1;
                        if (nx[a] >= 0) for (int s = 0; s < m; s++) if (win[s] == nx[a]) bad = 1;
                        for (int t = 0; t < np; t++) if (places[t] == a) bad = 1;
                        if (!bad) places[np++] = a;
                    }
                }
            }
            u64 c0b = coff[u1], c1b = coff[u1 + 1]; step = (c1b - c0b) > 64 ? (c1b - c0b) / 64 : 1;
            for (int q = 11; q >= QMIN && np < 2 * PLACES; q--) {
                for (u64 c = c0b + (xr() % step); c < c1b && np < 2 * PLACES; c += step) {
                    u64 key = 1ULL << 63 | (u64)q << 48 | (CE[c] & ((1ULL << (4 * q)) - 1));
                    for (u32 e = ix_first(key); e != ~0u && np < 2 * PLACES; e = inext[e]) {
                        int b = iunit[e]; if (pv[b] < 0) continue;
                        if ((CS[cho[b]] >> (4 * (11 - q))) != (CE[c] & ((1ULL << (4 * q)) - 1))) continue;
                        int a = pv[b];
                        int bad = 0; for (int s = 0; s < m; s++) if (win[s] == a || win[s] == b) bad = 1;
                        for (int t = 0; t < np; t++) if (places[t] == a) bad = 1;
                        if (!bad) places[np++] = a;
                    }
                }
            }
            /* evaluate each place exactly */
            i64 bestd = 1; int besta = -1; u64 bestout[MAXW]; int bestw[MAXW], bestm = 0;
            for (int t = 0; t < np; t++) {
                int a = places[t];
                int L2[4], R2[4], nl2 = 0, nr2 = 0; x = a;
                while (x >= 0 && nl2 < WIN + 1) { L2[nl2++] = x; x = pv[x]; }
                x = nx[a]; while (x >= 0 && nr2 < WIN + 1) { R2[nr2++] = x; x = nx[x]; }
                int w2[MAXW], m2 = 0, bad = 0;
                for (int s = nl2 - 1; s >= 0; s--) w2[m2++] = L2[s];
                for (int s = 0; s < nr2; s++) w2[m2++] = R2[s];
                for (int s = 0; s < m2; s++) for (int r = 0; r < m; r++) if (w2[s] == win[r]) bad = 1;
                if (bad) continue;
                i64 curB = 0; for (int s = 0; s + 1 < m2; s++) curB += jc(CE[cho[w2[s]]], CS[cho[w2[s + 1]]]);
                int w3[MAXW], m3 = 0; for (int s = nl2 - 1; s >= 0; s--) w3[m3++] = L2[s]; for (int s = 0; s < L; s++) w3[m3++] = seg[s]; for (int s = 0; s < nr2; s++) w3[m3++] = R2[s];
                u64 c0 = (nl2 == WIN + 1) ? cho[w3[0]] : ~0ULL, cm = (nr2 == WIN + 1) ? cho[w3[m3 - 1]] : ~0ULL;
                u64 out3[MAXW]; i64 newB = dp_chain(w3, m3, c0, cm, out3);
                i64 d = (newB - curB) - gainA;
                if (d < bestd) { bestd = d; besta = a; memcpy(bestout, out3, sizeof out3); memcpy(bestw, w3, sizeof w3); bestm = m3; }
            }
            tried++;
            if (besta < 0) continue;
            if (bestd > 0 || (bestd == 0 && (peq <= 0 || (double)(xr() % 1000000) / 1e6 >= peq))) continue;
            /* apply: remove segment */
            int p = pv[u0], n = nx[u1];
            if (p >= 0) nx[p] = n; else head = n;
            if (n >= 0) pv[n] = p; else tailu = p;
            for (int s = 0; s < mr; s++) { cho[wr[s]] = outR[s]; }
            /* insert after besta */
            int b = nx[besta];
            nx[besta] = u0; pv[u0] = besta; nx[u1] = b; if (b >= 0) pv[b] = u1; else tailu = u1;
            for (int s = 0; s < bestm; s++) cho[bestw[s]] = bestout[s];
            for (int s = 0; s < mr; s++) ix_unit(wr[s]);
            for (int s = 0; s < bestm; s++) ix_unit(bestw[s]);
            cost += bestd; acc++; acc_pass++; if (bestd == 0) eqacc++;
            if (wall() - lastrep > 60) {
                fprintf(stderr, "  pass %d: tried %ld, accepted %ld (equal %ld), cost %lld, length %llu (%.0fs)\n", pass, tried, acc, eqacc, cost, (unsigned long long)(base + cost), wall() - t0);
                lastrep = wall();
            }
            if (last_write - cost >= 1000) { snprintf(note, sizeof note, "uopt from %s, length %llu", argv[2], (unsigned long long)(base + cost)); write_plan(argv[3], note); last_write = cost; }
            if (inn > 200000000u) ix_build();
        }
        pass++;
        i64 chk = total_cost();
        if (chk != cost) DIE("cost bookkeeping %lld != %lld", cost, chk);
        fprintf(stderr, "pass %d done: accepted %ld in this pass, cost %lld, length %llu (%.0fs)\n", pass, acc_pass, cost, (unsigned long long)(base + cost), wall() - t0);
        ix_build();
        if (acc_pass == 0 && peq <= 0) break;
    }
    snprintf(note, sizeof note, "uopt from %s (seg %d, win %d, qmin %d, seed %llu), length %llu", argv[2], SEG, WIN, QMIN, (unsigned long long)seed, (unsigned long long)(base + cost));
    write_plan(argv[3], note);
    fprintf(stderr, "start cost %lld, end cost %lld; LENGTH %llu (Echols 93904936032, difference %lld) (%.0fs)\n",
            start_cost, cost, (unsigned long long)(base + cost), (long long)(base + cost) - 93904936032LL, wall() - t0);
    return 0;
}
