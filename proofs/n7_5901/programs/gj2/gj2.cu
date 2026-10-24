/* gj.cu (agent n7-gpuj, 2026-10-11): the JOINT search of programs/jr/jr.c (= jt.c of defect 15, not in this repository, with the cut on one
 * piece, PREV, and the order rule, ORD) on the card.  Design of gk4.cu (the first layout of programs/gk4/gk5.cu): one thread = one depth-first walk,
 * one uniform step, class state in shared memory, a split kernel between the rounds.
 * Frames: a NODE (prefix of a piece; lo = mask of the untried successors) or a START frame (lo = counter over the start
 *   vertices of a piece; or, as a task of the host's gate, one explicit row).  A node whose piece is complete has "jump
 *   pending" (jp) and becomes the parent of the start frame of the next piece.
 *   a = lo (32: cm | kn (13) + kend << 13) | x << 32 (13: end vertex | current start vertex) | len2 << 45 (3) | l2 << 48 (3)
 *       | j << 51 (5) | dm << 56 (6: which classes of the current row are shared) | jp << 62 | start << 63
 *   b = pm (14; ring: start vertex of the ring) | pM << 14 (14) | km3 << 28 (3) | r << 32 (8) | d << 40 (7) | t << 47 (4)
 *       | recmax << 51 (8) | dups << 59 (2) | km4 << 61 (3);  km = number of hole counts 0 .. km - 1 of a next row that
 *       can lead to a kept or completed node (light, heavy link); 7 = not computed yet (tasks).
 * A step: (start the next piece if jp) + (pop if exhausted) + (take up to NR rows until one has an admissible length) +
 *   (judge one length: the rule of jr.c) + (push if kept or complete).
 * Class state: 2 bits per class in shared memory (bit 0: used by some piece, bit 1: used by this piece); at a jump the
 *   bits 1 are saved to CSV and cleared, at the return restored.  dups = shared classes so far (at most B).
 * Vertices are numbered (orbit of the row rotation) * 8 + position, so the end vertex of a row is arithmetic (XN).
 * Per piece (12 bits of pcw): ring 1 | pS << 1 (4) | ordsk << 5 | isrp << 6 | last << 7 | ring ordinal << 8 (2).
 * Tables: ROWC2[x * 32 + j] = (classes of the row that starts at successor j of x, 10 bits each; its start vertex),
 *   ROWC2[NVD * 32 + v] the same for the row that starts at v;  SUCCC[x * 6 + q / 6] = start classes of the successors;
 *   MT[(ip * 10 + tl) * 128 + bl] (sequence node with tl heavy links and weight bl left): a = 6 thresholds (light link,
 *   k holes: admissible iff value needed + 40 <= byte) | G3 << 48 | G4 << 56,  b = 6 thresholds (heavy) | B1 << 48 |
 *   B2 << 56 (bytes: value + 60; 0 = minus infinity, 255 = plus infinity);  TB = B1 as 16 bits (ring completion);
 *   RV[(tl * NN2 + need + NOFF2) * 128 + bl] = CN1 | A2P << 16 | CN1h << 32 | A2Ph << 48 (the cut, jr.c rev_light/heavy);
 *   RK6[ring * krw + (b * 200 + r) * 128 + d] = 6 thresholds for the children | own keep byte << 56 (1 + largest value
 *   needed for which the ring prefix is kept);  KR the keep bytes alone (host only);  L3[q * lw + v / 32] bit v % 32 = v
 *   is a weight-3 successor of q (ring closure);  VMAP = device number of vertex v (start vertices under PART2).
 * The thresholds only prefilter (a superset); kept, completed and found are decided by the rule itself, as in jr.c.
 * build: build_ptx.bat gj.cu gj7.ptx 6   (LL = 6 for 7 symbols; BT = 128 threads per block, NR = 2; FC > 0 = the last FC
 *   frames in shared memory, measured slower)
 */
typedef unsigned long long u64;
typedef unsigned int u32;
#ifndef LL
#define LL 6
#endif
#define C5 (LL - 1)
#define C6 LL
#define STK 192
#define UW 45
#ifndef BT
#define BT 128
#endif
#ifndef NR
#define NR 2
#endif
#define SMX 10
#define RMX 200
#define NOFF2 168
#define NN2 428
#define MAXSV 4
#ifndef FC
#define FC 0
#endif
#ifndef SC
#define SC 3      /* 16-byte words of successor classes per vertex: 3 (36 slots); 2 would need at most 24 successors, 7 symbols have 28 */
#endif
#ifndef RC
#define RC 0      /* 1: the parent frame and its row stay in registers */
#endif
#if FC
#define PUSHF() do { V2 w_; w_.a = PACKA(); w_.b = PACKB(); if (top - clo == FC) { sk[clo] = fc[(clo & (FC - 1)) * BT + tid]; clo++; } fc[(top & (FC - 1)) * BT + tid] = w_; } while (0)
#define POPF(w) do { if (top >= clo) w = fc[(top & (FC - 1)) * BT + tid]; else { w = sk[top]; clo = top; } } while (0)
#define FLUSHF() do { for (int g_ = clo; g_ < top; g_++) sk[g_] = fc[(g_ & (FC - 1)) * BT + tid]; } while (0)
#elif RC
#define PUSHF() do { if (pv_) sk[top - 1] = pc_; pc_.a = PACKA(); pc_.b = PACKB(); prc_ = rc; prs_ = rs; prk_ = rok; pv_ = 1; } while (0)
#define FLUSHF() do { if (pv_) sk[top - 1] = pc_; } while (0)
#else
#define PUSHF() do { V2 w_; w_.a = PACKA(); w_.b = PACKB(); sk[top] = w_; } while (0)
#define POPF(w) w = sk[top]
#define FLUSHF()
#endif
#if RC
#define POPU() do { if (pv_) { UNPACKN(pc_); rc = prc_; rs = prs_; rok = prk_; pv_ = 0; } else { V2 w = sk[top]; UNPACK(w); } } while (0)
#else
#define POPU() do { V2 w; POPF(w); UNPACK(w); } while (0)
#endif
#define NFND 16
#ifndef LEARN
#define LEARN 1
#endif
#ifndef EXH
#define EXH 1
#endif
#ifndef ORB
#define ORB 1
#endif
#ifndef NRS
#define NRS NR     /* rows scanned per step at most at a start frame */
#endif
#ifndef ROT
#define ROT 1      /* the row of the next start vertex of the same orbit = the row in the registers, rotated: no load */
#endif
struct __align__(16) V2 { u64 a, b; };
#define SVAL(c) ((sh[((c) >> 4) * BT + tid] >> (2 * ((c) & 15))) & 3u)
#define SSET(c) (sh[((c) >> 4) * BT + tid] |= 3u << (2 * ((c) & 15)))
#define SCLR(c, m) (sh[((c) >> 4) * BT + tid] &= ~((u32)(m) << (2 * ((c) & 15))))

#define UNPACKN(w) do { lo = (u32)(w).a; x = (int)((w).a >> 32) & 0x1fff; len2 = (int)((w).a >> 45) & 7; l2 = (int)((w).a >> 48) & 7; j = (int)((w).a >> 51) & 31; \
    dm = (u32)((w).a >> 56) & 63; jp = (u32)((w).a >> 62) & 1; start = (u32)((w).a >> 63); pm = ((int)((w).b & 0x3fff) << 18) >> 18; pM = ((int)(((w).b >> 14) & 0x3fff) << 18) >> 18; \
    r = (int)((w).b >> 32) & 255; d = (int)((w).b >> 40) & 127; t = (int)((w).b >> 47) & 15; rcm = (int)(signed char)(((w).b >> 51) & 255); dups = ((int)((w).b >> 59) & 3) | (((int)((w).b >> 31) & 1) << 2); mk3 = (1u << (((w).b >> 28) & 7)) - 1; mk4 = (1u << (((w).b >> 61) & 7)) - 1; \
    type = j >= n3; rid = start ? NVD * 32 + x : x * 32 + j; } while (0)
#define UNPACK(w) do { UNPACKN(w); rok = 1; { const V2 rr_ = ROWC2[rid]; rc = rr_.a; rs = (int)rr_.b; } } while (0)
#define XN(l) ((rs & ~7) | ((((rs & 7) + (l) - 1) >= LL) ? ((rs & 7) + (l) - 1 - LL) : ((rs & 7) + (l) - 1)))
#define PACKA() ((u64)lo | ((u64)x << 32) | ((u64)len2 << 45) | ((u64)l2 << 48) | ((u64)j << 51) | ((u64)dm << 56) | ((u64)jp << 62) | ((u64)start << 63))
#define PACKB() ((u64)(pm & 0x3fff) | ((u64)(pM & 0x3fff) << 14) | ((u64)__popc(mk3) << 28) | ((u64)__popc(mk4) << 61) | ((u64)r << 32) | ((u64)d << 40) | ((u64)t << 47) | ((u64)(rcm & 0xff) << 51) | ((u64)(dups & 3) << 59) | ((u64)(dups >> 2) << 31))
#define PINFO() do { pin = (u32)(pcw >> (12 * ip)) & 4095; ring = pin & 1; pS = (int)(pin >> 1) & 15; ordsk = (pin >> 5) & 1; isrp = (pin >> 6) & 1; last = (pin >> 7) & 1; rord = (int)(pin >> 8) & 3; ords = (pin >> 10) & 1; } while (0)
#define GE7(E, q) ((u32)(((((((E) | 0x8080808080808080ull) - (u64)(q) * 0x0101010101010101ull) & 0x8080808080808080ull) >> 7) * 0x0102040810204080ull) >> 56) & ((1u << LL) - 1))
#define GETMASK() do { if (ring) { const u64 e_ = RK6[(size_t)rord * krw + (b * RMX + r) * 128 + d]; int q_ = (a > 0 ? a : 0) + 1; if (q_ > 127) q_ = 127; mk3 = GE7(e_, q_); mk4 = 0; }     else { int q_ = a - (r - d - C5 * t) + 40; q_ = q_ < 1 ? 1 : (q_ > 127 ? 127 : q_); const V2 e_ = MT[((ip * SMX + pS - t) << 7) + b - d - C6 * t]; mk3 = GE7(e_.a, q_); mk4 = GE7(e_.b, q_); } } while (0)
#define REM() ((type ? mk4 : mk3) & ((1u << (LL - l2)) - 1) & ~((1u << (LL - len2)) - 1))
#define GETCTX() do { int c_ = CTX[8 * i + ip]; a = (int)(short)(c_ & 0xffff); b = (c_ >> 16) & 255; pv = (int)(signed char)((c_ >> 24) & 255); } while (0)

static __device__ __forceinline__ u32 avail6(u64 w, int q0, int jlo, int jhi, const u32 *sh, int tid, u32 dok) {
    u32 av = 0;
    for (int p = 0; p < 6; p++) { const int q = q0 + p; const u32 c = (u32)(w >> (10 * p)) & 1023; const u32 sv = SVAL(c); const u32 fr = ((sv >> 1) ^ 1u) & ((sv ^ 1u) | dok) & 1u; if (q >= jlo && q < jhi) av |= fr << q; }
    return av;
}

extern "C" __global__ void gj_run(const V2 *ROWC2, const V2 *SUCCC, const unsigned short *VMAP, const u64 *TB, const u64 *RV,
                                  const unsigned char *KR, const u32 *L3, const V2 *MT, const u64 *RK6, u32 *USED, u32 *CSV, int *HDR, int *CTX, u64 *CNT,
                                  V2 *STKM, u64 *CTL, V2 *FND,
                                  int N, int K, int n3, int ns, int NPv, int Bmax, u64 pcw, int flags, int PA, int PB, int PH,
                                  int RLO, int RHI, int p2, int np2, int lw, int krw)
{
    __shared__ u32 sh[UW * BT];
#if FC
    __shared__ V2 fc[FC * BT];
#endif
    const int tid = threadIdx.x;
    const int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;
    int *h = HDR + 8 * i;
    if (h[0] == 0) return;
    if (blockDim.x != BT) { CTL[3] = 3; return; }
    u32 *ug = USED + (size_t)UW * i;
    for (int w = 0; w < UW; w++) sh[w * BT + tid] = ug[w];
    V2 *sk = STKM + (size_t)i * STK;
    u64 *cn = CNT + 16 * (size_t)i;
    int top = h[1], ip = h[3];
    const int base = h[2];
    const u32 nocut = flags & 1, rev = (flags >> 1) & 1;
    const int n4 = ns - n3, NVD = (NPv / LL) * 8;
    int a, b, pv; GETCTX();
    u32 pin, ring, ordsk, isrp, last, ords; int pS, rord; PINFO();
    u32 lo, dm, jp, start; int x, len2, l2, j, pm, pM, r, d, t, rcm, dups, type, rid, rs = 0; u64 rc;
    u32 mk3, mk4, rok = 1;
    const u32 orbok0 = (np2 <= 1);
#define orbok (orbok0 | (u32)(ip != 1))
    { V2 w = sk[top]; UNPACK(w); }
    if (mk3 == 127u) GETMASK();
    int clo = top; V2 pc_; u64 prc_ = 0; int prs_ = 0; u32 pv_ = 0, prk_ = 0; pc_.a = 0; pc_.b = 0;
    u64 kept = 0, tries = 0; u32 nodes = 0, found = 0;
    int it, alive = 1;
    for (it = 0; it < K; it++) {
        if (jp) {                                                           /* the piece is complete: start the next one */
            jp = 0;
            PUSHF();
            cn[2 * ip] += kept; cn[2 * ip + 1] += tries; kept = 0; tries = 0;
            u32 *cs = CSV + ((size_t)i * MAXSV + ip) * UW;
            for (int w = 0; w < UW; w++) { const u32 v_ = sh[w * BT + tid]; cs[w] = v_ & 0xAAAAAAAAu; sh[w * BT + tid] = v_ & 0x55555555u; }
            const int val = ring ? r - d : r - d - C5 * t, wt = ring ? d : d + C6 * t;
            a -= val; b -= wt; pv = val; ip++;
            CTX[8 * i + ip] = (a & 0xffff) | (b << 16) | ((pv & 0xff) << 24);
            PINFO();
            top++;
            if (top >= STK - 1) { CTL[3] = 1; alive = 0; break; }
            const int cnt = (ip == 1) ? (NPv - p2 + np2 - 1) / np2 : NPv;
            const int k0 = ords ? (pm >> 3) * LL + (pm & 7) : 0;      /* ORDS: this ring starts at or after the start vertex of the ring before it */
            lo = ((u32)cnt << 13) | (u32)k0; x = 0; len2 = 0; l2 = 0; j = 0; dm = 0; start = 1;
            pm = 0; pM = 0; r = 0; d = 0; t = 0; rcm = -128; type = 0; rc = 0; rid = 0; rok = 0;
            tries += (u64)(cnt - k0);
            GETMASK();
            continue;
        }
        u32 more = start ? ((lo & 0x1fff) < (lo >> 13)) : (lo != 0);
        u32 rem = REM();
        if (!rem && !more) {                                          /* exhausted: back to the parent */
            if (top == base) { alive = 0; it++; break; }
            const u32 ws = start & (r == 0);                               /* a real start frame: the piece ends */
            top--;
            POPU();
            if (ws) {
                cn[2 * ip] += kept; cn[2 * ip + 1] += tries; kept = 0; tries = 0;
                ip--; GETCTX(); PINFO();
                const u32 *cs = CSV + ((size_t)i * MAXSV + ip) * UW;
                for (int w = 0; w < UW; w++) sh[w * BT + tid] |= cs[w];
            } else {
                for (int q = 0; q < l2; q++) { const u32 c = (u32)(rc >> (10 * q)) & 1023; SCLR(c, 3u - ((dm >> q) & 1u)); }
            }
            rem = REM();
            more = start ? ((lo & 0x1fff) < (lo >> 13)) : (lo != 0);
        }
        if (!rem) {                                                   /* the next row (up to NR rows in one step) */
            if (!more) continue;
            for (int nr = 0; ; ) {
                u32 rot_ = 0;
                if (start) { const int k = (int)(lo & 0x1fff), xo_ = x; lo++; x = (ip == 1 && np2 > 1) ? (int)VMAP[p2 + k * np2] : (k / LL) * 8 + k % LL; rid = NVD * 32 + x;
                    rot_ = (u32)ROT & rok & (u32)(x == xo_ + 1) & (u32)((x & 7) != 0) & (u32)(r == 0); }
                else { j = __ffs((int)lo) - 1; lo &= lo - 1; rid = x * 32 + j; }
                type = j >= n3;
                if (rot_) { rc = ((rc >> 10) | (rc << (10 * LL - 10))) & ((1ull << (10 * LL)) - 1); rs = x; }
                else { const V2 rr_ = ROWC2[rid]; rc = rr_.a; rs = (int)rr_.b; rok = 1; }
                len2 = 0; dm = 0;
                { u32 ok = 1; int dc = dups;
                  for (int q = 0; q < LL; q++) { const u32 c = (u32)(rc >> (10 * q)) & 1023; const u32 sv = SVAL(c); const u32 inc = sv >> 1, inu = sv & 1u;
                      ok &= (inc ^ 1u) & ((inu ^ 1u) | (u32)(dc < Bmax)); const u32 dq = ok & inu; dm |= dq << q; dc += (int)dq; len2 += (int)ok; } }
                l2 = 0;
#if ORB
                if (start && orbok && len2 < LL && mk3 == 1u && r == 0) {      /* only a full row can be kept: the other rows of this orbit have the same classes */
                    const int k_ = (int)(lo & 0x1fff) - 1, ke_ = (int)(lo >> 13); int nk_ = k_ + LL - k_ % LL; if (nk_ > ke_) nk_ = ke_;
                    lo = (lo & ~0x1fffu) | (u32)nk_;
                }
#endif
                rem = REM();
                if (rem || ++nr >= (start ? NRS : NR)) break;
                more = start ? ((lo & 0x1fff) < (lo >> 13)) : (lo != 0);
                if (!more) break;
            }
            if (!rem) { len2 = 0; continue; }
            len2 = LL - (__ffs((int)rem) - 1); l2 = LL - 1 - (31 - __clz((int)rem));
        }
        const int l = LL - (31 - __clz((int)rem)); l2 = l;
        nodes++;
        const int t2 = t + type, d2 = d + LL - l, r2 = r + 1;
        u32 k3 = 0, k4 = 0, cp = 0, cmk3 = 0, cmk4 = 0, vi = 1;
        int pm2 = pm, pM2 = pM, val;
        if (ring) {
            val = r2 - d2;
            const int bl = b - d2;
            const int s0 = (start && r == 0) ? x : pm;
            pm2 = s0;
            if (r2 >= 2 && d2 >= RLO && d2 <= RHI) {
                const int xn = XN(l);
                if ((L3[(size_t)xn * lw + (s0 >> 5)] >> (s0 & 31)) & 1) {
                    const int B1 = (int)(short)((TB[((ip * SMX) << 7) + bl] >> 32) & 0xffff);
                    cp = (!ordsk || val <= pv) && (val + B1 >= a);
                }
            }
            { const u64 e_ = RK6[(size_t)rord * krw + (b * RMX + r2) * 128 + d2]; int q_ = (a > 0 ? a : 0) + 1; if (q_ > 127) q_ = 127;
              k3 = (r2 < RMX) && ((int)(e_ >> 56) >= q_); cmk3 = GE7(e_, q_); }
            vi = k3 | (u32)(r2 >= 2 && d2 >= RLO && d2 <= RHI && (!ordsk || val <= pv));
        } else {
            val = r2 - d2 - C5 * t2;
            const int wt = d2 + C6 * t2, bl = b - wt, need = a - val, tl = pS - t2;
            const V2 E = MT[((ip * SMX + tl) << 7) + bl];
            const int g3 = (int)((E.a >> 48) & 255), g4 = (int)(E.a >> 56), b1 = (int)((E.b >> 48) & 255), b2 = (int)(E.b >> 56);
            const u32 rec = (u32)(val > rcm) | nocut;
            cp = rec & (u32)(!ordsk || val <= pv) & ((u32)(b2 == 255) | ((u32)(b2 != 0) & (u32)(val + b2 - 60 >= need)))
                 & ((u32)(b1 == 255) | ((u32)(b1 != 0) & (u32)(val + b1 - 60 >= a)));
            k3 = ((u32)(val >= 1) | nocut) & ((u32)(g3 == 255) | ((u32)(g3 != 0) & (u32)(val + g3 - 60 >= a))) & (u32)(r2 < RMX - 1);
            k4 = ((u32)(val - C5 >= 1) | nocut) & ((u32)(g4 == 255) | ((u32)(g4 != 0) & (u32)(val - C5 + g4 - 60 >= a))) & (u32)(r2 < RMX - 1);
            { int q_ = need + 40; q_ = q_ < 1 ? 1 : (q_ > 127 ? 127 : q_); cmk3 = GE7(E.a, q_); cmk4 = GE7(E.b, q_); }
            if (rev && isrp) {
                const int fpar = PA * r - PB * d - 2 * PH * t - (type ? PH : 0);
                if (fpar < pm2) pm2 = fpar;
                if (fpar > pM2) pM2 = fpar;
                const int f = PA * r2 - PB * d2 - 2 * PH * t2;
                const int m = pm2 < f ? pm2 : f, M = pM2 > f ? pM2 : f;
                cp &= (u32)(m + M - f >= 0);
                const int n = need + NOFF2;
                if (n >= 0 && (k3 | k4)) {
                    const u64 Rv = RV[((size_t)(tl * NN2 + n) << 7) + bl];
                    if (m < 0) k3 &= (u32)(M + m - f >= (int)(short)(Rv & 0xffff)) | (u32)(m >= (int)(short)((Rv >> 16) & 0xffff));
                    const int fh = f - PH, mh = pm2 < fh ? pm2 : fh, Mh = pM2 > fh ? pM2 : fh;
                    if (mh < 0) k4 &= (u32)(Mh + mh - f >= (int)(short)((Rv >> 32) & 0xffff)) | (u32)(mh >= (int)(short)((Rv >> 48) & 0xffff));
                }
            }
        }
        if (!ring) vi = k3 | k4 | cp;
#if LEARN
        if (!vi) {                                  /* no row of this frame with this link kind and this length can be kept or complete */
            const int kk_ = LL - l;
            if (type) { if ((mk4 >> kk_) == 1u) mk4 >>= 1; } else if ((mk3 >> kk_) == 1u) mk3 >>= 1;
#if EXH
            if (!(type ? mk4 : mk3)) { if (start) lo = (lo >> 13) * 0x2001u; else if (type) lo &= (1u << n3) - 1; else lo &= ~((1u << n3) - 1); }
#endif
            continue;
        }
#endif
        if (last && cp) {                                                   /* an object: count it, write the first ones out */
            found++;
            const u64 slot = atomicAdd(CTL + 5, 1ull);
            if (slot < NFND) {
                V2 *fo = FND + slot * (STK + 1);
                fo[0].a = (u64)(top + 1); fo[0].b = (u64)h[4];
                FLUSHF();
                for (int g = 0; g < top; g++) fo[1 + g] = sk[g];
                fo[1 + top].a = PACKA(); fo[1 + top].b = PACKB();
            }
            cp = 0;
        }
        kept += (u64)(k3 | k4);
        if (!(k3 | k4 | cp)) continue;
        PUSHF();
        for (int q = 0; q < l; q++) { const u32 c = (u32)(rc >> (10 * q)) & 1023; SSET(c); }
        dups += __popc(dm & ((1u << l) - 1));
        const int xn = XN(l);
        top++;
        if (top >= STK - 1) { CTL[3] = 1; alive = 0; break; }
        x = xn; r = r2; d = d2; t = t2; pm = pm2; pM = pM2; start = 0; jp = cp;
        if (!ring && val > rcm) rcm = val;
        tries += (u64)(k3 ? n3 : 0) + (u64)(k4 ? n4 : 0);
        {
            const int jlo = k3 ? 0 : n3, jhi = k4 ? ns : n3;
            const u32 dok = (u32)(dups < Bmax);
            u32 av = 0;
            if (jlo < jhi) {
                const V2 *sc = SUCCC + x * SC;
                const V2 s0 = sc[0];
                av = avail6(s0.a, 0, jlo, jhi, sh, tid, dok) | avail6(s0.b, 6, jlo, jhi, sh, tid, dok);
                if (jhi > 12) {
#if SC == 2
                    const V2 s1 = sc[1];
                    av |= avail6(s1.a, 12, jlo, jhi, sh, tid, dok) | avail6(s1.b, 18, jlo, jhi, sh, tid, dok);
#else
                    const V2 s1 = sc[1], s2 = sc[2];
                    av |= avail6(s1.a, 12, jlo, jhi, sh, tid, dok) | avail6(s1.b, 18, jlo, jhi, sh, tid, dok) | avail6(s2.a, 24, jlo, jhi, sh, tid, dok);
                    if (jhi > 30) av |= avail6(s2.b, 30, jlo, jhi, sh, tid, dok);
#endif
                }
            }
            lo = av;
        }
        len2 = 0; l2 = 0; j = 0; dm = 0; type = 0; rc = 0; rid = 0;
        mk3 = cmk3; mk4 = cmk4;
    }
    FLUSHF();
    { V2 w; w.a = PACKA(); w.b = PACKB(); sk[top] = w; }
    for (int w = 0; w < UW; w++) ug[w] = sh[w * BT + tid];
    h[1] = top; h[3] = ip; h[0] = alive;
    cn[2 * ip] += kept; cn[2 * ip + 1] += tries; cn[10] += found; cn[11] += nodes; cn[12] += (u64)it;
    if (alive) atomicAdd(CTL + 1, 1ull);
}

extern "C" __global__ void gj_steal(const V2 *ROWC2, u32 *USED, u32 *CSV, int *HDR, int *CTX, V2 *STKM, int *LOCK, u64 *CTL,
                                    const u32 *TASKU, const u64 *TASKF, const int *TASKH, int N, int qn, int round, int tries, int NPv)
{
    const int i = blockIdx.x * blockDim.x + threadIdx.x;
    if (i >= N) return;
    int *h = HDR + 8 * i;
    if (h[0] != 0) return;
    const int NVD = (NPv / LL) * 8;
    u32 *ub = USED + (size_t)UW * i;
    V2 *sk = STKM + (size_t)i * STK;
    if (CTL[0] < (u64)qn) {
        const u64 q = atomicAdd(CTL, 1ull);
        if (q < (u64)qn) {
            const u32 *tu = TASKU + q * UW;
            for (int w = 0; w < UW; w++) ub[w] = tu[w];
            sk[0].a = TASKF[2 * q]; sk[0].b = TASKF[2 * q + 1];
            const int tip = TASKH[2 * q];
            CTX[8 * i + tip] = TASKH[2 * q + 1];
            h[1] = 0; h[2] = 0; h[3] = tip; h[4] = (int)q; __threadfence(); h[0] = 2;
            return;
        }
    }
    u32 s = (u32)i * 2654435761u + (u32)round * 0x9E3779B9u + 12345u;
    for (int at = 0; at < tries; at++) {
        s ^= s << 13; s ^= s >> 17; s ^= s << 5;
        const int v = (int)(((u64)s * (u64)N) >> 32);
        if (v == i) continue;
        int *hv = HDR + 8 * v;
        if (hv[0] == 0) continue;
        { int got = 0; for (int sp = 0; sp < 64 && !got; sp++) got = atomicCAS(LOCK + v, 0, 1) == 0; if (!got) continue; }
        __threadfence();
        const int vt = hv[1], vb = hv[2], vip = hv[3];
        int found = 0;
        V2 *vs = STKM + (size_t)v * STK;
        for (int f = vb; f <= vt; f++) {
            const u64 wa = vs[f].a, wb = vs[f].b;
            const u32 lo = (u32)wa, st = (u32)(wa >> 63);
            const int len2 = (int)(wa >> 45) & 7, l2 = (int)(wa >> 48) & 7;
            const int pr = len2 > l2 ? len2 - l2 : 0;
            const int kn = (int)(lo & 0x1fff), ke = (int)(lo >> 13);
            const int pc = st ? (ke > kn ? ke - kn : 0) : __popc(lo);
            int nst, tl = 0, ls = l2;                                       /* tl: the thief takes the lengths after ls */
            if (f < vt) { nst = (pc + 1) / 2; tl = pr > 0; }
            else if (pr > 0) { nst = (pc + 1) / 2; if (pc == 0 && pr >= 2) { tl = 1; ls = l2 + 1; } }
            else nst = pc / 2;
            if (nst == 0 && !tl) continue;
            u32 slo, vlo;
            if (st) { vlo = (u32)kn | ((u32)(ke - nst) << 13); slo = (u32)(ke - nst) | ((u32)ke << 13); if (nst == 0) slo = 0; }
            else { slo = lo; for (int q = 0; q < pc - nst; q++) slo &= slo - 1; vlo = lo ^ slo; }
            const u64 k0 = wa & ~0xffffffffull & ~(7ull << 45) & ~(7ull << 48) & ~(1ull << 62);
            vs[f].a = (wa & (1ull << 62)) | k0 | vlo | ((u64)(tl ? ls : len2) << 45) | ((u64)l2 << 48);
            sk[f].a = k0 | slo | ((u64)(tl ? len2 : 0) << 45) | ((u64)(tl ? ls : 0) << 48);
            sk[f].b = wb;
            for (int g = 0; g < f; g++) sk[g] = vs[g];
            int above = 0;
            for (int g = f + 1; g <= vt; g++) above += (int)(vs[g].a >> 63);
            const int ipf = vip - above;
            const u32 *uv = USED + (size_t)UW * v;
            const u32 *cv = CSV + ((size_t)v * MAXSV + ipf) * UW;
            for (int w = 0; w < UW; w++) ub[w] = above ? ((uv[w] & 0x55555555u) | cv[w]) : uv[w];
            int pg = ipf;
            u64 ga = wa;                                                    /* the rows of the frames f .. vt - 1 are placed in the victim */
            for (int g = f; g < vt; g++) {
                if (g > f) { ga = vs[g].a; pg += (int)(ga >> 63); }
                const int gx = (int)(ga >> 32) & 0x1fff, gj = (int)(ga >> 51) & 31, lg = (int)(ga >> 48) & 7; const u32 gd = (u32)(ga >> 56) & 63;
                const u64 rg = ROWC2[(ga >> 63) ? NVD * 32 + gx : gx * 32 + gj].a;
                for (int q = 0; q < lg; q++) { const u32 c = (u32)(rg >> (10 * q)) & 1023;
                    const u32 m_ = (((gd >> q) & 1) ? 0u : 1u) | ((pg == ipf) ? 2u : 0u);
                    ub[c >> 4] &= ~(m_ << (2 * (c & 15))); }
            }
            for (int w = 0; w < 8; w++) CTX[8 * i + w] = CTX[8 * v + w];
            h[1] = f; h[2] = f; h[3] = ipf; h[4] = hv[4]; __threadfence(); h[0] = 2;
            found = 1;
            break;
        }
        __threadfence(); LOCK[v] = 0;
        if (found) { atomicAdd(CTL + 4, 1ull); break; }
    }
}
