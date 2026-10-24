/* emu.cpp (agent n7-gkjs): the two kernels of gkjs.cu compiled for the processor.  One call = one launch: the threads of
 * the grid run one after the other.  For tests of the logic without the card (host built with -DEMU). */
#include <cstddef>
#include <cstdlib>
#define __device__
#define __forceinline__ inline
#define __global__
#define __shared__ static
#define __align__(n)
struct Idx { unsigned x; };
static Idx threadIdx, blockIdx, blockDim;
static inline int __ffs(int v) { return __builtin_ffs(v); }
static inline int __clz(int v) { return v ? __builtin_clz((unsigned)v) : 32; }
static inline int __popc(unsigned v) { return __builtin_popcount(v); }
static inline unsigned long long atomicAdd(unsigned long long *p, unsigned long long v) { unsigned long long o = *p; *p = o + v; return o; }
static inline int atomicCAS(int *p, int c, int v) { int o = *p; if (o == c) *p = v; return o; }
static inline void __threadfence() {}
#include "gkjs.cu"
#define PP(T, i) ((T *)(size_t)*(unsigned long long *)p[i])
#define PI(i) (*(int *)p[i])
extern "C" void emu_run(void **p, unsigned grid, unsigned bt) {
    blockDim.x = bt;
    for (unsigned b = 0; b < grid; b++) for (unsigned t = 0; t < bt; t++) {
        blockIdx.x = b; threadIdx.x = t;
        gk_run(PP(const u64, 0), PP(const V2, 1), PP(const unsigned short, 2), PP(const u64, 3), PP(u32, 4), PP(int, 5), PP(u64, 6), PP(V2, 7), PP(u64, 8),
               PI(9), PI(10), PI(11), PI(12), PI(13), PI(14), PI(15), PI(16));
    }
}
extern "C" void emu_steal(void **p, unsigned grid, unsigned bt) {
    blockDim.x = bt;
    for (unsigned b = 0; b < grid; b++) for (unsigned t = 0; t < bt; t++) {
        blockIdx.x = b; threadIdx.x = t;
        gk_steal(PP(const u64, 0), PP(u32, 1), PP(int, 2), PP(V2, 3), PP(int, 4), PP(u64, 5), PP(const u32, 6), PP(const u64, 7),
                 PI(8), PI(9), PI(10), PI(11), PI(12), PI(13));
    }
}
