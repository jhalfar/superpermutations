#!/bin/bash
# build.sh [OUTDIR] - PTX of the card kernels and the host programs of tools/gpucheck, into OUTDIR (default: this
# directory).  NVCC = the CUDA compiler (default nvcc; on Windows it needs the MSVC build tools in the environment,
# e.g. from vcvars64.bat).  CC = the C compiler (default gcc).  On Linux add -ldl: LIBDL=-ldl.
H=$(cd "$(dirname "$0")" && pwd); O=${1:-$H}; mkdir -p "$O" || exit 1
NVCC=${NVCC:-nvcc}; CC=${CC:-gcc}; LIBDL=${LIBDL:-}
for k in gpuprep w2pg tsgl; do "$NVCC" -arch=sm_120 -O3 -ptx -o "$O/$k.ptx" "$H/$k.cu" || exit 1; done
$CC -O2 -Wall -o "$O/gcheck" "$H/gcheck.c" -lpthread $LIBDL || exit 1
$CC -O2 -Wall -o "$O/gdelcheck" "$H/gdelcheck.c" -lpthread $LIBDL || exit 1
$CC -O2 -fopenmp -o "$O/w2p13g" "$H/w2p13g.c" $LIBDL || exit 1
$CC -O2 -mpopcnt -fopenmp -o "$O/trailsearch_gl" "$H/trailsearch_gl.c" -lm $LIBDL || exit 1
$CC -O2 -o "$O/corrupt" "$H/corrupt.c" || exit 1
echo build done
