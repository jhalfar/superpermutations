#!/bin/bash
# mkptx.sh - compiles the CUDA kernels of this directory to PTX: kern.cu (for trailsearch_gpu), segins_kern.cu (for
# segins_gpu) and, with WIDE=1, kern_wide.cu (for recut_wide --gpu --wide).
#
# Part of github.com/jhalfar/superpermutations.  Apache License 2.0, see LICENSE and NOTICE.
#
# usage: bash mkptx.sh [OUTDIR]          OUTDIR: where the .ptx files go (default: this directory)
#        ARCH=sm_89 bash mkptx.sh        another card generation (default sm_120, the RTX 50 series, the only one I
#                                        tested); NVCC=/path/to/nvcc if nvcc is not on the PATH
# It needs the CUDA toolkit for this step only: the programs load the driver library at run time.  On Windows run it
# from a shell in which the compiler of Visual Studio is set up (vcvars64.bat) and that has bash and awk, or type the
# nvcc lines there and run the awk line in Git Bash afterwards.
#
# segins_kern.ptx gets one line that nvcc does not write: ".maxnreg 56" in front of the body of the kernel.  It limits
# the kernel to 56 registers per thread, so that a block of 1024 threads fits one multiprocessor (65,536 registers)
# whatever the compiler would use.  With that line the file is byte for byte the one my runs loaded (CUDA 13.4).
set -e
S="$(cd "$(dirname "$0")" && pwd)"; O="${1:-$S}"; NVCC="${NVCC:-nvcc}"; ARCH="${ARCH:-sm_120}"
mkdir -p "$O"
"$NVCC" -arch=$ARCH -ptx -o "$O/kern.ptx" "$S/kern.cu"
"$NVCC" -arch=$ARCH -ptx -o "$O/segins_kern.raw.ptx" "$S/segins_kern.cu"
awk '/^\.visible \.entry or_judge\(/ { e = 1 } e && /^\{/ { print ".maxnreg 56"; e = 0 } { print }' "$O/segins_kern.raw.ptx" > "$O/segins_kern.ptx"
rm -f "$O/segins_kern.raw.ptx"
grep -q "^\.maxnreg 56" "$O/segins_kern.ptx" || { echo "mkptx.sh: the line .maxnreg was not written (another nvcc version?)" >&2; exit 1; }
[ "${WIDE:-0}" = 1 ] && "$NVCC" -arch=$ARCH -ptx -o "$O/kern_wide.ptx" "$S/kern_wide.cu"
echo "wrote kern.ptx and segins_kern.ptx to $O"
