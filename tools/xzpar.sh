#!/bin/bash
# xzpar.sh - archive of a word in the format of the words/ directory: XZ with a delta filter of distance n, LZMA2 9e and
# a SHA-256 check, as Pantone's compress_word.py writes it, but in 64 MiB blocks so that several threads can work.
# Measured at n = 12 on 4 threads: 116 seconds against about 420, for a file 1.2 % larger.  The round trip is
# verified before the archive gets its name.  About 0.7 GB of RAM per thread.  `xz -d` unpacks the result.
# usage: xzpar.sh WORD.txt OUT.xz N [THREADS=4]      prints one JSON line with the hashes
[ $# -ge 3 ] || { sed -n '2,6p' "$0"; exit 1; }
W=$1; OUT=$2; N=$3; T=${4:-4}
S=$(sha256sum "$W" | cut -d' ' -f1); t0=$(date +%s)
nice -n 19 xz -c -T"$T" --block-size=64MiB --check=sha256 --delta=dist="$N" --lzma2=preset=9e,dict=64MiB,lc=4,lp=0,pb=0 "$W" > "$OUT.partial" || exit 1
R=$(nice -n 19 xz -dc -T"$T" "$OUT.partial" | sha256sum | cut -d' ' -f1)
[ "$R" = "$S" ] || { echo "round trip FAILED"; exit 1; }
mv "$OUT.partial" "$OUT"
echo "{\"file_sha256\": \"$S\", \"compressed_bytes\": $(stat -c %s "$OUT"), \"compressed_sha256\": \"$(sha256sum "$OUT" | cut -d' ' -f1)\", \"roundtrip_verified\": true, \"threads\": $T, \"seconds\": $(( $(date +%s) - t0 ))}"
