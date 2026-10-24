#!/bin/bash
# gjsumm.sh TAG NPARTS NPARTS2 - sums the parts of gjparts.sh: objects found, kept prefixes, rows tried, card seconds.
# Counts above the gate are in part 0 only and piece 1 is counted for PART2 = 0 only (as jt.c), so the sums are the
# counts of the whole statement.  Last line "RESULT: all parts present, found 0" = the statement is COMPUTED.
cd "$(dirname "$0")"
dir=parts/$1; n=0; miss=""
cat $dir/command.txt
for i in $(seq 0 $(($2 - 1))); do for j in $(seq 0 $((${3:-1} - 1))); do
  f=$dir/p${i}_$j.txt; if [ -s $f ] && grep -q "^RESULT" $f; then n=$((n + 1)); else miss="$miss ${i}_$j"; fi
done; done
cat $dir/p*_*.txt 2>/dev/null | awk '/^RESULT/ {f += $3; k += $5; t += $8; s += substr($10, 1, length($10) - 1)} /^FOUND/ {print} END {printf "found %d   kept %.0f   rows tried %.0f   card seconds %.1f\n", f, k, t, s}' > $dir/sum.txt
cat $dir/sum.txt
echo "parts $n of $(($2 * ${3:-1}))${miss:+   missing:$miss}"
[ $n -eq $(($2 * ${3:-1})) ] && grep -q "^found 0 " $dir/sum.txt && echo "RESULT: all parts present, found 0"
