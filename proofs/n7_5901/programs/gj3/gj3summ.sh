#!/bin/bash
# gj3summ.sh TAG NPARTS NPARTS2 - sums the parts of gj3parts.sh: objects found, kept prefixes, rows tried, card seconds.
# With PLIST (environment) only the listed first-gate parts are expected.
# Last line "RESULT: all parts present, found 0" = the statement is COMPUTED.  A line FOUND = an object (the statement is false).
cd "$(dirname "$0")"
dir=parts/$1; n=0; miss=0
cat $dir/command.txt
for i in ${PLIST:-$(seq 0 $(($2 - 1)))}; do for j in $(seq 0 $((${3:-1} - 1))); do
  f=$dir/p${i}_$j.txt; if [ -s $f ] && grep -q "^RESULT" $f; then n=$((n + 1)); else miss=$((miss + 1)); fi
done; done
cat $dir/p*_*.txt 2>/dev/null | awk '/^RESULT/ {f += $3; k += $5; t += $8; s += substr($10, 1, length($10) - 1)} /^FOUND/ {print} END {printf "found %d   kept %.0f   rows tried %.0f   card seconds %.1f\n", f, k, t, s}' > $dir/sum.txt
cat $dir/sum.txt
echo "parts $n of $(($2 * ${3:-1}))   missing $miss"
[ $miss -eq 0 ] && grep -q "^found 0 " $dir/sum.txt && echo "RESULT: all parts present, found 0"
