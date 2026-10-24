#!/bin/bash
# ksumm.sh TAG NPARTS - sums the parts of kparts.sh: kept = above the gate + sum over the parts of (kept - above the gate).
# Last line "RESULT: no violation, all parts present" = the statement is COMPUTED (after m5check.sh TAG says 1 line).
cd "$(dirname "$0")"
dir=parts/$1; n=0; tot=0; viol=0; ab=-1; dis=0
for i in $(seq 0 $(($2 - 1))); do
  f=$dir/p$i.txt; [ -s $f ] || continue
  l=$(head -1 $f); k=$(echo "$l" | grep -o "   kept [0-9]*" | grep -o "[0-9]*"); a=$(echo "$l" | grep -o "gate: rows placed [0-9]* kept [0-9]*" | grep -o "[0-9]*$"); v=$(echo "$l" | grep -o "violations [0-9]*" | grep -o "[0-9]*")
  [ $ab -ge 0 ] && [ $ab -ne $a ] && { echo "parts disagree above the gate"; dis=1; }
  ab=$a; tot=$((tot + k - a)); viol=$((viol + v)); n=$((n + 1))
done
cat $dir/params.txt
echo "parts $n of $2   kept $((tot + ab)) (above the gate $ab)   violations $viol   card seconds $(grep -ho 'kept [0-9]* in [0-9.]*s' $dir/p*.txt | awk '{s += substr($4, 1, length($4) - 1)} END {print s}')"
[ $n -eq $2 ] && [ $viol -eq 0 ] && [ $dis -eq 0 ] && echo "RESULT: no violation, all parts present"
