#!/bin/bash
# Compiles the modules of nk_order.txt one after the other (nat.sh, K16Search.dll, J threads); a module whose .olean
# exists is skipped, so the same line resumes.  Stops at the first failure.   ./nk_queue.sh [J]
cd "$(dirname "$0")" || exit 1
J="${1:-3}"
while read -r M; do
  [ -f "build/lib/Audit5901/$M.olean" ] && continue
  echo "$(date '+%F %T') start $M" >> nk_queue.log
  ./nat.sh "$M" ../../../../lb/lean/build/native/K16Search.dll "$J" || { echo "$(date '+%F %T') FAILED $M" >> nk_queue.log; exit 1; }
  echo "$(date '+%F %T') done $M $(grep -o 'wall=[0-9]*s' logs/$M.log)" >> nk_queue.log
done < nk_order.txt
echo "$(date '+%F %T') queue finished" >> nk_queue.log
