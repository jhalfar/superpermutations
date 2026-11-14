#!/bin/bash
# gpubusy.sh - exit 0 if the card is free, 1 if busy.  Busy = a compute process (type C, not C+G) in nvidia-smi's list,
# or a utilisation of 30 % or more in all of three samples one second apart (processes inside WSL, e.g. a solver
# running on the card there, do not appear in the list).  Used before every card run of tools/gpucheck.
L=$(nvidia-smi | awk '/Processes:/{p=1} p && $0 ~ /^\|  +[0-9]+ +N\/A +N\/A +[0-9]+ +C +/')
hi=0
for i in 1 2 3; do
  u=$(nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | head -1 | tr -d ' ')
  [ "${u:-0}" -ge 30 ] && hi=$((hi + 1))
  [ $i -lt 3 ] && sleep 1
done
echo "gpu: $(nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader), high samples $hi/3"
[ -n "$L" ] && { echo "$L"; exit 1; }
[ $hi -eq 3 ] && { echo "utilisation high (a process outside Windows?)"; exit 1; }
echo "free"; exit 0
