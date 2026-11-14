#!/bin/bash
# gpu_free.sh: exit 0 if the NVIDIA card looks free (three samples one second apart: utilization below 25 % and less
# than 10 GB of its memory in use; a Windows desktop alone uses a few GB), else exit 1.  No card or no nvidia-smi: 1.
# GPU_FREE_UTIL / GPU_FREE_MB change the two limits.
command -v nvidia-smi > /dev/null 2>&1 || { echo "no nvidia-smi"; exit 1; }
for i in 1 2 3; do
  line=$(nvidia-smi --query-gpu=utilization.gpu,memory.used --format=csv,noheader,nounits | head -n 1 | tr -dc '0-9,')
  util=${line%%,*}; mem=${line#*,}
  [ -n "$util" ] && [ -n "$mem" ] || { echo "no card"; exit 1; }
  if [ "$util" -ge "${GPU_FREE_UTIL:-25}" ] || [ "$mem" -ge "${GPU_FREE_MB:-10240}" ]; then
    echo "busy: utilization $util %, $mem MB used"; exit 1
  fi
  sleep 1
done
echo "free (utilization $util %, $mem MB used)"
