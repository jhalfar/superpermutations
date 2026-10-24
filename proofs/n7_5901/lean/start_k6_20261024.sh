#!/bin/bash
# 24.10: the Lean equation of K6 (16 modules NK6_00..15, about 217 thread-hours), as PROOF_5901.md section 7.2 says
cd "$(dirname "$0")" || exit 1
exec nice -n 19 ./nk_queue.sh 4
