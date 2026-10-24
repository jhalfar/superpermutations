#!/bin/bash
# rate16.sh: the defect-16 statements T1..T8 on the card (table capD.txt): T8 and T7 in full, the others for 60 s
# (line ABORTED: rows tried so far / 60 s = the rate at the start of that tree).
cd "$(dirname "$0")"
D=../jrev/capD.txt
one() { name=$1; ms=$2; e="$3"; shift 3
  sh=$(tasklist | grep -c -i "gk4.exe")
  echo "$name [$e] $* (limit $ms s, gk4 on the card: $sh)"
  env $e MAXSEC=$ms ./gj.exe 7 $D run $* 2>&1 | grep -E "^piece|^RESULT|^card|ABORT|FOUND|range|exceed" | cut -c1-330; }
one T8 1500 X=1 66 65 2 S0 S0 S0 R
one T7 1500 X=1 62 70 3 S1 S1 R R
one T1_ordprev 60 "ORD=1 REV=1 RMODE=2 RP=0 PB=15 PH=25" 50 84 1 S7 S7
one T1_plain 60 X=1 50 84 1 S7 S7
one T2_ringfirst_8_15_prev 60 "RLO=8 RHI=15 REV=1 RMODE=2 RP=1 PB=15 PH=30" 46 89 1 R S7
one T2_kernelfirst_prev 60 "REV=1 RMODE=2 RP=0 PB=15 PH=30" 46 89 1 S7 R
one T3_prev 60 "REV=1 RMODE=2 RP=0 PB=15 PH=30" 52 82 2 S5 R R
one T4_ordprev 60 "ORD=1 REV=1 RMODE=2 RP=0 PB=16 PH=25" 56 77 2 S4 S4 R
one T5_plain 60 X=1 60 72 2 S3 S3 S3
one T5_ordprev 60 "ORD=1 REV=1 RMODE=2 RP=0 PB=16 PH=25" 60 72 2 S3 S3 S3
one T6_plain 60 X=1 58 75 3 S2 R R R
