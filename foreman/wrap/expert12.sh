#!/bin/bash
# expert12.sh OUT PLAN BASE N L0 SEC [THR=6]: a whole chain of tools as one arm of foreman, the chain that took
# William Echols's n = 12 word W-0091 from 522,736,503 to 522,736,440 by hand.  Cycles until a whole cycle gains
# nothing or SEC seconds are used:
#   1. trailsearch kmax 8 T0 0.4, 1200 s;
#   2. segment insertion with 3, 4 and 5 cuts, slack 1 (tools/gpucuts/tsw5g2): judged on the NVIDIA card (--or3-gpu)
#      when gpu_free.sh says the card is free, else on the processor;
#   3. segins_ils kick depth 1 slack 2, 3000 s (first cycle only: it stalls afterwards);
#   4. tools/pipeline/ils12.sh to its end (polish.sh, two segins_ils lanes kmax 2 and 3 of 3000 s, while a round gains);
#   5. recut --co-skip.
# Every step starts from the best plan so far.  Prints "wrote OUT length L" (L0 and the input plan when nothing
# gains); foreman verifies the word with delcheck.  Log DIR/expert.log.
. "$(dirname "$0")/paths.sh"; OUT=$1; PLAN=$2; B=$3; N=$4; L0=$5; SEC=$6; THR=${7:-6}
D=$(dirname "$OUT" | tr '\\' '/'); LOG=$D/expert.log
say() { echo "$(date '+%m-%d %H:%M:%S') $*" | tee -a "$LOG"; }
wl() { grep -a -o 'wrote .* length [0-9]*' "$1" 2>/dev/null | tail -1 | grep -o '[0-9]*$'; }
T_END=$(( $(date +%s) + SEC )); left() { echo $(( T_END - $(date +%s) )); }
best=$L0; P=$PLAN; bw=""
take() {   # take LEN WORD PLAN STEP: a shorter word with its plan becomes the current best
  if [ -n "$1" ] && [ "$1" -lt "$best" ] && [ -f "$2" ] && [ -f "$3" ]; then
    best=$1; cp "$3" "$D/best.plan"; P=$D/best.plan; cp "$2" "$D/best.txt"; bw=$D/best.txt
    say "$4: $best"; return 0
  fi
  return 1
}
say "start: n $N plan $L0, $SEC s"
for cyc in $(seq 1 99); do
  [ "$(left)" -gt 1500 ] || { say "time up"; break; }
  g0=$best
  # 1. trailsearch
  t=$D/ts$cyc
  OMP_NUM_THREADS=4 "$(exe trailsearch)" "$B" "$t.txt" --plan-in "$P" --time 1200 --seed $((cyc * 11)) --kmax 8 \
    --T0 0.4 --threads 4 --sync 15 > "$t.log" 2>&1
  take "$(wl "$t.log")" "$t.txt" "$t.txt.plan" "cycle $cyc trailsearch" || say "cycle $cyc trailsearch: no gain"
  rm -f "$t.txt"
  # 2. segment insertion 3 / 4 / 5 cuts slack 1
  for k in 3 4 5; do
    [ "$(left)" -gt 1500 ] || break
    s=$D/or$cyc$k
    if bash "$FMW/gpu_free.sh" > "$D/gpu_free.log" 2>&1; then
      OMP_NUM_THREADS=$THR "$(exe "$GC" tsw5g2)" "$B" "$s.txt" --plan-in "$P" --time 0 --threads "$THR" --or3 $k \
        --or3-slack 1 --or3-gpu --or3-maxcand 200000 --or3-sec 1800 --or3-stop "$D/STOP" > "$s.log" 2>&1
      where=card
    else                                  # the same program judging on the processor
      OMP_NUM_THREADS=$THR "$(exe "$GC" tsw5g2)" "$B" "$s.txt" --plan-in "$P" --time 0 --threads "$THR" --or3 $k \
        --or3-slack 1 --or3-maxcand 3000 --or3-sec 1800 --or3-stop "$D/STOP" > "$s.log" 2>&1
      where=cpu
    fi
    take "$(wl "$s.log")" "$s.txt" "$s.txt.plan" "cycle $cyc or3 $k cuts slack 1 ($where)" || say "cycle $cyc or3 $k ($where): no gain"
    rm -f "$s.txt"
  done
  # 3. segins_ils kick depth 1 (first cycle)
  if [ "$cyc" = 1 ] && [ "$(left)" -gt 3600 ]; then
    i=$D/ils1
    "$(exe segins_ils)" "$B" "$i.txt" --plan-in "$P" --time 0 --threads 2 --seed 7 --ils 3000 --ils-log 600 \
      --ils-kmax 1 --ils-slack 2 --ils-near -1 --ils-cuts 3 --or3-stop "$D/STOP" > "$i.log" 2>&1
    take "$(wl "$i.log")" "$i.txt" "$i.txt.plan" "cycle 1 segins_ils kmax 1" || say "cycle 1 segins_ils kmax 1: no gain"
    rm -f "$i.txt"
  fi
  # 4. ils12.sh to its end
  if [ "$(left)" -gt 3600 ]; then
    I=$D/I$cyc; NR=$(( ( $(left) - 1800 ) / 3300 )); [ "$NR" -gt 20 ] && NR=20
    if [ "$NR" -ge 1 ]; then
      BASE=$B TOOLS=$T bash "$PL/ils12.sh" "$I" "$(echo "$P" | tr '\\' '/')" "$best" "$NR" 3000 > /dev/null 2>&1
      read -r ib ip < "$I/best.txt" 2>/dev/null
      iw=${ip%.plan}; [ -f "$iw" ] || iw=$iw.txt   # a segins_ils word is o.txt beside o.txt.plan, a polish word NAME.txt beside NAME.plan
      take "$ib" "$iw" "$ip" "cycle $cyc ils12" || say "cycle $cyc ils12: no gain (${ib:-none})"
    fi
  fi
  # 5. recut --co-skip
  r=$D/rc$cyc
  "$(exe recut)" "$B" "$r.txt" --plan-in "$P" --co-skip --time 0 > "$r.log" 2>&1
  take "$(wl "$r.log")" "$r.txt" "$r.txt.plan" "cycle $cyc recut" || say "cycle $cyc recut: no gain"
  rm -f "$r.txt"
  if [ "$best" -ge "$g0" ]; then say "cycle $cyc: no gain, fixed point"; break; fi
done
if [ -z "$bw" ]; then cp "$PLAN" "$OUT.plan"; : > "$OUT"; say "END no gain"; echo "wrote $OUT length $L0"; exit 0; fi
mv "$bw" "$OUT"; cp "$P" "$OUT.plan"
say "END best $best"
echo "wrote $OUT length $best"
