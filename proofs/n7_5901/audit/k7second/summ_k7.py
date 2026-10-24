"""Sum and check the 64 part files of the second count of K7 (run_k7.sh): all parts present and complete, one
statement line and one gate line, no violation; kept = kept_top + sum of kept_below (as summ.py of the second programs of defect 15, not in this repository)."""
import os, re, sys
d = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'parts')
N = 64
stm = gate = None; kept = placed = viol = 0; cpu = 0.0; bad = []
for i in range(N):
    fn = os.path.join(d, 'p%d.txt' % i)
    if not os.path.exists(fn): bad.append((i, 'missing')); continue
    L = open(fn).read().split('\n')
    if len(L) < 5 or L[4] != 'END': bad.append((i, 'incomplete')); continue
    if stm is None: stm, gate = L[0], L[1]
    if L[0] != stm: bad.append((i, 'statement line differs'))
    if L[1] != gate: bad.append((i, 'gate line differs'))
    m = re.match(r'part (\d+) kept_below (\d+) placed_below (\d+) violations_below (\d+)$', L[2])
    if not m or int(m.group(1)) != i: bad.append((i, 'part index')); continue
    kept += int(m.group(2)); placed += int(m.group(3)); viol += int(m.group(4))
    cpu += float(L[3].split()[4])
    if os.path.exists(fn + '.viol'): bad.append((i, 'violation file'))
g = re.match(r'gate: depth (\d+) parts (\d+) gate_count (\d+) kept_top (\d+) placed_top (\d+) violations_top (\d+)$', gate)
kept += int(g.group(4)); placed += int(g.group(5)); viol += int(g.group(6))
print(stm); print(gate)
print('parts %d of %d; problems %s' % (N - sum(1 for b in bad if b[1] == 'missing'), N, bad))
print('kept %d   placed %d   violations %d   cpu %.0f s (%.3f thread-hours), %.4f us per kept' % (kept, placed, viol, cpu, cpu / 3600, 1e6 * cpu / kept))
want = 320243136927
print('Table C (gk4 on the card): kept %d -> %s' % (want, 'EQUAL' if kept == want else 'DIFFERENT'))
ok = not bad and viol == 0 and kept == want
print('RESULT: ' + ('all parts present, one statement line, no violation, kept equal to Table C' if ok else 'CHECK FAILED'))
sys.exit(0 if ok else 1)
