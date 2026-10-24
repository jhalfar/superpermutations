# Generates LowerBounds/KTestTables.lean: the reference tables D^u_7, D^u_8 (rows T_0..T_(S-1), D_S) of the first
# program, cut to the holes that a search for S links reads, for tests and for the benchmark.
import os
here = os.path.dirname(os.path.abspath(__file__))
def rd(S):
    D = {}
    for line in open(os.path.join(here, '..', 'tables', 'capD15u_%d.txt' % S)):
        if ':' in line and not line.startswith('#'):
            s, r = line.split(':'); D[int(s)] = [int(x) for x in r.split()][:91 - 6 * S]
    return [D[s] for s in range(S + 1)]
def L(r): return '[' + ', '.join(map(str, r)) + ']'
def LL(t): return '[' + ',\n   '.join(L(r) for r in t) + ']'
d7, d8 = rd(7), rd(8)
low = [r[:] for r in d7]; low[7][48] -= 1     # a table that is too low at 48 holes
out = '''/-!
# Reference tables for tests (generated; do not edit)

`Du7`, `Du8`: the tables of the reference runs for 7 and for 8 links (rows `T_0 .. T_(S-1)` of table T
and the row `D_S`, to `90 - 6 S` holes).  `Du7low`: `Du7` with the last entry of its last row lowered
by one, which is not a valid table.
-/

namespace SuperpermLowerBounds
namespace T5900

def Du7 : List (List Nat) :=
  %s

def Du8 : List (List Nat) :=
  %s

def Du7low : List (List Nat) :=
  %s

end T5900
end SuperpermLowerBounds
''' % (LL(d7), LL(d8), LL(low))
open(os.path.join(os.environ.get('OUT', os.path.join(here, '..', '..', 'LowerBounds')), 'KTestTables.lean'), 'w', encoding='utf-8', newline='\n').write(out)
print('ok', [len(r) for r in d7], d7[7][-3:], low[7][-3:])
