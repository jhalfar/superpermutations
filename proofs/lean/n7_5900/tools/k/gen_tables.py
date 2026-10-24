# Generates LowerBounds/KTables.lean from PTables.lean (set B) and capD15.txt (table D; tables/ here).
import re, os
here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, '..', '..', '..', 'n7', 'LowerBounds', 'PTables.lean'), encoding='utf-8').read()
def grab(name):
    m = re.search(r'def %s : [^\n]*:=\s*(\[.*?\])\s*\n\s*\n' % name, src, re.S)
    return eval(m.group(1))
M, P, PR = grab('Mtab'), grab('Ptabs'), grab('PRtab')
assert len(M) == 85 and P[0] == M and [len(r) for r in P] == [85, 79, 73, 67, 61, 55] and len(PR) == 78
D = {}
for line in open(os.path.join(here, '..', 'tables', 'capD15.txt')):
    if ':' in line and not line.startswith('#'):
        s, r = line.split(':'); D[int(s)] = [int(x) for x in r.split()]
D = [D[s] for s in range(9)]
assert [len(r) for r in D] == [91 - 6 * s for s in range(9)]
# T'_0: set B with 97 at 59, I2 at 62..75, 120 at 76 (= D_0 to 76 holes), then M
T0 = D[0][:77] + M[77:]
exc = {59: 97, 62: 101, 63: 102, 64: 103, 65: 104, 66: 106, 67: 107, 68: 109, 69: 111, 70: 112, 71: 115, 72: 116,
       73: 117, 74: 118, 75: 119, 76: 120}
for x in range(85):
    assert T0[x] == exc.get(x, M[x]), x
T = [T0, P[1], P[2], P[3], P[4], D[5], D[6], D[7], D[8]]
for s in range(1, 5):
    for x in range(len(P[s])):
        assert D[s][x] == min(P[s][x], x + 44 + 5 * s), (s, x)
for s in range(9):
    for x in range(len(D[s])):
        assert D[s][x] <= x + 44 + 5 * s
TR = PR[:64] + [95, 96, 97, 98, 99, 100] + [min(PR[x], T0[x]) for x in range(70, 78)] + T0[78:85]
assert TR[70:78] == [112, 115, 116, 117, 118, 119, 120, 126], TR[70:78]
assert len(TR) == 85
def L(r): return '[' + ', '.join(map(str, r)) + ']'
def LL(t): return '[' + ',\n   '.join(L(r) for r in t) + ']'
out = '''/-!
# Tables for 5,900 (generated; do not edit)

`Dtab`: table D of the written proof (section 2.3), rows `s = 0..8`, entries `x = 0..90 - 6 s`.
`Ttab`: table T' (sections 2.2 and 2.3), rows `0..8`: the chain row to 84 holes (set B with the entries
97 at 59 holes, 101 .. 119 at 62 .. 75 holes and 120 at 76 holes), the rows `P_1 .. P_4` of set B, and
the rows `D_5 .. D_8`.  `TRtab`: the ring row of T' to 84 holes.
-/

namespace SuperpermLowerBounds
namespace T5900

/-- Table D. -/
def Dtab : List (List Nat) :=
  %s

/-- Table T'. -/
def Ttab : List (List Nat) :=
  %s

/-- The ring row of T'. -/
def TRtab : List Nat :=
  %s

end T5900
end SuperpermLowerBounds
''' % (LL(D), LL(T), L(TR))
open(os.path.join(os.environ.get('OUT', os.path.join(here, '..', '..', 'LowerBounds')), 'KTables.lean'), 'w', encoding='utf-8', newline='\n').write(out)
# caps files for the C programs: T' (rows 0..8) for cross-checks
with open(os.path.join(os.environ.get('OUT', here), 'capT.txt'), 'w', newline='\n') as f:
    for s in range(9): f.write('%d: %s\n' % (s, ' '.join(map(str, T[s]))))
print('ok', [len(r) for r in T], len(TR))
