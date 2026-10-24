# Writes scratchJ15/both_order.txt: the evaluation modules of part B (scratchK/native_order.txt) and of part C
# (scratchJ15/native_order.txt) in one order for j15_native_both.sh.  Lines "K NAME" / "J NAME".
# The short modules of both parts come first (a wrong answer or a broken build shows within the first hours),
# then the long ones, taken in turn from the two parts.
#   .venv/Scripts/python.exe scratchJ15/mkorder.py
import os
here = os.path.dirname(os.path.abspath(__file__))
def read(p):
    return [x.strip() for x in open(p, encoding='utf-8').read().split() if x.strip()]
K = read(os.path.join(here, '..', 'scratchK', 'native_order.txt'))
J = read(os.path.join(here, 'native_order.txt'))
shortK = [m for m in K if not (m.startswith('KK0_') or m.startswith('KK1_') or m.startswith('KK2_'))]
longK = [m for m in K if m not in shortK]
shortJ = [m for m in J if not (m.startswith('J15S1_') or m.startswith('J15S2A2_'))]
longJ = [m for m in J if m not in shortJ]
out = []
# short: the cheapest of both first
first = ['KK87Native', 'KSmallNative', 'J15S5Native', 'J15S4Native', 'J15S3Native', 'KK4Native', 'KK5Native', 'KK3Native']
for m in first:
    if m in shortK:
        out.append('K ' + m)
    elif m in shortJ:
        out.append('J ' + m)
for m in shortK:
    if 'K ' + m not in out:
        out.append('K ' + m)
for m in shortJ:
    if 'J ' + m not in out:
        out.append('J ' + m)
i = j = 0
while i < len(longJ) or j < len(longK):
    if i < len(longJ):
        out.append('J ' + longJ[i]); i += 1
    if j < len(longK):
        out.append('K ' + longK[j]); j += 1
assert len(out) == len(K) + len(J) and len(set(out)) == len(out)
open(os.path.join(here, 'both_order.txt'), 'w', newline='\n').write('\n'.join(out) + '\n')
print(len(out), 'modules:', ' '.join(x.split()[1].replace('Native', '') for x in out))
