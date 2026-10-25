"""check_witness.py DATA WITNESS_LEAN: the list `witness` written out in Witness.lean is the word of the data file.

The data file holds the 872 digits 1-6 of Houston's word (Grayzel's `data/superperm6_872_clean.txt`); Witness.lean of
the kernel-only version has the same word as a list of `Fin 6` values 0-5.  Exit status 0 if they agree.
"""
import re
import sys

digits = [int(c) - 1 for c in open(sys.argv[1], encoding='ascii').read() if c in '123456']
src = open(sys.argv[2], encoding='utf-8').read()
m = re.search(r'def witness : Word :=\s*\[([0-9,\s]*)\]', src)
if not m:
    sys.exit('no literal definition of witness in ' + sys.argv[2])
lit = [int(x) for x in m.group(1).replace('\n', ' ').split(',')]
if len(digits) != 872 or lit != digits:
    sys.exit('the witness in %s differs from %s' % (sys.argv[2], sys.argv[1]))
print('witness: the 872 letters of Witness.lean are those of the data file')
