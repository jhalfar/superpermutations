"""Build order of Lean modules, from the import lines of their sources.

    order.py TARGET.Module [TARGET.Module ...] -- ROOT [ROOT ...]

A ROOT is a directory that holds sources: ROOT/A/B.lean is the module A.B.  When two roots hold the same
module, the root named first wins (this is how constant/patches replaces one file of Jay Pantone's library).
Imports that are found under no root (Mathlib, Std, ...) are taken as already compiled.

Output, one line per module that a target needs, in an order in which they can be compiled:

    LEVEL <tab> MODULE <tab> ROOT <tab> SOURCE <tab> STAMP

LEVEL  0 for a module that imports no other module of the roots, otherwise one more than the largest level
       among its imports.  Two modules of the same level do not import each other, so they can be compiled
       at the same time.
STAMP  SHA-256 of the source text and of the stamps of its imports.  It changes when the source or anything
       it imports changes; the build scripts keep it next to each compiled module to know what is up to date.
"""
import hashlib, os, re, sys

args = sys.argv[1:]
if '--' not in args:
    sys.exit(__doc__)
targets, roots = args[:args.index('--')], args[args.index('--') + 1:]
IMPORT = re.compile(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([A-Za-z0-9_.]+)')

def find(mod):
    for r in roots:
        p = os.path.join(r, *mod.split('.')) + '.lean'
        if os.path.isfile(p):
            return r, p
    return None

def imports(path):
    """the modules named by the import lines at the top of a Lean file"""
    found, in_comment = [], False
    with open(path, encoding='utf-8') as f:
        for line in f:
            s = line.strip()
            if in_comment:
                in_comment = '-/' not in s
                continue
            if not s or s.startswith('--') or s in ('module', 'prelude'):
                continue
            if s.startswith('/-'):
                in_comment = '-/' not in s
                continue
            m = IMPORT.match(s)
            if not m:
                break                      # the first line that is not an import ends the header
            found.append(m.group(1))
    return found

info, order = {}, []                       # module -> (level, root, source, stamp)
def visit(mod, chain=()):
    if mod in info:
        return info[mod]
    if mod in chain:
        sys.exit('order.py: import cycle through ' + mod)
    where = find(mod)
    if where is None:
        return None
    root, path = where
    level, h = 0, hashlib.sha256()
    with open(path, 'rb') as f:
        h.update(f.read())
    for imp in imports(path):
        got = visit(imp, chain + (mod,))
        if got is not None:
            level = max(level, got[0] + 1)
            h.update(b'\n' + imp.encode() + b' ' + got[3].encode())
    info[mod] = (level, root, path, h.hexdigest())
    order.append(mod)
    return info[mod]

sys.setrecursionlimit(100000)
for t in targets:
    if visit(t) is None:
        sys.exit('order.py: no source for the target module %s under %s' % (t, ', '.join(roots)))
sys.stdout.reconfigure(newline='\n')                         # the same line ends on every system
for mod in sorted(order, key=lambda m: info[m][0]):          # stable: keeps dependency order inside a level
    level, root, path, stamp = info[mod]
    print('%d\t%s\t%s\t%s\t%s' % (level, mod, root.replace(os.sep, '/'), path.replace(os.sep, '/'), stamp))
