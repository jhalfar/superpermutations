"""Compare files with a list of SHA-256 hashes, or write such a list.

    check_hashes.py LIST DIR                  every file named in LIST exists under DIR with the listed hash
    check_hashes.py --write DIR FILE...       print the list for these files (paths relative to DIR)

A line of LIST is "<hash>  <path>", as sha256sum prints it.  One difference from sha256sum: a file is hashed
with Windows line ends (CR LF) turned into LF, so that a checkout made on Windows and one made on Linux give
the same hashes.  For a text file with LF line ends the hash is the one sha256sum prints.
"""
import hashlib, os, sys

def file_hash(path):
    with open(path, 'rb') as f:
        return hashlib.sha256(f.read().replace(b'\r\n', b'\n')).hexdigest()

if len(sys.argv) >= 3 and sys.argv[1] == '--write':
    sys.stdout.reconfigure(newline='\n')
    for rel in sys.argv[3:]:
        print('%s  %s' % (file_hash(os.path.join(sys.argv[2], rel)), rel.replace(os.sep, '/')))
    sys.exit(0)
if len(sys.argv) != 3:
    sys.exit(__doc__)
bad = 0
with open(sys.argv[1], encoding='utf-8') as f:
    for line in f:
        if not line.strip():
            continue
        want, rel = line.rstrip('\r\n').split('  ', 1)
        path = os.path.join(sys.argv[2], rel)
        if not os.path.isfile(path):
            print('missing: ' + rel); bad += 1
        elif file_hash(path) != want:
            print('different: ' + rel); bad += 1
if bad:
    sys.exit('%d of the files listed in %s are missing or different under %s' % (bad, sys.argv[1], sys.argv[2]))
