#!/bin/bash
# m5check.sh TAG - referee point M5 for a tag of kparts.sh: the statement line (first line) of every part file must be the
# same apart from the part number and the counts of the part: statement, levels, CUT, potential, JS, checksum of the table,
# number of parts, gate depth, kept above the gate, number of gate prefixes.  ("rows placed" above the gate is left out: the
# host subtracts the gate prefixes of the part from it, so it differs by a few units from part to part, as in gk4.exe.)
# Must print "distinct statement lines 1".
cd "$(dirname "$0")"
n=$(ls parts/$1 | grep -c '^p[0-9]*\.txt$')
for f in parts/$1/p[0-9]*.txt; do head -1 $f | sed -E 's/ part [0-9]+ of / part * of /; s/: violations [0-9]+ +rows placed [0-9]+ +kept [0-9]+ +above the gate: rows placed [0-9]+ kept/: above the gate: kept/; s/ \(this part [0-9]+\)//'; done | sort | uniq -c > parts/$1/m5.txt
echo "$1: files $n, distinct statement lines $(wc -l < parts/$1/m5.txt)"; cut -c1-330 parts/$1/m5.txt
