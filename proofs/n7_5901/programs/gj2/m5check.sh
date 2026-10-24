#!/bin/bash
# m5check.sh TAG - referee point M5: the statement line (first line) of every part file of a tag must be the same
# apart from the part numbers; prints the distinct lines and the number of files.
cd "$(dirname "$0")"
n=$(ls parts/$1 | grep -c '^p[0-9_]*\.txt$')
for f in parts/$1/p*.txt; do head -1 $f | sed -E 's/PART=[0-9]+\//PART=*\//; s/PART2=[0-9]+\//PART2=*\//'; done | sort | uniq -c > parts/$1/m5.txt
echo "$1: files $n, distinct statement lines $(wc -l < parts/$1/m5.txt)"; cut -c1-330 parts/$1/m5.txt
