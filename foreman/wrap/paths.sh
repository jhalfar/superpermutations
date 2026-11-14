# paths.sh: sourced by the wrappers (". paths.sh").  foreman's scheduler exports FM_ROOT, FM_BIN and FM_PYTHON
# (fm/config.py, config.json); a wrapper run by hand falls back to the layout of the repository: foreman/wrap/ ->
# root = ../.., the tools in root/tools and its folders gpucuts/, reorder/, pipeline/, prepub/.
R=${FM_ROOT:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}
T=${FM_BIN:-$R/tools}
PYX=${FM_PYTHON:-python}
FMW=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)            # the wrappers
GC=$T/gpucuts; RO=$T/reorder; PL=$T/pipeline; PP=$T/prepub
exe() { local d=$T n=$1; [ $# -ge 2 ] && { d=$1; n=$2; }       # exe NAME (in tools/) or exe DIR NAME
        if [ -f "$d/$n.exe" ]; then echo "$d/$n.exe"; else echo "$d/$n"; fi; }   # NAME.exe on Windows
