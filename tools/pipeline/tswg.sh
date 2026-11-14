#!/bin/bash
# tswg.sh ARGS...: tsw5g2 with the memory guard GUARD in front (orx.sh runs its TSW as it is; pass TSW=this script).
# TOOLS = directory of the binaries (default: the directory of this script); GUARD as in loop.sh (default: none).
B=${TOOLS:-$(cd "$(dirname "$0")" && pwd)}
exec ${GUARD-} $B/tsw5g2 "$@"
