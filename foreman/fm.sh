#!/bin/bash
# fm.sh ARGS: runs foreman.py in isolated mode (set PYTHON to choose the interpreter), e.g. bash foreman/fm.sh status
H=$(cd "$(dirname "$0")" && pwd)
exec "${PYTHON:-python}" -I "$H/foreman.py" "$@"
