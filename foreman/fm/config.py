"""Foreman's configuration: the repository root and every tool and directory foreman uses.

The root is the folder above foreman's own folder (the root of the repository), unless config.json sets "root".  Paths
come from config.json next to foreman.py (a template is config.example.json); a relative path is taken relative to the
root.  Nothing machine-specific is written in the code.

    from fm.config import ROOT, P     # P("bin") -> absolute path of the "bin" entry
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

DEFAULTS = {
    "root": "",                                    # "" = the folder above foreman's folder
    "python": "",                                  # "" = the Python that runs foreman
    "guard": "",                                   # optional memory guard: a script run as  python GUARD --gb G -- CMD
    "bash": "bash",                                # bash for the wrapper scripts (on Windows: Git's usr/bin/bash.exe)
    "bin": "tools",                                # the built tools: trailsearch, recut, relocate, segins, gpucuts/tsw5g2,
                                                   # segins_ils, loopscan, recut_wide, delcheck (+ polish.sh)
    "work": "foreman/work",                        # work files of the runs (an n = 12 word is 523 MB)
    "on_record": "",                               # optional command run as  CMD LENGTH WORD PLAN  for a verified word
                                                   # below a case's --report-below ("" = nothing; run --on-record CMD)
    # search programs of other users that occupy the card (substrings of the exe path): then foreman's GPU arm waits
    "gpu_exe": ["tsw5g2", "segins_gpu", "trailsearch_gpu"],
    "threads_cap": 12,
    "reserve_gb": 8,
}


def _load():
    c = dict(DEFAULTS)
    p = os.path.join(HERE, "config.json")
    if os.path.exists(p):
        c.update(json.load(open(p)))
    return c


C = _load()
ROOT = os.path.abspath(C["root"]) if C["root"] else os.path.dirname(HERE)

PATH_KEYS = ["python", "guard", "bash", "bin", "work"]


def P(key):
    """absolute path of a path entry ("" stays "", a bare command name like "bash" stays as it is)."""
    v = C[key]
    if not v or ("/" not in v and "\\" not in v):
        return v
    return v if os.path.isabs(v) else os.path.normpath(os.path.join(ROOT, v))


def live(key):
    """the current value of a key (config.json read again: lists like gpu_exe change without a restart)"""
    return _load()[key]


def env():
    """FM_ROOT and FM_<KEY> for every path entry: the wrappers (wrap/paths.sh) read their tools from these."""
    e = {"FM_ROOT": ROOT.replace("\\", "/"), "FM_PYTHON": (P("python") or sys.executable).replace("\\", "/")}
    for k in PATH_KEYS:
        if P(k):
            e["FM_" + k.upper()] = P(k).replace("\\", "/")
    return e
