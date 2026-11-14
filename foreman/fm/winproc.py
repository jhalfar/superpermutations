"""Process helpers for foreman (standard library only): Windows through ctypes, Linux through /proc and signals.

proc_table()            -> {pid: (ppid, exe name)} of all processes
tree(pid)               -> pid and all its descendants (by parent pid; foreman starts every job, so the tree is ours)
suspend(pids) / resume(pids) / kill(pids)
mem_status()            -> (total GB, available GB)
cpu_busy()              -> fraction of all cores busy since the previous call
"""
import os
import sys

WIN = sys.platform == "win32"


def tree(pid, table=None):
    table = table or proc_table()
    kids = {}
    for p, (pp, _) in table.items():
        kids.setdefault(pp, []).append(p)
    out, stack = [], [pid]
    while stack:
        p = stack.pop()
        if p in out or (p != pid and p not in table):
            continue
        out.append(p)
        stack.extend(k for k in kids.get(p, []) if k != p)
    return out


_last = None

if WIN:
    import ctypes
    import ctypes.wintypes as wt

    k32 = ctypes.WinDLL("kernel32", use_last_error=True)
    ntdll = ctypes.WinDLL("ntdll")

    TH32CS_SNAPPROCESS = 0x2
    PROCESS_SUSPEND_RESUME = 0x0800
    PROCESS_TERMINATE = 0x0001

    class PROCESSENTRY32W(ctypes.Structure):
        _fields_ = [("dwSize", wt.DWORD), ("cntUsage", wt.DWORD), ("th32ProcessID", wt.DWORD),
                    ("th32DefaultHeapID", ctypes.c_size_t), ("th32ModuleID", wt.DWORD), ("cntThreads", wt.DWORD),
                    ("th32ParentProcessID", wt.DWORD), ("pcPriClassBase", ctypes.c_long), ("dwFlags", wt.DWORD),
                    ("szExeFile", ctypes.c_wchar * 260)]

    class MEMORYSTATUSEX(ctypes.Structure):
        _fields_ = [("dwLength", wt.DWORD), ("dwMemoryLoad", wt.DWORD), ("ullTotalPhys", ctypes.c_uint64),
                    ("ullAvailPhys", ctypes.c_uint64), ("ullTotalPageFile", ctypes.c_uint64),
                    ("ullAvailPageFile", ctypes.c_uint64), ("ullTotalVirtual", ctypes.c_uint64),
                    ("ullAvailVirtual", ctypes.c_uint64), ("ullAvailExtendedVirtual", ctypes.c_uint64)]

    k32.CreateToolhelp32Snapshot.restype = wt.HANDLE
    k32.OpenProcess.restype = wt.HANDLE

    def proc_table():
        snap = k32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
        out = {}
        e = PROCESSENTRY32W()
        e.dwSize = ctypes.sizeof(PROCESSENTRY32W)
        ok = k32.Process32FirstW(snap, ctypes.byref(e))
        while ok:
            out[e.th32ProcessID] = (e.th32ParentProcessID, e.szExeFile)
            ok = k32.Process32NextW(snap, ctypes.byref(e))
        k32.CloseHandle(snap)
        return out

    def _each(pids, access, fn):
        n = 0
        for p in pids:
            h = k32.OpenProcess(access, False, p)
            if not h:
                continue
            fn(h)
            n += 1
            k32.CloseHandle(h)
        return n

    def suspend(pids):
        return _each(pids, PROCESS_SUSPEND_RESUME, ntdll.NtSuspendProcess)

    def resume(pids):
        return _each(pids, PROCESS_SUSPEND_RESUME, ntdll.NtResumeProcess)

    def kill(pids):
        return _each(pids, PROCESS_TERMINATE, lambda h: k32.TerminateProcess(h, 1))

    def mem_status():
        m = MEMORYSTATUSEX()
        m.dwLength = ctypes.sizeof(MEMORYSTATUSEX)
        k32.GlobalMemoryStatusEx(ctypes.byref(m))
        return m.ullTotalPhys / 2 ** 30, m.ullAvailPhys / 2 ** 30

    def cpu_busy():
        global _last
        idle, kern, user = wt.FILETIME(), wt.FILETIME(), wt.FILETIME()
        k32.GetSystemTimes(ctypes.byref(idle), ctypes.byref(kern), ctypes.byref(user))
        v = [(f.dwHighDateTime << 32) | f.dwLowDateTime for f in (idle, kern, user)]
        if _last is None:
            _last = v
            return 0.0
        di, dk, du = (a - b for a, b in zip(v, _last))
        _last = v
        tot = dk + du                      # kernel time includes idle time
        return 0.0 if tot <= 0 else max(0.0, min(1.0, 1 - di / tot))

else:
    import signal

    def proc_table():
        out = {}
        for d in os.listdir("/proc"):
            if not d.isdigit():
                continue
            try:
                with open("/proc/%s/stat" % d) as f:
                    st = f.read()
                name = st[st.index("(") + 1:st.rindex(")")]
                ppid = int(st[st.rindex(")") + 2:].split()[1])
                out[int(d)] = (ppid, name)
            except (OSError, ValueError):
                pass
        return out

    def _sig(pids, s):
        n = 0
        for p in pids:
            try:
                os.kill(p, s)
                n += 1
            except OSError:
                pass
        return n

    def suspend(pids):
        return _sig(pids, signal.SIGSTOP)

    def resume(pids):
        return _sig(pids, signal.SIGCONT)

    def kill(pids):
        return _sig(pids, signal.SIGKILL)

    def mem_status():
        info = {}
        with open("/proc/meminfo") as f:
            for line in f:
                k, v = line.split(":", 1)
                info[k] = int(v.split()[0]) * 1024
        return info["MemTotal"] / 2 ** 30, info.get("MemAvailable", info["MemFree"]) / 2 ** 30

    def cpu_busy():
        global _last
        with open("/proc/stat") as f:
            v = [int(x) for x in f.readline().split()[1:]]
        idle, tot = v[3] + (v[4] if len(v) > 4 else 0), sum(v)
        if _last is None:
            _last = (idle, tot)
            return 0.0
        di, dt = idle - _last[0], tot - _last[1]
        _last = (idle, tot)
        return 0.0 if dt <= 0 else max(0.0, min(1.0, 1 - di / dt))
