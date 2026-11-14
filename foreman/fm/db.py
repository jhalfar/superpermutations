"""SQLite state of foreman (one file, foreman.db next to foreman.py).

cases    one row per search target (n, base, start plan, target length if it is a benchmark)
plans    the shared plan store: SHA-256 of the plan text, length, how it was made (parent plan, arm, rung, variant)
runs     every job: arm, rung, variant, resources, times, lengths in and out, gain, status
memo     (plan, arm, rung, variant) -> run, gain: a 0 is never run again on the same plan
events   the event log (new best, rung climb, fixed point, pause, errors)
samples  the anytime curve: best length against elapsed wall hours and CPU hours
sched    snapshots of the scheduler (threads used, the job on the GPU, RAM, pause reason)
"""
import json
import os
import sqlite3
import time

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DB = os.path.join(HERE, "foreman.db")

SCHEMA = """
CREATE TABLE IF NOT EXISTS cases (name TEXT PRIMARY KEY, n INT, base TEXT, base_tsv TEXT, start_sha TEXT,
  target INT, created REAL, config TEXT, state TEXT DEFAULT 'idle');
CREATE TABLE IF NOT EXISTS plans (sha TEXT, case_name TEXT, n INT, path TEXT, base TEXT, length INT,
  parent TEXT, arm TEXT, rung INT, variant TEXT, ts REAL, note TEXT, PRIMARY KEY (sha, case_name));
CREATE TABLE IF NOT EXISTS runs (id INTEGER PRIMARY KEY, case_name TEXT, plan_sha TEXT, arm TEXT, rung INT,
  variant TEXT, setting TEXT, threads INT, gpu INT, gb INT, status TEXT, t_start REAL, t_end REAL, wall_s REAL,
  susp_s REAL DEFAULT 0, cpu_h REAL, gpu_h REAL, len_in INT, len_out INT, gain INT, out_sha TEXT, dir TEXT, pid INT,
  early INT DEFAULT 0, note TEXT);
CREATE TABLE IF NOT EXISTS memo (plan_sha TEXT, arm TEXT, rung INT, variant TEXT, run_id INT, gain INT,
  PRIMARY KEY (plan_sha, arm, rung, variant));
CREATE TABLE IF NOT EXISTS events (ts REAL, case_name TEXT, kind TEXT, text TEXT);
CREATE TABLE IF NOT EXISTS samples (ts REAL, case_name TEXT, wall_h REAL, cpu_h REAL, best INT);
CREATE TABLE IF NOT EXISTS sched (ts REAL, threads_used INT, threads_cap INT, gpu_job TEXT, ram_total REAL,
  ram_avail REAL, gb_used INT, running INT, paused TEXT);
CREATE INDEX IF NOT EXISTS runs_case ON runs (case_name, status);
CREATE INDEX IF NOT EXISTS plans_case ON plans (case_name, length);
"""


def connect(path=DB):
    c = sqlite3.connect(path, timeout=60, isolation_level=None)      # autocommit; one writer (the scheduler)
    c.row_factory = sqlite3.Row
    c.execute("PRAGMA journal_mode=WAL")
    c.executescript(SCHEMA)
    return c


def event(c, case, kind, text):
    c.execute("INSERT INTO events VALUES (?,?,?,?)", (time.time(), case, kind, text))


def best_plan(c, case):
    return c.execute("SELECT * FROM plans WHERE case_name=? ORDER BY length, ts LIMIT 1", (case,)).fetchone()


def population(c, case, k, extra_bases=2, slack=3, explorers=2):
    """the k shortest distinct plans of a case (ties: newest first, so fresh plans of equal length get a turn), plus
    the best plan of up to extra_bases other bases within slack letters of the best (diversity for walks over
    selections: a flipped selection starts a few letters longer)."""
    rows = c.execute("SELECT * FROM plans WHERE case_name=? ORDER BY length, ts DESC", (case,)).fetchall()
    pop = rows[:k]
    if not pop:
        return pop
    bases = {r["base"] for r in pop}
    for r in rows[k:]:
        if len(pop) >= k + extra_bases or r["length"] > pop[0]["length"] + slack:
            break
        if r["base"] not in bases:
            pop.append(r)
            bases.add(r["base"])
    # explorers: the newest plans kept by late acceptance (note "explorer ..."), at most `explorers` of them,
    # within slack letters of the best; they sit a few letters above the best and are searched like the others
    have = {r["sha"] for r in pop}
    ex = [r for r in sorted(rows, key=lambda r: -r["ts"]) if (r["note"] or "").startswith("explorer")
          and r["sha"] not in have and r["length"] <= pop[0]["length"] + slack][:explorers]
    return pop + ex


def memo_get(c, sha, arm, rung, variant):
    return c.execute("SELECT * FROM memo WHERE plan_sha=? AND arm=? AND rung=? AND variant=?",
                     (sha, arm, rung, variant)).fetchone()


def memo_put(c, sha, arm, rung, variant, run_id, gain):
    c.execute("INSERT OR REPLACE INTO memo VALUES (?,?,?,?,?,?)", (sha, arm, rung, variant, run_id, gain))


def case_row(c, name):
    r = c.execute("SELECT * FROM cases WHERE name=?", (name,)).fetchone()
    if r is None:
        raise SystemExit("no case %s" % name)
    return r


def config(row):
    return json.loads(row["config"] or "{}")
