#!/usr/bin/env python3
"""Runs a solver on SMT-LIB benchmarks and checks its answers and models.

Usage: eval.py SOLVER Z3 OUT.csv [--timeout S] [--jobs J] [--mem GB] FILE_OR_DIR...

For every .smt2 file (directories are searched recursively): the solver gets the script with
`(exit)` removed and `(get-model)` appended, under a wall-clock limit and an address-space limit.
Its answer is compared with the `:status` of the file. For `sat`, the model is checked with z3:
the declarations of the file are replaced by the model's definitions (abstract values
`(as @x S)` become distinct new constants of sort S) and z3 must find the assertions satisfiable.

OUT.csv gets one row per file: file, status, answer, seconds, model (ok / bad / unchecked / -).
`crash` is an answer with no output (the solver aborted, for example out of memory); `error` is
any other output that is not sat/unsat/unknown. The summary at the end counts the answers, the wrong answers (contradicting the status) and the
bad models.
"""
import argparse
import concurrent.futures
import csv
import os
import re
import resource
import subprocess
import sys
import time


def commands(text):
    """The top-level s-expressions of an SMT-LIB script (comments, strings, quoted symbols aware)."""
    out, depth, start, i, n = [], 0, None, 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] not in "\n\r":
                i += 1
            continue
        if c == '"':
            i += 1
            while i < n:
                if text[i] == '"':
                    if i + 1 < n and text[i + 1] == '"':
                        i += 2
                        continue
                    break
                i += 1
        elif c == "|":
            i += 1
            while i < n and text[i] != "|":
                i += 1
        elif c == "(":
            if depth == 0:
                start = i
            depth += 1
        elif c == ")":
            depth -= 1
            if depth == 0:
                out.append(text[start:i + 1])
        i += 1
    return out


def head(cmd):
    m = re.match(r"\(\s*([^\s()]+)", cmd)
    return m.group(1) if m else ""


def status_of(cmds):
    for c in cmds:
        m = re.match(r"\(\s*set-info\s+:status\s+(sat|unsat|unknown)\s*\)", c)
        if m:
            return m.group(1)
    return "unknown"


def limit(mem_gb):
    def f():
        b = int(mem_gb * 2**30)
        resource.setrlimit(resource.RLIMIT_AS, (b, b))
    return f


def model_script(cmds, model):
    """The script that checks `model` (a get-model response) against the assertions of `cmds`."""
    values = sorted(set(re.findall(r"\(as (@[^\s()]+) ([^\s()]+|\|[^|]*\|)\)", model)))
    body = model
    names = {}
    for k, (v, s) in enumerate(values):
        names[(v, s)] = "|model value %d|" % k
        body = body.replace("(as %s %s)" % (v, s), names[(v, s)])
    defs = commands(body.strip()[1:-1]) if body.strip().startswith("(") else []
    out, placed = [], False
    for c in cmds:
        h = head(c)
        if h in ("declare-fun", "declare-const"):
            if not placed:
                for s in sorted({s for _, s in values}):
                    group = [names[x] for x in values if x[1] == s]
                    out += ["(declare-const %s %s)" % (g, s) for g in group]
                    if len(group) > 1:
                        out.append("(assert (distinct %s))" % " ".join(group))
                out += defs
                placed = True
            continue
        if h in ("check-sat", "exit", "get-model", "set-option", "set-info"):
            continue
        out.append(c)
    if not placed:
        out += defs
    return "\n".join(out + ["(check-sat)"])


def run_one(solver, z3, path, timeout, mem):
    text = open(path, encoding="latin-1").read()
    cmds = commands(text)
    status = status_of(cmds)
    script = "\n".join(c for c in cmds if head(c) != "exit") + "\n(get-model)\n"
    t0 = time.time()
    try:
        r = subprocess.run([solver], input=script.encode("latin-1"), capture_output=True,
                           timeout=timeout, preexec_fn=limit(mem))
        out = r.stdout.decode("latin-1")
        # No output at all: the solver crashed (for example, out of memory).
        answer = out.split("\n", 1)[0].strip() or "crash"
    except subprocess.TimeoutExpired:
        out, answer = "", "timeout"
    secs = time.time() - t0
    model = "-"
    if answer == "sat":
        resp = out.split("\n", 1)[1] if "\n" in out else ""
        try:
            chk = subprocess.run([z3, "-in", "-T:%d" % max(60, int(timeout))], input=model_script(cmds, resp).encode("latin-1"),
                                 capture_output=True, timeout=max(90, timeout + 30))
            res = chk.stdout.decode("latin-1").strip().split("\n")[-1]
            model = "ok" if res == "sat" else ("bad" if res == "unsat" else "unchecked")
        except subprocess.TimeoutExpired:
            model = "unchecked"
    elif answer not in ("unsat", "unknown", "timeout", "crash"):
        answer = "error"
    return path, status, answer, "%.2f" % secs, model


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("solver")
    ap.add_argument("z3")
    ap.add_argument("out")
    ap.add_argument("paths", nargs="+")
    ap.add_argument("--timeout", type=float, default=60)
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--mem", type=float, default=8)
    a = ap.parse_args()
    files = []
    for p in a.paths:
        if os.path.isdir(p):
            for root, _, fs in os.walk(p):
                files += [os.path.join(root, f) for f in fs if f.endswith(".smt2")]
        else:
            files.append(p)
    files.sort()
    counts, wrong, bad = {}, [], []
    with open(a.out, "w", newline="") as f, concurrent.futures.ThreadPoolExecutor(a.jobs) as ex:
        w = csv.writer(f)
        w.writerow(["file", "status", "answer", "seconds", "model"])
        for row in ex.map(lambda p: run_one(a.solver, a.z3, p, a.timeout, a.mem), files):
            w.writerow(row)
            f.flush()
            _, status, answer, _, model = row
            counts[answer] = counts.get(answer, 0) + 1
            if answer in ("sat", "unsat") and status in ("sat", "unsat") and answer != status:
                wrong.append(row[0])
            if model == "bad":
                bad.append(row[0])
    print("files %d: %s" % (len(files), ", ".join("%s %d" % kv for kv in sorted(counts.items()))))
    print("wrong answers %d, bad models %d" % (len(wrong), len(bad)))
    for x in wrong:
        print("WRONG", x)
    for x in bad:
        print("BAD MODEL", x)


if __name__ == "__main__":
    main()
