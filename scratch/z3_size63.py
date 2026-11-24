#!/usr/bin/env python3
"""Z3 search for a size-63 monotone fan-in-2 circuit that is arc-correct on PG(2,3).

Template: free circuit with exactly M gates; each gate AND/OR of two earlier wires.
Constraints: completeness on 52 edges; soundness on a covering set of critical
edge-free arcs (all arcs with line-mask in a selected family).
"""
from __future__ import annotations

import sys
import time
from itertools import combinations

from z3 import And, Bool, BoolVal, If, Int, Or, Solver, Sum, sat, unsat

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [frozenset((w + d) % N for d in DIFF) for w in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]


def is_arc(pmask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if pmask & (1 << p)) > 2:
            return False
    return True


def has_edge(pmask: int, lmask: int) -> bool:
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def critical_negatives():
    """Edge-free arc inputs that are minimal-ish: 
    - no lines, any arc points
    - one line, arc points disjoint from that line
    - two lines, etc. Focus on hardest small cases.
    """
    negs = []
    # all arcs with no lines
    for pmask in range(1 << N):
        if is_arc(pmask) and pmask != 0:
            negs.append((pmask, 0))
    # single line + arc in the complement (points off the line, still an arc)
    for w in range(N):
        off = [p for p in range(N) if p not in LINE_PTS[w]]
        # subsets of off with size <=5 that remain arcs globally
        for r in range(1, 4):
            for pts in combinations(off, r):
                pmask = 0
                for p in pts:
                    pmask |= 1 << p
                if is_arc(pmask) and not has_edge(pmask, 1 << w):
                    negs.append((pmask, 1 << w))
    # dedupe
    return list(dict.fromkeys(negs))


def synthesize(M: int = 63, time_limit: float = 120.0) -> bool:
    negs = critical_negatives()
    print(f"M={M} edges={len(EDGES)} neg_tests={len(negs)}", flush=True)
    s = Solver()
    s.set("timeout", int(time_limit * 1000))

    # Gate i in 0..M-1: is_and[i], in1[i], in2[i] in 0..V+i-1
    is_and = [Bool(f"and_{i}") for i in range(M)]
    in1 = [Int(f"in1_{i}") for i in range(M)]
    in2 = [Int(f"in2_{i}") for i in range(M)]
    for i in range(M):
        s.add(in1[i] >= 0, in1[i] < V + i)
        s.add(in2[i] >= 0, in2[i] < V + i)

    out_wire = Int("out")
    s.add(out_wire >= 0, out_wire < V + M)

    def eval_on(x_bits):
        """x_bits: list of length V of Z3 BoolRefs or Python bools."""
        wires = list(x_bits)
        for i in range(M):
            # pick inputs via brute mux — only feasible for small; use If chain
            a = BoolVal(False)
            b = BoolVal(False)
            # Build selectors: for each possible wire j < V+i
            av = BoolVal(False)
            bv = BoolVal(False)
            for j in range(V + i):
                av = If(in1[i] == j, wires[j], av)
                bv = If(in2[i] == j, wires[j], bv)
            wi = If(is_and[i], And(av, bv), Or(av, bv))
            wires.append(wi)
        # output mux
        o = BoolVal(False)
        for j in range(V + M):
            o = If(out_wire == j, wires[j], o)
        return o

    # Completeness
    for ei, (p, w) in enumerate(EDGES):
        x = [BoolVal(False) for _ in range(V)]
        x[p] = BoolVal(True)
        x[N + w] = BoolVal(True)
        s.add(eval_on(x) == True)

    # Soundness on negatives (may be many — subsample if needed)
    # Prioritize: first all no-line arcs with <=3 points, then sample
    small_negs = [(pm, lm) for pm, lm in negs if lm == 0 and bin(pm).count("1") <= 3]
    other = [t for t in negs if t not in small_negs]
    import random
    random.seed(0)
    random.shuffle(other)
    use = small_negs + other[:200]
    print(f"using {len(use)} negative constraints", flush=True)
    for pi, (pmask, lmask) in enumerate(use):
        x = []
        for p in range(N):
            x.append(BoolVal(bool(pmask & (1 << p))))
        for w in range(N):
            x.append(BoolVal(bool(lmask & (1 << w))))
        s.add(eval_on(x) == False)

    print("solving...", flush=True)
    t0 = time.time()
    r = s.check()
    print("result", r, "in", round(time.time() - t0, 2), "s", flush=True)
    if r == sat:
        m = s.model()
        print("SAT witness out", m[out_wire])
        for i in range(M):
            print(i, "AND" if m[is_and[i]] else "OR", m[in1[i]], m[in2[i]])
        return True
    return False


if __name__ == "__main__":
    M = int(sys.argv[1]) if len(sys.argv) > 1 else 63
    ok = synthesize(M, time_limit=float(sys.argv[2]) if len(sys.argv) > 2 else 90)
    sys.exit(0 if ok else 1)
