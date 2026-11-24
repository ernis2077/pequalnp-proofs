#!/usr/bin/env python3
"""L-meta-651 shard 3 search: first gate NOT of an input, size <= 19.

Aut-pruned: gate 0 = NOT(0). Subcase: remaining gates AND/OR only; gate 1 consumes
NOT(0) with an input from {neighbor orbit rep 1, dist-2 orbit rep 2}.

Size exactly S with output = last wire covers size <= S by padding.
CEGAR on wt<=2 then all counterexamples.

Exit: 0 sat/witness, 1 all listed cases unsat, 2 timeout
"""
from __future__ import annotations

import argparse
import hashlib
import sys
import time
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

from pysat.solvers import Cadical195

EDGES = [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
]
N = 10
M = 1 << N
T = [int(any(((m >> a) & 1) and ((m >> b) & 1) for a, b in EDGES)) for m in range(M)]


def run_case(args):
    S, op1, partner, wall = args
    tag = f"S={S} {op1} p={partner}"
    v = 0

    def new():
        nonlocal v
        v += 1
        return v

    s = Cadical195()
    is_and, is_or, left, right = [], [], [], []
    for g in range(1, S):
        a, o = new(), new()
        is_and.append(a)
        is_or.append(o)
        s.add_clause([a, o])
        s.add_clause([-a, -o])
        nw = N + g
        L = [new() for _ in range(nw)]
        R = [new() for _ in range(nw)]
        left.append(L)
        right.append(R)
        s.add_clause(L)
        s.add_clause(R)
        for i in range(nw):
            for j in range(i + 1, nw):
                s.add_clause([-L[i], -L[j]])
                s.add_clause([-R[i], -R[j]])
        for i in range(nw):
            for j in range(i):
                s.add_clause([-a, -L[i], -R[j]])
                s.add_clause([-o, -L[i], -R[j]])
    s.add_clause([is_and[0] if op1 == "and" else is_or[0]])
    s.add_clause([left[0][partner]])
    s.add_clause([right[0][N]])

    active: set[int] = set()

    def add_mask(m: int) -> None:
        if m in active:
            return
        active.add(m)
        wvals: list = [bool((m >> i) & 1) for i in range(N)]
        wvals.append(not ((m >> 0) & 1))
        for gi, g in enumerate(range(1, S)):
            vg = new()
            a, o = is_and[gi], is_or[gi]
            L, R = left[gi], right[gi]
            nw = N + g
            la, ra = new(), new()
            for i in range(nw):
                wi = wvals[i]
                if isinstance(wi, bool):
                    s.add_clause([-L[i], la] if wi else [-L[i], -la])
                    s.add_clause([-R[i], ra] if wi else [-R[i], -ra])
                else:
                    s.add_clause([-L[i], -la, wi])
                    s.add_clause([-L[i], la, -wi])
                    s.add_clause([-R[i], -ra, wi])
                    s.add_clause([-R[i], ra, -wi])
            s.add_clause([-a, -la, -ra, vg])
            s.add_clause([-a, la, -vg])
            s.add_clause([-a, ra, -vg])
            s.add_clause([-o, la, ra, -vg])
            s.add_clause([-o, -la, vg])
            s.add_clause([-o, -ra, vg])
            wvals.append(vg)
        s.add_clause([wvals[-1]] if T[m] else [-wvals[-1]])

    for m in range(M):
        if m.bit_count() <= 2:
            add_mask(m)

    t0 = time.time()
    rnd = 0
    status = "timeout"
    circ = None
    print(f"{tag} start vars={v} masks={len(active)}", flush=True)
    try:
        while time.time() - t0 < wall:
            rnd += 1
            t1 = time.time()
            sat = s.solve()
            print(
                f"{tag} rnd={rnd} sat={sat} {time.time()-t1:.1f}s "
                f"active={len(active)} total={time.time()-t0:.1f}s",
                flush=True,
            )
            if sat is False:
                status = "unsat"
                break
            if sat is not True:
                status = "timeout"
                break
            model = set(s.get_model())
            circ = [("not", 0)]
            for gi, g in enumerate(range(1, S)):
                li = next(i for i in range(N + g) if left[gi][i] in model)
                ri = next(i for i in range(N + g) if right[gi][i] in model)
                circ.append(("and" if is_and[gi] in model else "or", li, ri))
            cex = []
            for m in range(M):
                w = [(m >> i) & 1 for i in range(N)]
                w.append(1 - w[0])
                for op, *ins in circ[1:]:
                    w.append(
                        w[ins[0]] & w[ins[1]]
                        if op == "and"
                        else w[ins[0]] | w[ins[1]]
                    )
                if w[-1] != T[m]:
                    cex.append(m)
            print(f"{tag} cex={len(cex)}", flush=True)
            if not cex:
                status = "sat"
                break
            for m in cex:
                add_mask(m)
    finally:
        s.delete()
    print(f"RESULT {tag} {status} {time.time()-t0:.1f}s", flush=True)
    return (S, op1, partner, status, circ)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--size", type=int, default=19)
    ap.add_argument("--wall", type=float, default=3600)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--sha-only", action="store_true")
    args = ap.parse_args()
    path = Path(__file__).resolve()
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(f"program={path}", flush=True)
    print(f"sha256={digest}", flush=True)
    if args.sha_only:
        return 0

    cases = [
        (args.size, op, p, args.wall)
        for op in ("and", "or")
        for p in (1, 2)
    ]
    print(f"cases={cases}", flush=True)
    results = []
    with ProcessPoolExecutor(max_workers=args.jobs) as ex:
        futs = [ex.submit(run_case, c) for c in cases]
        for fut in as_completed(futs):
            r = fut.result()
            results.append(r)
            if r[3] == "sat":
                print("WITNESS", r, flush=True)
                # cancel others by shutdown
                return 0
    print("ALL_RESULTS", results, flush=True)
    if results and all(r[3] == "unsat" for r in results):
        print("EXHAUSTED early-consumer AND/OR-rest cases", flush=True)
        return 1
    return 2


if __name__ == "__main__":
    sys.exit(main())
