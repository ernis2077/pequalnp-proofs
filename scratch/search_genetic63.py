#!/usr/bin/env python3
"""Genetic / MCMC search for size<=63 arc-correct incidence circuits.
Starts from the size-64 cover and mutates, allowing unclean gates."""
from __future__ import annotations

import random
import sys
import time
from typing import List, Optional, Tuple

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [tuple(sorted((w + d) % N for d in DIFF)) for w in range(N)]
PT_LINES = [tuple(sorted(w for w in range(N) if p in LINE_PTS[w])) for p in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]
Gate = Tuple[str, Tuple[int, ...]]


def is_arc(mask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if mask & (1 << p)) > 2:
            return False
    return True


ARCS = [m for m in range(1 << N) if is_arc(m)]


def eval_out(gates: List[Gate], out: int, xbits: List[bool]) -> bool:
    w = list(xbits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        if op == "and":
            w.append(all(vals) if vals else True)
        else:
            w.append(any(vals) if vals else False)
    return bool(w[out]) if out < len(w) else False


def pack(pmask: int, lmask: int) -> List[bool]:
    x = [False] * V
    for p in range(N):
        x[p] = bool(pmask & (1 << p))
    for i in range(N):
        x[N + i] = bool(lmask & (1 << i))
    return x


def has_edge(pmask: int, lmask: int) -> bool:
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def cover_lines() -> Tuple[List[Gate], int]:
    gates: List[Gate] = []
    ands = []
    for w in range(N):
        pts = LINE_PTS[w]
        gates.append(("or", (pts[0], pts[1])))
        a = V + len(gates) - 1
        gates.append(("or", (pts[2], pts[3])))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (N + w, o)))
        ands.append(V + len(gates) - 1)
    cur = list(ands)
    while len(cur) > 1:
        nxt = []
        it = iter(cur)
        for a in it:
            try:
                b = next(it)
            except StopIteration:
                nxt.append(a)
                break
            gates.append(("or", (a, b)))
            nxt.append(V + len(gates) - 1)
        cur = nxt
    return gates, cur[0]


# Precompute edge inputs and a pool of arc test cases
EDGE_INPUTS = []
for p, w in EDGES:
    x = [False] * V
    x[p] = True
    x[N + w] = True
    EDGE_INPUTS.append(x)

# Critical soundness tests: arc point masks with line masks that have NO edge
NEG_TESTS = []
for pmask in ARCS:
    # all line masks with no edge: lines that avoid all selected points
    forbidden_lines = set()
    for w in range(N):
        if any(pmask & (1 << p) for p in LINE_PTS[w]):
            forbidden_lines.add(w)
    # empty line mask always
    NEG_TESTS.append((pmask, 0))
    # single non-incident lines
    for w in range(N):
        if w not in forbidden_lines:
            NEG_TESTS.append((pmask, 1 << w))
    # a few random safe line masks
    safe = [w for w in range(N) if w not in forbidden_lines]
    if safe:
        for _ in range(3):
            k = random.randint(0, min(3, len(safe)))
            chosen = random.sample(safe, k) if k else []
            lmask = 0
            for w in chosen:
                lmask |= 1 << w
            NEG_TESTS.append((pmask, lmask))

print(f"arcs={len(ARCS)} neg_tests={len(NEG_TESTS)}", flush=True)


def score(gates: List[Gate], out: int, full_neg: bool = False) -> Tuple[int, int, int]:
    """Return (completeness_fail, soundness_fail, size). Lower better. 0,0,<=63 wins."""
    cf = 0
    for x in EDGE_INPUTS:
        if not eval_out(gates, out, x):
            cf += 1
    sf = 0
    tests = NEG_TESTS if not full_neg else None
    if tests is not None:
        for pmask, lmask in tests:
            if eval_out(gates, out, pack(pmask, lmask)) and not has_edge(pmask, lmask):
                sf += 1
    else:
        for pmask in ARCS:
            for lmask in range(1 << N):
                if eval_out(gates, out, pack(pmask, lmask)) and not has_edge(pmask, lmask):
                    sf += 1
                    if sf > 5:
                        return cf, sf, len(gates)
    return cf, sf, len(gates)


def mutate(gates: List[Gate], out: int) -> Tuple[List[Gate], int]:
    g = [(op, tuple(inp)) for op, inp in gates]
    out2 = out
    m = random.randrange(6)
    if m == 0 and g:
        # flip op
        i = random.randrange(len(g))
        op, inp = g[i]
        g[i] = ("or" if op == "and" else "and", inp)
    elif m == 1 and g:
        # rewire one input
        i = random.randrange(len(g))
        op, inp = g[i]
        if inp:
            inp = list(inp)
            j = random.randrange(len(inp))
            inp[j] = random.randrange(V + i)
            g[i] = (op, tuple(inp))
    elif m == 2 and len(g) > 50:
        # delete a gate, map refs to one of its inputs or random earlier
        i = random.randrange(len(g))
        op, inp = g[i]
        repl = inp[0] if inp else random.randrange(V)
        new_g = []
        old_to_new = {}
        for gi, (op2, inp2) in enumerate(g):
            if gi == i:
                if repl < V:
                    old_to_new[V + gi] = repl
                elif repl in old_to_new:
                    old_to_new[V + gi] = old_to_new[repl]
                else:
                    old_to_new[V + gi] = 0
                continue
            ni = tuple(r if r < V else old_to_new.get(r, 0) for r in inp2)
            new_g.append((op2, ni))
            old_to_new[V + gi] = V + len(new_g) - 1
        g = new_g
        out2 = old_to_new.get(out, out) if out >= V else out
    elif m == 3 and len(g) < 70:
        # append random gate
        lim = V + len(g)
        a, b = random.randrange(lim), random.randrange(lim)
        op = random.choice(["and", "or"])
        g.append((op, (a, b)))
        if random.random() < 0.2:
            out2 = V + len(g) - 1
    elif m == 4 and g:
        # replace gate with (in0 OR/AND unclean partner)
        i = random.randrange(len(g))
        op, inp = g[i]
        if len(inp) == 2:
            # swap to AND of two points or two lines sometimes
            if random.random() < 0.5:
                a = random.randrange(N)  # point
                b = random.randrange(N)
                g[i] = ("and", (a, b))
            else:
                a = N + random.randrange(N)
                b = N + random.randrange(N)
                g[i] = ("and", (a, b))
    else:
        # change output to random wire
        out2 = random.randrange(V + len(g))
    return g, out2


def full_verify(gates, out) -> bool:
    cf, sf, _ = score(gates, out, full_neg=True)
    return cf == 0 and sf == 0


def main():
    random.seed(1)
    gates, out = cover_lines()
    assert score(gates, out)[0] == 0
    best = (gates, out, score(gates, out))
    print("start", best[2], flush=True)
    t0 = time.time()
    budget = float(sys.argv[1]) if len(sys.argv) > 1 else 180.0
    trials = 0
    accepts = 0
    while time.time() - t0 < budget:
        trials += 1
        g2, o2 = mutate(gates, out)
        if not g2 or len(g2) > 75:
            continue
        sc = score(g2, o2)
        # lexicographic: cf, sf, size — accept if better or equal with temp
        cur = score(gates, out)
        better = sc < cur
        equalish = sc[0] <= cur[0] and sc[1] <= cur[1] and sc[2] <= cur[2] + 2
        if better or (equalish and random.random() < 0.05):
            gates, out = g2, o2
            accepts += 1
            if sc < best[2]:
                best = (list(g2), o2, sc)
                print("best", sc, "trials", trials, flush=True)
                if sc[0] == 0 and sc[1] == 0 and sc[2] <= 63:
                    print("candidate size", sc[2], "full verify...", flush=True)
                    if full_verify(g2, o2):
                        print("FOUND", sc[2])
                        print(g2)
                        print("out", o2)
                        return 0
                    else:
                        print("failed full verify", flush=True)
    print("done trials", trials, "accepts", accepts, "best", best[2])
    # If best has cf=0 and size<=63, full-check soundness
    g, o, sc = best
    if sc[0] == 0 and sc[2] <= 63:
        print("full-checking best...", flush=True)
        if full_verify(g, o):
            print("FOUND", sc)
            return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
