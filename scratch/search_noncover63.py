#!/usr/bin/env python3
"""Search non-cover architectures for size ≤ 63 arc-correct circuits.

Cover-shaped (13 stars) is locked at 64: dual blocks intersect in ≤1 line/point,
so the thirteen OR4 trees share no internal gates (39 + 13 + 12 = 64).

Non-cover tries:
1. 12 stars + direct ANDs for remaining edges of the omitted vertex
2. Matching layers for difference-set shifts with aggressive CSE
3. Depth-3 random circuits biased toward incidence
"""
from __future__ import annotations

import itertools
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
ARCS = [m for m in range(1 << N) if all(
    sum(1 for p in pts if m & (1 << p)) <= 2 for pts in LINE_PTS
)]


def eval_out(gates, out, x):
    w = list(x)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        if op == "and":
            w.append(all(vals) if vals else True)
        else:
            w.append(any(vals) if vals else False)
    return w[out]


def pack(pmask, lmask):
    x = [False] * V
    for p in range(N):
        x[p] = bool(pmask & (1 << p))
    for i in range(N):
        x[N + i] = bool(lmask & (1 << i))
    return x


def has_edge(pmask, lmask):
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def check(gates, out) -> Tuple[bool, str]:
    for p, wl in EDGES:
        x = [False] * V
        x[p] = True
        x[N + wl] = True
        if not eval_out(gates, out, x):
            return False, "complete"
    for pmask in ARCS:
        for lmask in range(1 << N):
            if eval_out(gates, out, pack(pmask, lmask)) and not has_edge(pmask, lmask):
                return False, "sound"
    return True, "ok"


def or_tree(wires, gates):
    cur = list(wires)
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
    return cur[0]


def try_12_stars_plus_edges(omit_point: bool = True):
    """12 full gadgets + k direct edge ANDs for the omitted vertex's edges."""
    results = []
    for omit in range(N):
        gates: List[Gate] = []
        ands = []
        if omit_point:
            for p in range(N):
                if p == omit:
                    continue
                lines = PT_LINES[p]
                gates.append(("or", (N + lines[0], N + lines[1])))
                a = V + len(gates) - 1
                gates.append(("or", (N + lines[2], N + lines[3])))
                b = V + len(gates) - 1
                gates.append(("or", (a, b)))
                o = V + len(gates) - 1
                gates.append(("and", (p, o)))
                ands.append(V + len(gates) - 1)
            # 4 edges of omit: (omit, L) for L in PT_LINES[omit]
            for L in PT_LINES[omit]:
                gates.append(("and", (omit, N + L)))
                ands.append(V + len(gates) - 1)
        else:
            for w in range(N):
                if w == omit:
                    continue
                pts = LINE_PTS[w]
                gates.append(("or", (pts[0], pts[1])))
                a = V + len(gates) - 1
                gates.append(("or", (pts[2], pts[3])))
                b = V + len(gates) - 1
                gates.append(("or", (a, b)))
                o = V + len(gates) - 1
                gates.append(("and", (N + w, o)))
                ands.append(V + len(gates) - 1)
            for p in LINE_PTS[omit]:
                gates.append(("and", (p, N + omit)))
                ands.append(V + len(gates) - 1)
        out = or_tree(ands, gates)
        results.append((len(gates), omit, gates, out))
        print(f"12-stars+4edges omit={'pt' if omit_point else 'ln'}{omit}: size={len(gates)}")
        if len(gates) <= 63:
            ok, why = check(gates, out)
            print("  ", ok, why)
            if ok:
                return gates, out
    return None


def try_difference_layers():
    """For each d in DIFF: s_d = OR_t (P_{t+d} AND L_t). OR the four s_d.
    Size: 4*(13 AND + 12 OR) + 3 = 4*25+3=103. With CSE across d:

    Share ANDs? P_i ∧ L_j appears for at most one d (d = i-j). No shared ANDs.

    Partial: only 3 differences fully, and approximate the 4th on arcs?
    """
    # 3 full layers: 75 gates, plus cheap approx for 4th
    for skip_d in DIFF:
        gates: List[Gate] = []
        layer_outs = []
        for d in DIFF:
            if d == skip_d:
                continue
            ands = []
            for t in range(N):
                p = (t + d) % N
                gates.append(("and", (p, N + t)))
                ands.append(V + len(gates) - 1)
            layer_outs.append(or_tree(ands, gates))
        # For skipped d: use unclean shortcut — OR_t P_{t+d} AND OR_t L_t
        # too loose. Or: reuse AND from elsewhere.
        # Direct: still add 13 ANDs for skip_d but share OR-tree with another layer
        # by OR'ing into existing tree leaf-by-leaf: add 13 AND + 13 OR into tree = +26
        # total 3*25 + 26 = 101. Still bad.
        #
        # Budget 63: only room for ~2 full layers (50) + 13 leftover.
        # 2 layers cover 26 edges; 26 edges remain.
        ands2 = []
        d = skip_d
        for t in range(N):
            p = (t + d) % N
            gates.append(("and", (p, N + t)))
            ands2.append(V + len(gates) - 1)
        # merge all layer outs and ands2
        out = or_tree(layer_outs + ands2, gates)
        print(f"3-layer+13and skip_d={skip_d}: size={len(gates)}")
        # too big; skip check
    return None


def try_two_layers_plus_cover_fragment():
    """2 difference layers (50 gates) + small cover fragment with 13 gates."""
    # 2 layers = 26 edges covered by matching-style. Remaining 26 edges:
    # the other two differences. With 13 gates cannot cover 26 edges as ANDs.
    return None


def try_random_noncover(budget_s=90.0):
    """Random circuits of size 63 with AND-bias toward (point,line) pairs."""
    random.seed(2)
    t0 = time.time()
    best_cf = 99
    trials = 0
    while time.time() - t0 < budget_s:
        trials += 1
        gates: List[Gate] = []
        # Seed with many edge ANDs
        edges = list(EDGES)
        random.shuffle(edges)
        for p, w in edges[:20]:
            gates.append(("and", (p, N + w)))
            if len(gates) >= 63:
                break
        while len(gates) < 63:
            lim = V + len(gates)
            if random.random() < 0.4 and edges:
                p, w = random.choice(edges)
                a, b = p, N + w
                op = "and"
            else:
                a, b = random.randrange(lim), random.randrange(lim)
                op = random.choice(["and", "or"])
            gates.append((op, (a, b)))
        out = V + len(gates) - 1
        # quick completeness
        cf = 0
        for p, w in EDGES:
            x = [False] * V
            x[p] = True
            x[N + w] = True
            if not eval_out(gates, out, x):
                cf += 1
        if cf < best_cf:
            best_cf = cf
            print(f"trials={trials} best_cf={best_cf}", flush=True)
        if cf == 0:
            # soundness sample then full
            bad = False
            for pmask in random.sample(ARCS, min(80, len(ARCS))):
                for _ in range(40):
                    lmask = random.randrange(1 << N)
                    if eval_out(gates, out, pack(pmask, lmask)) and not has_edge(pmask, lmask):
                        bad = True
                        break
                if bad:
                    break
            if not bad:
                ok, why = check(gates, out)
                print("full", ok, why, "size", len(gates))
                if ok:
                    return gates, out
    print("random done", trials, "best_cf", best_cf)
    return None


def try_12_stars_plus_3_and_unclean():
    """12 stars (48) + OR-tree on 12 (11) = 59, budget 4 more gates.
    Need to cover 4 edges of omitted vertex with ≤4 gates, arc-sound.

    Direct 4 ANDs + need to OR into tree: would add 4 AND + rebuild tree
    with 16 leaves costing 15 instead of 11 (+4), total +8 → 67.

    With budget 4 total for everything: impossible to add 4 ANDs and connect.

    12 stars + 3 ANDs for 3 of 4 edges, and get 4th via unclean of size 1?
    Completeness for 4th edge needs a path — one AND (p,L) is the minimum,
    so 4 ANDs minimum for 4 edges if no OR4 structure. With OR3+AND = 3 for 3
    edges of a star? (p AND (L1∨L2∨L3)) covers 3 edges cost 3, plus (p AND L4)
    cost 1 = 4, plus OR-tree 12→14 leaves: +2 in tree vs 12 leaves...
    12*4=48, +3+1=4, tree 13 = 48+4+13=65. Still 65.

    11 stars + bigger: worse.
    """
    for omit in range(N):
        gates: List[Gate] = []
        ands = []
        for p in range(N):
            if p == omit:
                continue
            lines = PT_LINES[p]
            gates.append(("or", (N + lines[0], N + lines[1])))
            a = V + len(gates) - 1
            gates.append(("or", (N + lines[2], N + lines[3])))
            b = V + len(gates) - 1
            gates.append(("or", (a, b)))
            o = V + len(gates) - 1
            gates.append(("and", (p, o)))
            ands.append(V + len(gates) - 1)
        Ls = list(PT_LINES[omit])
        # (omit AND OR3) + (omit AND Lmiss)
        gates.append(("or", (N + Ls[0], N + Ls[1])))
        a = V + len(gates) - 1
        gates.append(("or", (a, N + Ls[2])))
        o3 = V + len(gates) - 1
        gates.append(("and", (omit, o3)))
        ands.append(V + len(gates) - 1)
        gates.append(("and", (omit, N + Ls[3])))
        ands.append(V + len(gates) - 1)
        out = or_tree(ands, gates)
        print(f"12star+OR3+1and omit pt{omit}: size={len(gates)}")
        if len(gates) <= 63:
            ok, why = check(gates, out)
            print("  ", ok, why)
            if ok:
                return gates, out
    return None


def main():
    print("arcs", len(ARCS))
    r = try_12_stars_plus_edges(True)
    if r:
        print("FOUND", len(r[0]))
        return 0
    r = try_12_stars_plus_edges(False)
    if r:
        print("FOUND", len(r[0]))
        return 0
    r = try_12_stars_plus_3_and_unclean()
    if r:
        print("FOUND", len(r[0]))
        return 0
    try_difference_layers()
    r = try_random_noncover(60)
    if r:
        print("FOUND random", len(r[0]))
        return 0
    print("no noncover witness")
    return 1


if __name__ == "__main__":
    sys.exit(main())
