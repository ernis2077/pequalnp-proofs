#!/usr/bin/env python3
"""Systematically try cross-gadget sharing to reach size 63.

Idea: precompute some shared ORs of line-pairs or point-pairs, then build
13 cover gadgets reusing those, targeting total <= 63.
"""
from __future__ import annotations

import itertools
import sys
import time
from typing import Dict, List, Optional, Tuple

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [tuple(sorted((w + d) % N for d in DIFF)) for w in range(N)]
PT_LINES = [tuple(sorted(w for w in range(N) if p in LINE_PTS[w])) for p in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]
Gate = Tuple[str, Tuple[int, ...]]
ARCS = None


def is_arc(mask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if mask & (1 << p)) > 2:
            return False
    return True


def prep():
    global ARCS
    ARCS = [m for m in range(1 << N) if is_arc(m)]


def eval_out(gates, out, xbits):
    w = list(xbits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        w.append(all(vals) if op == "and" else (any(vals) if vals else False) if op != "and" else False)
        if op == "and":
            w[-1] = all(vals) if vals else True
        else:
            w[-1] = any(vals) if vals else False
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


def check(gates, out) -> bool:
    for p, wline in EDGES:
        x = [False] * V
        x[p] = True
        x[N + wline] = True
        if not eval_out(gates, out, x):
            return False
    for pmask in ARCS:
        for lmask in range(1 << N):
            if eval_out(gates, out, pack(pmask, lmask)) and not has_edge(pmask, lmask):
                return False
    return True


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


def build_point_cover_with_shared_line_pairs(pair_list: List[Tuple[int, int]]) -> Tuple[List[Gate], int]:
    """Precompute OR for each pair in pair_list (line indices), then for each point
    build OR4 of its 4 lines using those pairs when possible."""
    gates: List[Gate] = []
    pair_wire: Dict[frozenset, int] = {}
    for a, b in pair_list:
        gates.append(("or", (N + a, N + b)))
        pair_wire[frozenset((a, b))] = V + len(gates) - 1
    ands = []
    for p in range(N):
        lines = list(PT_LINES[p])
        # try to cover the 4 lines with 2 precomputed pairs
        remaining = set(lines)
        used = []
        for fs, w in pair_wire.items():
            if fs <= remaining:
                used.append(w)
                remaining -= fs
        # OR together used pairs and remaining singles
        parts = used + [N + x for x in remaining]
        while len(parts) > 1:
            a = parts.pop()
            b = parts.pop()
            gates.append(("or", (a, b)))
            parts.append(V + len(gates) - 1)
        o4 = parts[0]
        gates.append(("and", (p, o4)))
        ands.append(V + len(gates) - 1)
    out = or_tree(ands, gates)
    return gates, out


def try_all_single_shared_pairs():
    """Share exactly one line-pair OR across points that contain it.
    A line-pair is contained in how many points' neighborhoods?
    Two lines meet at 1 point, so the pair of lines is subset of exactly that
    one point's 4-lines. NO SHARING across points!
    """
    # Confirm
    for a, b in itertools.combinations(range(N), 2):
        owners = [p for p in range(N) if a in PT_LINES[p] and b in PT_LINES[p]]
        assert len(owners) == 1, (a, b, owners)
    print("each line-pair owned by exactly 1 point: no cross-point share of line-pairs")
    # dual: each point-pair owned by exactly 1 line
    for a, b in itertools.combinations(range(N), 2):
        owners = [w for w in range(N) if a in LINE_PTS[w] and b in LINE_PTS[w]]
        assert len(owners) == 1
    print("each point-pair owned by exactly 1 line: no cross-line share of point-pairs")


def try_mixed_cover_share():
    """Use k point-gadgets and 13-k line-gadgets. Still 64 with no share.
    Can a point-gadget and a line-gadget share an AND of an incident pair (p,L)?

    Point gadget: p AND (OR of 4 lines). Line gadget: L AND (OR of 4 points).
    Shared: could compute p∧L once (1 AND), then:
      point needs p∧(L∨L1∨L2∨L3) = (p∧L)∨(p∧L1)∨(p∧L2)∨(p∧L3)
      which is MORE expensive (4 ANDs + ORs) than 3 OR + 1 AND.

    Factor p∧(OR4) remains best for point alone.
    """
    return None


def try_save_via_common_subexpr_unclean():
    """Allow unclean: compute all 13 values of OR4_points[w] using a linear-size
    circuit that is wrong on non-arcs but right on arcs.

    On arcs wt<=2 per line, OR4(a,b,c,d) still requires distinguishing 4 singles
    and 6 pairs — the function OR4 restricted to wt<=2 is just OR4 (since wt<=2
    never hits wt 3-4). So the PARTIAL function equals full OR4 on the domain
    wt<=2 anywhere... wait, the domain is global arcs, so for ONE line, other
    points being set could make wt on this line still <=2 while total config is arc.
    OR4 as a function of its 4 inputs only — restricted to inputs with wt<=2 —
    still needs to be correct for all 1+4+6=11 minterms. Minimum monotone circuit
    for OR4 is 3 gates. No local save.

    Global: OR of all 13 OR4s = OR of all points (each point on 4 lines).
    Cost 12 to OR all points. Not helpful alone.
    """
    return None


def try_formula_size_63_matching_plus():
    """13 matching ANDs (d=0) + 12 OR = 25. Remain budget 38 for other 39 edges.
    Remaining differences D'={1,3,9}: 39 edges = 13*3.

    For each remaining edge need something. With 38 gates for 39 ANDs impossible
    without OR-only paths (which would accept singles).

    Unless some edges are implied on arcs by others — they're not for completeness
    (each edge input is a separate completeness requirement).
    Each of 52 edges needs a root-to-AND path that fires on that pair only.
    Information: at least 52 different AND "reasons"? Not quite — the cover uses
    only 13 ANDs, each covering 4 edges.

    Lower bound intuition: need ≥13 ANDs (τ) and ≥52-13=39 more gates for
    neighbor ORs? The |E|+τ-1 = 64 counts 52+13-1. The -1 is the OR-tree overlap.
    Breaking this requires unclean ANDs that cover more than a star of edges.
    """
    return None


def try_unclean_and_covers_c4_like():
    """Even without C4 in G, on the bipartite double we might use
    (p1∨p2)∧(L1∨L2) when {p1,p2}×{L1,L2} has 3 edges and 1 non-edge —
    that would false-accept the non-edge.

    Is the non-edge an arc input? Single non-incident (p,L) is an arc. FAIL.

    What if (p1∨p2∨p3)∧(L1∨L2) where every pair (pi,Lj) is an edge?
    That means {L1,L2}'s points cover — two lines have 4+4-1=7 points, not 3.

    (p1∨p2)∧L1: equals (p1∧L1)∨(p2∧L1) — covers 2 edges of L1, cost 2.
    Four such for a line = 8 > 4.
    """
    return None


def try_depth2_sat_style():
    """Depth-2: OR of ANDs of width <=4, count gates as published fan-in-2 expansion.
    Single-level: OR of (p∧L) for edges: 52 AND + 51 OR = 103.
    Cover is already better.
    """
    return None


def try_one_global_unclean_shortcut():
    """Size 63 construction attempt:
    13 point OR4s of lines using 39 ORs (no share) = 39, then instead of 13 ANDs
    with points, use a different combining network of 63-39-?= .

    Standard: 39 + 13 + 12 = 64.

    Save 1 in the 39: is there a circuit computing all 13 four-ORs of the dual
    lines-at-points with 38 gates?

    Each output ORp = L0∨L1∨L2∨L3 for lines through p.
    Two points share 1 line. Can we save 1 gate globally?

    Model as: start from 13 line inputs (the N+w wires), produce 13 outputs.
    Lower bound for this 13-output Boolean map: each output needs 3 ORs in isolation
    = 39. With sharing, the multi-output OR complexity of the dual block design.

    Known: for projective plane of order n, the complexity of computing all line
    ORs of points... 

    Try greedy CSE: there are 13 targets, each is OR of 4. Total literal occurrences
    52. Each binary OR reduces gate...

    Algorithm: begin with 13 multisets of size 4. While some set has size >1,
    pick two elements that co-occur in the most sets, replace by a new symbol.
    Count steps.
    """
    # Represent each point's line-set as a frozenset of base ids 0..12 (lines)
    sets = [set(PT_LINES[p]) for p in range(N)]
    next_id = N  # new gate ids; base lines are 0..12 meaning wires N+0..N+12
    gates_cost = 0
    # map pair -> new id
    while any(len(s) > 1 for s in sets):
        # count co-occurrence of pairs of current elements
        from collections import Counter
        ctr: Counter = Counter()
        for s in sets:
            for a, b in itertools.combinations(sorted(s), 2):
                ctr[(a, b)] += 1
        if not ctr:
            break
        (a, b), c = ctr.most_common(1)[0]
        # always combine even if c==1
        new = next_id
        next_id += 1
        gates_cost += 1
        for s in sets:
            if a in s and b in s:
                s.remove(a)
                s.remove(b)
                s.add(new)
        if gates_cost > 100:
            break
    print("CSE multi-output OR4 cost", gates_cost, "final sets", sets)
    # Expect 39 if no useful sharing; if <39 we save
    return gates_cost


def try_cse_with_reorder():
    """Same CSE but try random tie-breaking many times."""
    best = 999
    for seed in range(200):
        import random
        random.seed(seed)
        sets = [set(PT_LINES[p]) for p in range(N)]
        next_id = N
        cost = 0
        while any(len(s) > 1 for s in sets):
            from collections import Counter
            ctr: Counter = Counter()
            for s in sets:
                for a, b in itertools.combinations(sorted(s), 2):
                    ctr[(a, b)] += 1
            # among top score, random choice
            if not ctr:
                break
            top = ctr.most_common(1)[0][1]
            cands = [p for p, c in ctr.items() if c == top]
            a, b = random.choice(cands)
            new = next_id
            next_id += 1
            cost += 1
            for s in sets:
                if a in s and b in s:
                    s.discard(a)
                    s.discard(b)
                    s.add(new)
        best = min(best, cost)
    print("best CSE cost over 200 seeds", best)
    return best


def main():
    prep()
    try_all_single_shared_pairs()
    c = try_one_global_unclean_shortcut()
    try_cse_with_reorder()
    # If CSE can't beat 39, standard cover is 64 with no multi-output save
    # Try building and verifying a circuit that uses CSE anyway
    print("done")


if __name__ == "__main__":
    main()
