#!/usr/bin/env python3
"""Search for a <=63 fan-in-2 AND/OR circuit for PG(2,3) incidence that is
arc-correct: true on every incident point-line pair, and on every arc input
(<=2 true points per line) true implies some incidence is present.

Complementary to L-meta-972 (size >= 64 for the exact edge function).
"""
from __future__ import annotations

import hashlib
import itertools
import random
import sys
import time
from typing import List, Optional, Tuple

# Difference set for PG(2,3): lines are translates of {0,1,3,9} mod 13.
DIFF = (0, 1, 3, 9)
N = 13  # points and lines
V = 26  # total inputs: points 0..12, lines 13..25

LINE_PTS = [frozenset((w + d) % N for d in DIFF) for w in range(N)]
PT_LINES = [frozenset(w for w in range(N) if p in LINE_PTS[w]) for p in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]
assert len(EDGES) == 52


def is_arc_points(mask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if mask & (1 << p)) > 2:
            return False
    return True


# All point-masks that are arcs (including empty). 560 nonempty+empty? empty+...
ARCS = [m for m in range(1 << N) if is_arc_points(m)]
assert len(ARCS) == 560  # includes empty; Glynn-style count often 560 for PG(2,3) with empty?


Gate = Tuple[str, Tuple[int, ...]]  # ("and"|"or", inputs)


def eval_circuit(gates: List[Gate], out: int, xbits: List[bool]) -> bool:
    w = list(xbits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        if op == "and":
            w.append(all(vals) if vals else True)
        else:
            w.append(any(vals) if vals else False)
    return w[out] if out < len(w) else False


def edge_input(p: int, w: int) -> List[bool]:
    x = [False] * V
    x[p] = True
    x[N + w] = True
    return x


def pack_input(pmask: int, lmask: int) -> List[bool]:
    x = [False] * V
    for p in range(N):
        if pmask & (1 << p):
            x[p] = True
    for w in range(N):
        if lmask & (1 << w):
            x[N + w] = True
    return x


def has_edge(pmask: int, lmask: int) -> bool:
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def check_completeness(gates: List[Gate], out: int) -> bool:
    for p, w in EDGES:
        if not eval_circuit(gates, out, edge_input(p, w)):
            return False
    return True


def check_arc_soundness(gates: List[Gate], out: int, max_line_masks: int = 0) -> bool:
    """If max_line_masks==0, check all 2^13 line masks; else random sample."""
    if max_line_masks <= 0:
        line_iter = range(1 << N)
    else:
        line_iter = [random.randrange(1 << N) for _ in range(max_line_masks)]
        line_iter.append(0)
        line_iter.extend(1 << w for w in range(N))
    for pmask in ARCS:
        for lmask in line_iter:
            if eval_circuit(gates, out, pack_input(pmask, lmask)):
                if not has_edge(pmask, lmask):
                    return False
    return True


def check_full(gates: List[Gate], out: int) -> bool:
    return check_completeness(gates, out) and check_arc_soundness(gates, out, 0)


def or_tree(wires: List[int], gates: List[Gate]) -> int:
    """Append OR-tree reducing wires to one; return output wire index."""
    cur = list(wires)
    if not cur:
        gates.append(("or", ()))  # false
        return V + len(gates) - 1
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


def cover_circuit_points() -> Tuple[List[Gate], int]:
    """Standard |E|+tau-1 = 64 cover using all points as cover."""
    gates: List[Gate] = []
    ands = []
    for p in range(N):
        lines = sorted(PT_LINES[p])
        # OR of 4 line inputs N+l
        w0 = N + lines[0]
        w1 = N + lines[1]
        w2 = N + lines[2]
        w3 = N + lines[3]
        gates.append(("or", (w0, w1)))
        a = V + len(gates) - 1
        gates.append(("or", (w2, w3)))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (p, o)))
        ands.append(V + len(gates) - 1)
    out = or_tree(ands, gates)
    return gates, out


def cover_circuit_lines() -> Tuple[List[Gate], int]:
    gates: List[Gate] = []
    ands = []
    for w in range(N):
        pts = sorted(LINE_PTS[w])
        gates.append(("or", (pts[0], pts[1])))
        a = V + len(gates) - 1
        gates.append(("or", (pts[2], pts[3])))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (N + w, o)))
        ands.append(V + len(gates) - 1)
    out = or_tree(ands, gates)
    return gates, out


def try_drop_gate(gates: List[Gate], out: int) -> Optional[Tuple[List[Gate], int]]:
    """Try removing one gate and rewiring consumers to one of its inputs or false."""
    m = len(gates)
    # Map wire -> gate index producing it: wire = V + gidx
    for drop in range(m):
        # Rewire: every reference to V+drop becomes replacement
        for repl_choice in list(gates[drop][1]) + [-1]:  # -1 means constant false via empty OR
            new_gates: List[Gate] = []
            wire_map = list(range(V))  # old wire -> new wire for inputs
            # We'll build gates except drop; map old V+i to new wires
            old_to_new = {}
            for gi, (op, inp) in enumerate(gates):
                if gi == drop:
                    if repl_choice == -1:
                        # constant false: introduce empty OR once
                        new_gates.append(("or", ()))
                        old_to_new[V + gi] = V + len(new_gates) - 1
                    else:
                        # map to repl_choice (possibly remapped if it was a later gate — only earlier allowed)
                        if repl_choice < V:
                            old_to_new[V + gi] = repl_choice
                        elif repl_choice in old_to_new:
                            old_to_new[V + gi] = old_to_new[repl_choice]
                        else:
                            # replacement is a later/same gate — skip
                            old_to_new = None
                            break
                    continue
                new_inp = []
                ok = True
                for r in inp:
                    if r < V:
                        new_inp.append(r)
                    elif r in old_to_new:
                        new_inp.append(old_to_new[r])
                    else:
                        ok = False
                        break
                if not ok:
                    old_to_new = None
                    break
                new_gates.append((op, tuple(new_inp)))
                old_to_new[V + gi] = V + len(new_gates) - 1
            if old_to_new is None:
                continue
            if out < V:
                new_out = out
            elif out not in old_to_new:
                continue
            else:
                new_out = old_to_new[out]
            if len(new_gates) > 63:
                continue
            # Quick completeness check first
            if not check_completeness(new_gates, new_out):
                continue
            # Sampled arc soundness then full
            if not check_arc_soundness(new_gates, new_out, 64):
                continue
            if check_arc_soundness(new_gates, new_out, 0):
                return new_gates, new_out
    return None


def random_local_search(budget_s: float = 30.0) -> Optional[Tuple[List[Gate], int]]:
    """Start from cover, randomly mutate; keep if still complete + sampled-sound."""
    gates, out = cover_circuit_points()
    assert len(gates) == 64
    t0 = time.time()
    best = None
    trials = 0
    while time.time() - t0 < budget_s:
        trials += 1
        g = [ (op, tuple(inp)) for op, inp in gates ]
        # mutations: flip op, rewire one input, delete last gate if possible, swap
        mtype = random.randrange(4)
        if mtype == 0 and g:
            i = random.randrange(len(g))
            op, inp = g[i]
            g[i] = ("or" if op == "and" else "and", inp)
        elif mtype == 1 and g:
            i = random.randrange(len(g))
            op, inp = g[i]
            if not inp:
                continue
            inp = list(inp)
            j = random.randrange(len(inp))
            # point to any earlier wire
            lim = V + i
            inp[j] = random.randrange(lim)
            g[i] = (op, tuple(inp))
        elif mtype == 2 and len(g) > 40:
            # delete a random gate, rewire refs to one of its inputs or 0
            i = random.randrange(len(g))
            op, inp = g[i]
            repl = inp[0] if inp else 0
            new_g = []
            old_to_new = {}
            for gi, (op2, inp2) in enumerate(g):
                if gi == i:
                    old_to_new[V + gi] = repl if repl < V else old_to_new.get(repl, 0)
                    continue
                ni = tuple(
                    (r if r < V else old_to_new.get(r, 0)) for r in inp2
                )
                new_g.append((op2, ni))
                old_to_new[V + gi] = V + len(new_g) - 1
            g = new_g
            out = old_to_new.get(out, out) if out >= V else out
        else:
            # append a random gate and maybe use as new out
            lim = V + len(g)
            a, b = random.randrange(lim), random.randrange(lim)
            op = random.choice(["and", "or"])
            g.append((op, (a, b)))
            if random.random() < 0.3:
                out = V + len(g) - 1

        if len(g) > 70 or len(g) < 1:
            continue
        if not check_completeness(g, out):
            continue
        if not check_arc_soundness(g, out, 32):
            continue
        # accept
        gates, out = g, out
        if len(gates) <= 63:
            if check_arc_soundness(gates, out, 0):
                return gates, out
            best = (gates, out, len(gates))
    print(f"local_search trials={trials} best={best[2] if best else None}", file=sys.stderr)
    return None


def try_omit_one_point_share() -> Optional[Tuple[List[Gate], int]]:
    """12 full point gadgets + try to cover remaining point's 4 edges with fewer than 4 gates
    by reusing line-OR fragments from neighbours."""
    # For each omitted point p*, build 12-point cover, then add cheap gadgets for p*'s edges.
    for pstar in range(N):
        gates: List[Gate] = []
        ands = []
        line_or4 = {}  # p -> wire that is OR of its 4 lines
        for p in range(N):
            if p == pstar:
                continue
            lines = sorted(PT_LINES[p])
            gates.append(("or", (N + lines[0], N + lines[1])))
            a = V + len(gates) - 1
            gates.append(("or", (N + lines[2], N + lines[3])))
            b = V + len(gates) - 1
            gates.append(("or", (a, b)))
            o = V + len(gates) - 1
            line_or4[p] = o
            gates.append(("and", (p, o)))
            ands.append(V + len(gates) - 1)
        # Now cover edges of pstar. Neighbours of each line of pstar include other points
        # that share that line. Idea: for each line w of pstar, use (pstar AND w) directly
        # (1 AND each) = 4 ANDs, then OR into tree. Cost +4 + OR into existing tree.
        # 12*4 + 4 + OR(13) = 48+4+12 = 64 again.
        # Try: only 3 direct ANDs and get the 4th edge "for free" via false positive path?
        # Or: pstar AND (OR of 3 of its lines) — misses one edge; cover missed edge by
        # AND of that line with OR of other points on it (already have those points' outputs?
        # No - those are point AND line-or, not line alone).

        # Cheaper try: pstar AND OR4(lines) using shared pieces from a neighbour.
        # Pick a neighbour q sharing line w0 with pstar. q's line set has w0.
        # We don't have OR of just pstar's lines as a subwire of q.

        # Explicit: build OR4 for pstar from scratch (3) + AND (1) = 4 → total 64.
        # To get 63: build OR of only 3 lines (2 ORs) + AND = 3, and handle the 4th line
        # by folding into the final OR-tree via (pstar AND w_miss) which is 1 AND → total
        # still 4 for pstar... 2+1+1=4.

        # Unless OR-tree can absorb without extra: we already need to OR the new signals in.
        # 12 ands + 2 signals from pstar → 14 leaves, OR-tree costs 13, plus 3 for pstar gadgets
        # = 12*4 + 3 + 13 = 48+3+13 = 64. Still 64.

        # Omit one OR in the final tree by identifying two signals? Only if equal.

        # Try size 63: 12*4 = 48 point gadgets, pstar contributes (pstar AND w) for each of
        # 4 lines = 4 ANDs, OR-tree on 16 leaves costs 15, total 48+4+15=67 worse.

        # Dual hybrid: use 6 points + 6 lines as cover (still 12? tau=13 so need 13).
        # Minimum vertex cover is 13, so cover construction cannot beat 64.

        # Non-cover: allow computing a function > f_G on non-arcs.
        # Candidate of size 63: take line-cover circuit and replace one (line AND OR4pts)
        # with just OR4pts (drop the AND with line). That fires when 1+ points on the line
        # are true even if line input is false — FAILS arc soundness (1-2 points, no lines).

        # Replace AND with (line OR thresh3(points))? Bigger.

        # Replace final OR combining two ANDs a,b by just a OR (something smaller)...

        continue
    return None


def try_threshold_relax() -> Optional[Tuple[List[Gate], int]]:
    """f OR (some line has >=3 points). May allow sharing; check size and soundness."""
    # Per line: thresh-3 of 4 points is expensive. Skip unless we find a cheap form.
    return None


def try_size63_by_constant_fold() -> Optional[Tuple[List[Gate], int]]:
    """Build cover of 64, force one gate to be a wire copy (fan-in 1 OR), then
    remove a redundant gate elsewhere — unlikely.

    Better: use one point with degree-gadget of cost 3:
    For pstar, compute a = L0 OR L1, b = L2 OR L3, c = a OR b, d = p AND c  (4 gates).
    Identical.

    Algebraic: (p AND (L0 OR L1 OR L2 OR L3)) = (p AND L0) OR (p AND L1) OR ...
    which is larger.

    Try mixed cover of 13 vertices with shared neighbour-ORs when two cover
    vertices are adjacent... they're in different parts.
    """
    # Mixed cover: k points + (13-k) lines.
    for k in range(0, N + 1):
        points = list(range(k))
        # Need lines that cover all edges not incident to chosen points.
        remaining_edges = [(p, w) for p, w in EDGES if p not in points]
        # Greedy line cover for remaining
        lines_needed = []
        rem = set(remaining_edges)
        while rem:
            best_l, best_c = None, -1
            for w in range(N):
                if w in lines_needed:
                    continue
                c = sum(1 for e in rem if e[1] == w)
                if c > best_c:
                    best_c, best_l = c, w
            if best_c <= 0:
                break
            lines_needed.append(best_l)
            rem = {e for e in rem if e[1] != best_l}
        if rem:
            continue
        cover_size = len(points) + len(lines_needed)
        # Gate count estimate: each point: 3 OR + 1 AND = 4; each line: 3+1=4;
        # OR-tree: cover_size - 1. Total 4*cover_size + cover_size - 1 = 5*cover_size - 1.
        # For cover_size=13: 64. For cover_size=12: 59. But tau=13 so cover_size>=13.
        assert cover_size >= 13
    return None


def verify_cover():
    g, o = cover_circuit_points()
    assert len(g) == 64, len(g)
    assert check_full(g, o)
    g2, o2 = cover_circuit_lines()
    assert len(g2) == 64
    assert check_full(g2, o2)
    print("cover OK size", len(g))


def try_drop_from_cover() -> Optional[Tuple[List[Gate], int]]:
    g, o = cover_circuit_points()
    print("trying drop-gate from point-cover...", flush=True)
    r = try_drop_gate(g, o)
    if r:
        return r
    g, o = cover_circuit_lines()
    print("trying drop-gate from line-cover...", flush=True)
    return try_drop_gate(g, o)


def try_asymmetric_gadgets() -> Optional[Tuple[List[Gate], int]]:
    """Use cheaper gadgets for some cover vertices by sharing OR subtrees across
    a designed order of lines.

    Precompute pairwise ORs of lines that are reused.
    There are C(13,2)=78 pairs; too many. Only OR pairs that appear in pencils.

    Each pencil needs OR of 4 specific lines. Shared pair-ORs: two pencils
    intersect in 1 line so share no pair.

    Shared across dual: hmm.

    Formula size for incidence graph of projective plane is known to be high.

    Try size 63 exact edge function via random SAT on structure — skip for now.
    """
    # One more concrete try: output = OR of (p AND l) for all 52 edges, but
    # share the AND results in a chain... 52 AND + 51 OR = 103.

    # Bloom-like: hash lines into 12 buckets? Would false positive.

    # Size 63 attempt: 13 ANDs of (p_i, L_i) for a matching of 13 edges (perfect
    # matching exists — the plane is bipartite 13+13 regular), OR them (12),
    # PLUS something for the other 39 edges with 63-25=38 gates — 39 ANDs needed
    # minimum without sharing = too many.

    return None


def main():
    random.seed(0)
    verify_cover()
    t0 = time.time()

    r = try_drop_from_cover()
    if r:
        g, o = r
        print("FOUND via drop", len(g), "out", o)
        print(g)
        return 0

    r = random_local_search(60.0)
    if r:
        g, o = r
        print("FOUND via local", len(g), "out", o)
        print(g)
        return 0

    # Exhaustive: can we find ANY monotone circuit of size <=63 that is complete
    # on edges and sound on weight-2 (non-edges false)? That is necessary.
    # Weight-2 soundness + completeness = agrees with f_G on all 2-sets.
    # For monotone functions, size of f_G is the question of L-meta-972.
    # Arc soundness is MORE than weight-2: also larger arcs.

    print("NONE found in", round(time.time() - t0, 2), "s")
    return 1


if __name__ == "__main__":
    sys.exit(main())
