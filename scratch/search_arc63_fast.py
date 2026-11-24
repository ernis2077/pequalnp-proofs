#!/usr/bin/env python3
"""Fast bit-parallel search for <=63 arc-correct monotone circuits on PG(2,3)."""
from __future__ import annotations

import random
import sys
import time
from typing import List, Optional, Tuple

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [frozenset((w + d) % N for d in DIFF) for w in range(N)]
PT_LINES = [frozenset(w for w in range(N) if p in LINE_PTS[w]) for p in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]
ARCS = []
for m in range(1 << N):
    ok = True
    for pts in LINE_PTS:
        if sum(1 for p in pts if m & (1 << p)) > 2:
            ok = False
            break
    if ok:
        ARCS.append(m)
assert len(ARCS) == 560

Gate = Tuple[str, Tuple[int, ...]]


def or_tree(wires: List[int], gates: List[Gate]) -> int:
    cur = list(wires)
    if not cur:
        gates.append(("or", ()))
        return V + len(gates) - 1
    while len(cur) > 1:
        nxt: List[int] = []
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


def cover_points() -> Tuple[List[Gate], int]:
    gates: List[Gate] = []
    ands = []
    for p in range(N):
        L = sorted(PT_LINES[p])
        gates.append(("or", (N + L[0], N + L[1])))
        a = V + len(gates) - 1
        gates.append(("or", (N + L[2], N + L[3])))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (p, o)))
        ands.append(V + len(gates) - 1)
    return gates, or_tree(ands, gates)


def cover_lines() -> Tuple[List[Gate], int]:
    gates: List[Gate] = []
    ands = []
    for w in range(N):
        P = sorted(LINE_PTS[w])
        gates.append(("or", (P[0], P[1])))
        a = V + len(gates) - 1
        gates.append(("or", (P[2], P[3])))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (N + w, o)))
        ands.append(V + len(gates) - 1)
    return gates, or_tree(ands, gates)


def eval_wires(gates: List[Gate], x: List[int]) -> List[int]:
    """x[i] is a bitset (Python int) for input i; return all wire bitsets."""
    w = list(x)
    for op, inp in gates:
        if not inp:
            w.append(-1 if op == "and" else 0)  # true / false constant on all bits
            continue
        v = w[inp[0]]
        if op == "and":
            for j in inp[1:]:
                v &= w[j]
        else:
            for j in inp[1:]:
                v |= w[j]
        w.append(v)
    return w


def check_complete_bits(gates: List[Gate], out: int) -> bool:
    """52 edges as a bit-parallel batch (pad to 52)."""
    B = len(EDGES)
    batch = [0] * V
    for b, (p, wline) in enumerate(EDGES):
        batch[p] |= 1 << b
        batch[N + wline] |= 1 << b
    wires = eval_wires(gates, batch)
    got = wires[out]
    return got == (1 << B) - 1


def has_edge_mask(pmask: int, lmask: int) -> bool:
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def check_arc_sound_bits(gates: List[Gate], out: int) -> bool:
    """For each arc pmask, batch all 2^13 line masks."""
    L = 1 << N  # 8192
    # Precompute for each line-mask bit position whether each line is set — batch is all lmasks.
    # Input wires: points are CONSTANT across the line-mask batch (fixed pmask);
    # line inputs vary: line w is true on those lmasks where bit w is set.
    line_batch = [0] * N
    for lmask in range(L):
        for w in range(N):
            if lmask & (1 << w):
                line_batch[w] |= 1 << lmask
    # Actually lmask as bit index 0..8191 — good.
    full = (1 << L) - 1
    for pmask in ARCS:
        batch = [0] * V
        for p in range(N):
            if pmask & (1 << p):
                batch[p] = full
        for w in range(N):
            batch[N + w] = line_batch[w]
        wires = eval_wires(gates, batch)
        got = wires[out]
        # Allowed true bits: those lmasks where has_edge(pmask, lmask)
        if got == 0:
            continue
        # Check each set bit
        bad = got
        while bad:
            lsb = bad & -bad
            lmask = lsb.bit_length() - 1
            if not has_edge_mask(pmask, lmask):
                return False
            bad ^= lsb
    return True


def check_full(gates: List[Gate], out: int) -> bool:
    return check_complete_bits(gates, out) and check_arc_sound_bits(gates, out)


def rewrite_drop(gates: List[Gate], out: int, drop: int, repl: int) -> Optional[Tuple[List[Gate], int]]:
    """Remove gate `drop`, map its wire to `repl` (-1 => const false)."""
    new_gates: List[Gate] = []
    old_to_new = {}
    for gi, (op, inp) in enumerate(gates):
        if gi == drop:
            if repl == -1:
                new_gates.append(("or", ()))
                old_to_new[V + gi] = V + len(new_gates) - 1
            elif repl < V:
                old_to_new[V + gi] = repl
            elif repl in old_to_new:
                old_to_new[V + gi] = old_to_new[repl]
            else:
                return None
            continue
        new_inp = []
        for r in inp:
            if r < V:
                new_inp.append(r)
            elif r in old_to_new:
                new_inp.append(old_to_new[r])
            else:
                return None
        new_gates.append((op, tuple(new_inp)))
        old_to_new[V + gi] = V + len(new_gates) - 1
    if out < V:
        new_out = out
    elif out in old_to_new:
        new_out = old_to_new[out]
    else:
        return None
    return new_gates, new_out


def search_drop(gates: List[Gate], out: int) -> Optional[Tuple[List[Gate], int]]:
    m = len(gates)
    print(f"drop-search over {m} gates...", flush=True)
    for drop in range(m):
        candidates = list(gates[drop][1]) + [-1]
        # also try any earlier wire
        lim = V + drop
        extra = list(range(min(lim, V + 8)))  # sample early wires
        for repl in candidates + extra:
            r = rewrite_drop(gates, out, drop, repl)
            if r is None:
                continue
            ng, no = r
            if len(ng) > 63:
                continue
            if not check_complete_bits(ng, no):
                continue
            if check_arc_sound_bits(ng, no):
                return ng, no
        if drop % 8 == 0:
            print(f"  checked drop={drop}", flush=True)
    return None


def try_shared_pair_ors() -> Optional[Tuple[List[Gate], int]]:
    """Build all useful line-pair ORs once, then each pencil uses 2 pairs + 1 OR + AND.
    Pairs aren't shared across pencils (intersect 1), so no savings vs 64.
    Try point-side dual with shared point pairs across lines: two lines share 1 point,
    so no shared pair either.
    """
    return None


def try_size63_matching_plus() -> Optional[Tuple[List[Gate], int]]:
    """Matching of 13 disjoint edges: 13 ANDs + 12 ORs = 25 covers 13 edges.
    Remaining 39 edges: need 39 more ANDs + merge into OR tree.
    25+39+ (need to OR 39 more into the tree: if we OR all 52 ANDs, tree=51, total 103).
    No good.
    """
    return None


def try_omit_and_on_one_cover_vertex() -> Optional[Tuple[List[Gate], int]]:
    """Line cover of 13: for one line, output just OR4(points) without AND line.
    Completeness: when that line and one point fire, OR4 is true — OK.
    Soundness: OR4 true with 1-2 points and NO lines — FAIL.
    Soften: OR4 AND (OR of all lines)? Then need any line true — fails for other edges
    that use only their own line... actually if any line true and 2 points on L0,
    might false-fire.
    """
    # For line 0: use (OR4 pts) AND (OR all 13 lines) — expensive and wrong.
    return None


def try_geo_identity() -> Optional[Tuple[List[Gate], int]]:
    """In PG(2,3), every pair of points is on a line. Not helpful for incidence OR.

    Try: compute OR of all (point AND line) using bilinear circuit with
    intermediate factor width 12 — Boolean rank of incidence matrix is 13.
    """
    # Confirm boolean rank lower bound: incidence matrix of PG(2,q) has
    # Boolean rank q^2+q+1. So cover number 13, size >= 2*13 - 1 = 25 for
    # depth-3 OR-AND-OR of a certain form, but unrestricted monotone circuits
    # still have the |E|+tau-1 = 64 upper and conjectured lower for exact f_G.
    return None


def random_shrink(budget: float = 45.0) -> Optional[Tuple[List[Gate], int]]:
    gates, out = cover_points()
    assert check_complete_bits(gates, out)
    t0 = time.time()
    accepted = 0
    while time.time() - t0 < budget:
        g = list(gates)
        o = out
        # delete random gate
        if len(g) <= 50:
            gates, out = cover_points()
            continue
        drop = random.randrange(len(g))
        repl_choices = list(g[drop][1]) + [-1, 0]
        repl = random.choice(repl_choices)
        r = rewrite_drop(g, o, drop, repl)
        if r is None:
            continue
        ng, no = r
        if not check_complete_bits(ng, no):
            continue
        # cheap soundness sample: empty points, single points, all arcs with lmask=0, random
        # full check only if size<=63 or periodically
        if len(ng) <= 63:
            if check_arc_sound_bits(ng, no):
                return ng, no
            continue
        # accept as new start if sound on lmask=0 for all arcs (no lines => must be false)
        # and a few random line masks
        batch = [0] * V
        # test all arcs with lmask=0 as one batch: all line inputs 0, points vary per bit
        # Use up to 560 bits — OK in Python
        B = len(ARCS)
        batch = [0] * V
        for b, pmask in enumerate(ARCS):
            for p in range(N):
                if pmask & (1 << p):
                    batch[p] |= 1 << b
        wires = eval_wires(ng, batch)
        if wires[no] != 0:
            continue  # fired with no lines on some arc — unsound
        gates, out = ng, no
        accepted += 1
        if accepted % 20 == 0:
            print(f"  shrink size={len(gates)} accepted={accepted}", flush=True)
    print(f"shrink done accepted={accepted} size={len(gates)}", flush=True)
    return None


def main():
    random.seed(1)
    g, o = cover_points()
    print("point-cover size", len(g), flush=True)
    t0 = time.time()
    assert check_complete_bits(g, o)
    print("completeness OK", round(time.time() - t0, 3), "s", flush=True)
    t0 = time.time()
    assert check_arc_sound_bits(g, o)
    print("arc soundness OK", round(time.time() - t0, 3), "s", flush=True)

    for name, builder in [("points", cover_points), ("lines", cover_lines)]:
        g, o = builder()
        print(f"=== drop search on {name} cover ===", flush=True)
        r = search_drop(g, o)
        if r:
            ng, no = r
            print("FOUND", len(ng), no)
            print(ng)
            return 0

    print("=== random shrink ===", flush=True)
    r = random_shrink(60.0)
    if r:
        ng, no = r
        print("FOUND", len(ng), no)
        print(ng)
        return 0

    print("NONE")
    return 1


if __name__ == "__main__":
    sys.exit(main())
