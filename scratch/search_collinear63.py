#!/usr/bin/env python3
"""Try constructions for g = f_G OR Collinear3 of size <= 63, verify arc-correctness."""
from __future__ import annotations

import sys
from typing import List, Tuple

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [tuple(sorted((w + d) % N for d in DIFF)) for w in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]
Gate = Tuple[str, Tuple[int, ...]]


def is_arc(mask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if mask & (1 << p)) > 2:
            return False
    return True


ARCS = [m for m in range(1 << N) if is_arc(m)]


def eval_wires(gates, xbits):
    w = list(xbits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        w.append(all(vals) if op == "and" else (any(vals) if vals else False) if op == "or" else False)
        if op == "and":
            w[-1] = all(vals) if vals else True
        else:
            w[-1] = any(vals) if vals else False
    return w


def pack(pmask, lmask):
    x = [False] * V
    for p in range(N):
        x[p] = bool(pmask & (1 << p))
    for w in range(N):
        x[N + w] = bool(lmask & (1 << w))
    return x


def has_edge(pmask, lmask):
    for w in range(N):
        if lmask & (1 << w):
            for p in LINE_PTS[w]:
                if pmask & (1 << p):
                    return True
    return False


def check(gates, out):
    for p, w in EDGES:
        x = [False] * V
        x[p] = True
        x[N + w] = True
        if not eval_wires(gates, x)[out]:
            return False, "complete"
    for pmask in ARCS:
        for lmask in range(1 << N):
            if eval_wires(gates, pack(pmask, lmask))[out] and not has_edge(pmask, lmask):
                return False, "sound"
    return True, "ok"


def or_tree(wires, gates):
    cur = list(wires)
    if not cur:
        gates.append(("or", ()))
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


def thresh2_4(a, b, c, d, gates):
    """Thresh2 of 4 vars, return wire. Cost 7 with formula (a∧b)∨(c∧d)∨((a∨b)∧(c∨d))."""
    gates.append(("and", (a, b)))
    ab = V + len(gates) - 1
    gates.append(("and", (c, d)))
    cd = V + len(gates) - 1
    gates.append(("or", (a, b)))
    aob = V + len(gates) - 1
    gates.append(("or", (c, d)))
    cod = V + len(gates) - 1
    gates.append(("and", (aob, cod)))
    mid = V + len(gates) - 1
    gates.append(("or", (ab, cd)))
    o1 = V + len(gates) - 1
    gates.append(("or", (o1, mid)))
    return V + len(gates) - 1


def thresh3_4(a, b, c, d, gates):
    """(a∧b∧(c∨d)) ∨ (c∧d∧(a∨b)) cost 7."""
    gates.append(("or", (c, d)))
    cod = V + len(gates) - 1
    gates.append(("and", (a, b)))
    ab = V + len(gates) - 1
    gates.append(("and", (ab, cod)))
    t1 = V + len(gates) - 1
    gates.append(("or", (a, b)))
    aob = V + len(gates) - 1
    gates.append(("and", (c, d)))
    cd = V + len(gates) - 1
    gates.append(("and", (cd, aob)))
    t2 = V + len(gates) - 1
    gates.append(("or", (t1, t2)))
    return V + len(gates) - 1


def or4(a, b, c, d, gates):
    gates.append(("or", (a, b)))
    x = V + len(gates) - 1
    gates.append(("or", (c, d)))
    y = V + len(gates) - 1
    gates.append(("or", (x, y)))
    return V + len(gates) - 1


def try_factor_per_line():
    """Per line: OR4 ∧ (L ∨ Thresh3) = (L∧OR4)∨Thresh3. Build all 13, OR together.
    Cost per line: or4(3)+thresh3(7)+or(L,t3)(1)+and(1) = 12, ×13 +12 = 168. Too big.
    """
    return None


def try_shared_or4_plus_one_thresh3():
    """12 standard line gadgets (48) + OR-tree partial + one Thresh3 for omitted line
    that also covers via (OR4 ∧ Thresh3) = Thresh3 when we drop L.

    For omitted line w*: output includes Thresh3(pts of w*).
    Completeness for (p, L_w*): Thresh3 false on single point. FAIL unless we also
    have L_w* AND OR4.

    So: 12 gadgets + (L* AND OR4*) + Thresh3* OR'd — that's full 13 + extra Thresh3. Worse.

    Better idea: for ALL lines use OR4 only (no L), OR them = OR of all points that
    appear in any line = OR of all points (since every point is on a line). Then
    AND with OR of all lines: (OR points)∧(OR lines). Size: or-tree 12 for points,
    12 for lines, 1 AND = 25. Completeness OK for any point+line. Soundness FAILS
    on non-incident point+line (arc).
    """
    return None


def try_omit_one_or_in_final_with_thresh():
    """12 line gadgets (48) + for w*: compute OR4 (3) and Thresh3 (7) and L,
    output_local = (L AND OR4) OR Thresh3 = OR4 AND (L OR Thresh3).
    Cost: 3 + 7 + 1 + 1 = 12 for w* vs 4. Worse.
    """
    return None


def try_pairwise_and_sharing():
    """52 edge ANDs are expensive. Instead: for each line, 4 point-line ANDs share
    the line via (p1∧L)∨(p2∧L)∨(p3∧L)∨(p4∧L) = L∧(p1∨p2∨p3∨p4). Same as cover.

    Unclean: allow (p1∧p2) for points on a line, then AND with (p3 ∨ L)? 
    (p1∧p2∧p3) ∨ (p1∧p2∧L) = (p1∧p2)∧(p3∨L).
    On arcs: p1∧p2∧p3 never (would be 3 on line). So on arcs = p1∧p2∧L.
    That detects edge only if we also need the line — but only when both p1,p2 true.
    Misses single-point edges.

    Combine: (L∧OR4) = (L∧p1)∨(L∧p2)∨(L∧p3)∨(L∧p4).
    Alternative on arcs: since ≤2 points, L∧OR4 = (L∧p1)∨(L∧p2)∨(L∧p3)∨(L∧p4)
    still needed for singles.

    What if: for line w*, use (p1∧p2∧p3)∨(p1∧p2∧p4)∨(p1∧p3∧p4)∨(p2∧p3∧p4)∨(L∧OR4)
    = Thresh3 ∨ (L∧OR4). Same as before.
    """
    return None


def try_size59_drop_one_line_use_points_side():
    """Mix: 11 line gadgets + 2 point gadgets chosen to cover omitted lines' edges.

    Omitted lines: w_a, w_b. Their 8 edges need covering by point gadgets.
    Vertex cover: need points that hit all edges of w_a ∪ w_b.
    Edges of one line: 4 edges. Two lines intersect in 1 point: 4+4-0 = 8 point-line
    edges involving 4+4-1=7 points. Covering 8 edges with points: need all 7 points
    or include the lines. So 11 lines + 7 points = 18 cover vertices — worse.
    """
    return None


def try_construction_or4_and_or_lines_filtered():
    """Crazy idea: compute for each point p the value p, and for each line L.
    Use matching of size 13 (Singer): edges (i, i+d0) for a fixed d0 in D as perfect?
    Incidence graph is 4-regular bipartite on 13+13, has perfect matching of size 13.

    Matching cover gives only 13 edges. Remaining 39 edges need more.

    Size budget 63: 13 ANDs for matching + 12 OR = 25, remaining 38 gates for 39 edges
    — almost 1 gate per edge, need sharing.
    """
    return None


def try_one_shared_pair_or():
    """Build line cover but share one pairwise OR between... impossible across lines.
    Share in the OR-tree: use a balanced tree that reuses — OR-tree can't reuse.

    Use multi-output optimization: compute all 13 OR4s with CSE.
    Represent each OR4 as OR of two pair-ORs. 13*2 = 26 pair-ORs, but only 78 possible
    pairs and each pair appears in exactly one line, so 13*6/2 wait — each line needs
    2 pair-ORs for a partition of its 4 points. Choose a partition per line:
    13 pair-ORs (one matching per line) + 13 ORs combining the two pairs = 26,
    vs 39 without sharing. Save 13! Then 13 ANDs with L + 12 OR-tree = 26+13+12 = 51!

    WAIT: each line needs TWO pair-ORs. Total 26 pair-ORs + 13 combine = 39,
    same as 13*3=39. No savings unless pair-ORs are shared across lines.
    But each pair sits in exactly one line, so the pair-OR for {a,b} is only used
    by that one line's OR4. NO SHARING.

    Unless we use overlapping pairs within a line differently and share with Thresh
    computation for don't-cares — e.g. compute all 6 pair-ANDs for Thresh2 and also use
    for something. Not for exact OR4.
    """
    gates: List[Gate] = []
    # enumerate: pick a 1-factor of each line (partition into 2 pairs)
    pair_or_wires = {}  # frozenset of 2 pts -> wire

    def get_pair_or(u, v):
        key = frozenset((u, v))
        if key in pair_or_wires:
            return pair_or_wires[key]
        gates.append(("or", (u, v)))
        w = V + len(gates) - 1
        pair_or_wires[key] = w
        return w

    ands = []
    for w, pts in enumerate(LINE_PTS):
        a, b, c, d = pts
        # partition
        p1 = get_pair_or(a, b)
        p2 = get_pair_or(c, d)
        gates.append(("or", (p1, p2)))
        o4 = V + len(gates) - 1
        gates.append(("and", (N + w, o4)))
        ands.append(V + len(gates) - 1)
    out = or_tree(ands, gates)
    print("partition cover size", len(gates), "unique pairs", len(pair_or_wires))
    return gates, out


def try_with_collinear_dontcare_simplify_one_or4():
    """On arcs ≤2 per line, OR4(a,b,c,d) = a∨b∨c∨d still needs 3 ORs;
    no Boolean identity reduces OR of 4 under the promise of ≤2 true without
    looking at values — the function restricted to weight≤2 still needs all info.

    Unless we use non-local wires: OR4_w on arcs equals something involving other
    lines' signals? Unlikely for the OR4 alone.
    """
    return None


def try_output_or12_equals_or13_on_arcs_with_modified_gadgets():
    """Modify gadgets so that on arcs, one AND implies another.

    Suppose line gadgets 0..11 standard. For line 12, use a gadget that on arcs
    when it would fire, some other already fires — then we can omit it from OR-tree
    BUT still need completeness for edges of line 12 via other gadgets.

    Completeness forces: for input (p, L12), some gate path accepts.
    Other line gadgets need their L true — false. So need point-side or direct.

    Add point gadgets only for points that help: actually add ONE wire
    (p AND L12) for each of 4 points = 4 ANDs, OR into tree with 12 = 16 leaves.
    Cost: 48 + 4 + 15 = 67.

    Add a single OR4 of the 4 ANDs (p_i AND L12) more cheaply:
    L12 AND OR4(points) — that's the standard 4-gate gadget. Back to 64.
    """
    return None


def try_save_one_in_or_tree_by_ternary():
    """Fan-in 2 OR-tree of 13 costs 12. No save.

    Unless one signal is constant false on arcs — then drop it.
    Which AND signal is always false on arcs? None — each fires on its edge inputs (arcs!).
    """
    return None


def try_dual_rail_save():
    """Compute both point-cover and line-cover fragments sharing ANDs.

    Edge (p,l) appears in both. Direct AND (p,l) costs 1, usable in both trees —
    but then we're building from edges up: 52 ANDs + ORs.

    Subset: take a dominating set of edges?
    """
    # Use 39 ANDs? 
    return None


def try_explicit_size63_unclean_and():
    """Construction: 12 line gadgets (48 gates) + special for line 12:
    Let points be a,b,c,d. Compute:
      ab = a∧b  (1)
      cd = c∧d  (1)
      abcd_or = (a∨b)∨(c∨d)  (2) wait 3 for or4
    Actually:
      t2 = thresh2 via (a∧b)∨(c∧d)∨((a∨b)∧(c∨d))  (7)
      Use: (L12 ∧ OR4) ∨ (t2 ∧ false)? no.

    Goal size 3 for the 13th gadget to total 48+3+12=63.

    3-gate gadget for line 12 that works on arcs + completeness:
    Option A: L12 AND (a∨b∨c) — 2 OR + 1 AND = 3, misses point d.
    Option B: (L12 ∨ a) AND (b∨c∨d) — completeness: (d,L12): L12∨a=T, b∨c∨d=T. OK for d!
      (a,L12): L12∨a=T, b∨c∨d=F if only a. FAIL for a.
    Option C: (L12 ∨ (a∧b)) AND OR4 — more gates.
    Option D: (a∨L12) AND (b∨L12) AND (c∨d) — 
      (a,L12): (T)∧(T)∧(F)=F. FAIL.
    Option E: OR4 without L — 3 gates. Completeness OK. Soundness fail on points only.

    Option F: (L12 AND a) OR (L12 AND b) OR ... with sharing = L12 AND OR4 = 4 gates.

    Option G: use unclean (a∧b∧c) OR (L AND OR4) with clever sharing totaling 3? Impossible
    for (L AND OR4) alone needing 4.

    Unless OR4 reuses 2 ORs from elsewhere. Which elsewhere has (a∨b) already?
    Point gadgets on the dual side — we're not building those.

    Build 6 point gadgets + 6 line gadgets + 1 special = 13 cover, share ORs between
    adjacent point and line? A point gadget ORs lines; a line gadget ORs points.
    Different wires — no shared pair-ORs.

    Hybrid cover size 13 always costs 5*13-1=64 with no sharing.
    """
    # Try option: 12*4 + 3 + 12 = 63 with Option A, and cover missed edges via unclean
    # false positives that... can't help completeness for (d,L12).
    for miss_idx in range(4):
        gates: List[Gate] = []
        ands = []
        for w in range(N - 1):
            pts = LINE_PTS[w]
            o4 = or4(pts[0], pts[1], pts[2], pts[3], gates)
            gates.append(("and", (N + w, o4)))
            ands.append(V + len(gates) - 1)
        pts = LINE_PTS[N - 1]
        kept = [pts[i] for i in range(4) if i != miss_idx]
        gates.append(("or", (kept[0], kept[1])))
        x = V + len(gates) - 1
        gates.append(("or", (x, kept[2])))
        o3 = V + len(gates) - 1
        gates.append(("and", (N + (N - 1), o3)))
        ands.append(V + len(gates) - 1)
        out = or_tree(ands, gates)
        print(f"omit point {miss_idx} of last line: size={len(gates)}")
        ok, why = check(gates, out)
        print("  ", ok, why)
        if ok:
            return gates, out
    return None


def try_or4_without_and_for_one_line():
    """12*4 + 3 + 12 = 63: last 'gadget' is just OR4 (no AND with L)."""
    gates: List[Gate] = []
    ands = []
    for w in range(N - 1):
        pts = LINE_PTS[w]
        o4 = or4(pts[0], pts[1], pts[2], pts[3], gates)
        gates.append(("and", (N + w, o4)))
        ands.append(V + len(gates) - 1)
    pts = LINE_PTS[N - 1]
    o4 = or4(pts[0], pts[1], pts[2], pts[3], gates)
    ands.append(o4)  # no AND — unclean
    out = or_tree(ands, gates)
    print(f"OR4-only last: size={len(gates)}")
    ok, why = check(gates, out)
    print("  ", ok, why)
    if ok:
        return gates, out
    return None


def try_thresh2_and_L_for_one_line():
    """For last line: L AND Thresh2(pts). Cost thresh2(7)+1=8 > 4. Worse for size.
    But maybe replace several lines...
    On arcs, L∧Thresh2 equals? Misses single-point edges. Completeness fail.
    """
    return None


def try_L_or_thresh3_and_or4_size():
    """One line uses (L∨Thresh3)∧OR4. Cost 7+3+1+1=12. Worse.
    All 13 that way is g=f_G∨Collinear3. Huge.
    """
    return None


def main():
    r = try_one_shared_pair_or()
    if r:
        g, o = r
        ok, why = check(g, o)
        print("pair partition", ok, why, "size", len(g))

    r = try_or4_without_and_for_one_line()
    if r:
        print("FOUND or4-only", len(r[0]))
        return 0

    r = try_explicit_size63_unclean_and()
    if r:
        print("FOUND omit-point", len(r[0]))
        return 0

    print("no construction worked")
    return 1


if __name__ == "__main__":
    sys.exit(main())
