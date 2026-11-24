#!/usr/bin/env python3
"""Search for a ≤63 monotone fan-in-2 circuit that equals f_G on arc inputs
by merging gates of the size-64 cover that agree on the arc domain."""
from __future__ import annotations

import itertools
import sys
import time
from typing import Dict, List, Optional, Tuple

DIFF = (0, 1, 3, 9)
N = 13
V = 26
LINE_PTS = [frozenset((w + d) % N for d in DIFF) for w in range(N)]
PT_LINES = [frozenset(w for w in range(N) if p in LINE_PTS[w]) for p in range(N)]
EDGES = [(p, w) for w in range(N) for p in LINE_PTS[w]]

Gate = Tuple[str, Tuple[int, ...]]


def is_arc_points(mask: int) -> bool:
    for pts in LINE_PTS:
        if sum(1 for p in pts if mask & (1 << p)) > 2:
            return False
    return True


ARCS = [m for m in range(1 << N) if is_arc_points(m)]
print(f"arcs={len(ARCS)}", flush=True)


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
    # OR-tree
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


def cover_circuit_points() -> Tuple[List[Gate], int]:
    gates: List[Gate] = []
    ands = []
    for p in range(N):
        lines = sorted(PT_LINES[p])
        gates.append(("or", (N + lines[0], N + lines[1])))
        a = V + len(gates) - 1
        gates.append(("or", (N + lines[2], N + lines[3])))
        b = V + len(gates) - 1
        gates.append(("or", (a, b)))
        o = V + len(gates) - 1
        gates.append(("and", (p, o)))
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


def eval_wires(gates: List[Gate], xbits: List[bool]) -> List[bool]:
    w = list(xbits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        if op == "and":
            w.append(all(vals) if vals else True)
        else:
            w.append(any(vals) if vals else False)
    return w


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


def fingerprint_wires_on_arcs(gates: List[Gate], sample_lines: Optional[List[int]] = None) -> List[int]:
    """Return a hash fingerprint per wire over arc×line samples (or all lines)."""
    nwires = V + len(gates)
    # Use two 64-bit rolling hashes per wire for collision resistance-ish
    h1 = [0] * nwires
    h2 = [0] * nwires
    lines = sample_lines if sample_lines is not None else list(range(1 << N))
    for pmask in ARCS:
        for lmask in lines:
            x = pack_input(pmask, lmask)
            w = eval_wires(gates, x)
            for i, bit in enumerate(w):
                if bit:
                    h1[i] = (h1[i] * 1000003 + (pmask + 1) * 10007 + (lmask + 1)) & ((1 << 64) - 1)
                    h2[i] = (h2[i] * 10000019 + (pmask + 3) * 10009 + (lmask + 5)) & ((1 << 64) - 1)
                else:
                    h1[i] = (h1[i] * 1000003) & ((1 << 64) - 1)
                    h2[i] = (h2[i] * 10000019) & ((1 << 64) - 1)
    return [h1[i] ^ (h2[i] << 1) for i in range(nwires)]


def exact_wire_eq_on_arcs(gates: List[Gate], i: int, j: int, line_iter) -> bool:
    for pmask in ARCS:
        for lmask in line_iter:
            w = eval_wires(gates, pack_input(pmask, lmask))
            if w[i] != w[j]:
                return False
    return True


def rewrite_drop_equiv(gates: List[Gate], out: int, drop: int, repl: int) -> Tuple[List[Gate], int]:
    """Remove gate `drop` (0-based in gates), map its wire V+drop to repl, renumber."""
    new_gates: List[Gate] = []
    old_to_new: Dict[int, int] = {i: i for i in range(V)}
    for gi, (op, inp) in enumerate(gates):
        if gi == drop:
            old_to_new[V + gi] = repl if repl < V else old_to_new[repl]
            continue
        new_inp = tuple(old_to_new[r] if r in old_to_new else r for r in inp)
        # fix refs to already-mapped
        new_inp2 = []
        for r in inp:
            if r < V:
                new_inp2.append(r)
            elif r == V + drop:
                new_inp2.append(old_to_new[V + drop])
            else:
                new_inp2.append(old_to_new[r])
        new_gates.append((op, tuple(new_inp2)))
        old_to_new[V + gi] = V + len(new_gates) - 1
    new_out = out if out < V else old_to_new[out]
    return new_gates, new_out


def check_completeness(gates: List[Gate], out: int) -> bool:
    for p, w in EDGES:
        x = [False] * V
        x[p] = True
        x[N + w] = True
        if not eval_wires(gates, x)[out]:
            return False
    return True


def check_arc_soundness(gates: List[Gate], out: int) -> bool:
    for pmask in ARCS:
        for lmask in range(1 << N):
            if eval_wires(gates, pack_input(pmask, lmask))[out]:
                if not has_edge(pmask, lmask):
                    return False
    return True


def try_merge(gates: List[Gate], out: int, label: str) -> Optional[Tuple[List[Gate], int]]:
    print(f"=== {label}: size={len(gates)} ===", flush=True)
    # Sample line masks first for fingerprinting
    sample = list(range(0, 1 << N, 17))  # ~482 masks
    sample += [0, (1 << N) - 1] + [1 << i for i in range(N)]
    sample = sorted(set(sample))
    t0 = time.time()
    fps = fingerprint_wires_on_arcs(gates, sample)
    print(f"fingerprinted in {time.time()-t0:.1f}s", flush=True)
    # Group by fingerprint
    groups: Dict[int, List[int]] = {}
    for i, fp in enumerate(fps):
        groups.setdefault(fp, []).append(i)
    cand_pairs = []
    for g in groups.values():
        if len(g) < 2:
            continue
        for a, b in itertools.combinations(g, 2):
            # prefer replacing a later gate with an earlier wire
            if a > b:
                a, b = b, a
            if b < V:
                continue  # both inputs
            cand_pairs.append((a, b))
    print(f"candidate equiv pairs (sample): {len(cand_pairs)}", flush=True)
    # Verify on full line space (expensive) — first on denser sample
    denser = list(range(0, 1 << N, 5)) + sample
    denser = sorted(set(denser))
    verified = []
    for a, b in cand_pairs:
        if exact_wire_eq_on_arcs(gates, a, b, denser):
            verified.append((a, b))
    print(f"verified on denser sample: {len(verified)}", flush=True)
    for a, b in verified:
        # b is a gate wire; replace b's gate by a
        drop = b - V
        if drop < 0 or drop >= len(gates):
            continue
        # full verify equality before rewrite
        print(f"full-check eq wires {a},{b}...", flush=True)
        if not exact_wire_eq_on_arcs(gates, a, b, range(1 << N)):
            print("  rejected on full", flush=True)
            continue
        ng, no = rewrite_drop_equiv(gates, out, drop, a)
        print(f"  dropped gate {drop}, new size {len(ng)}", flush=True)
        if not check_completeness(ng, no):
            print("  fail completeness", flush=True)
            continue
        print("  completeness OK, arc soundness...", flush=True)
        if check_arc_soundness(ng, no):
            print("FOUND", len(ng), no, flush=True)
            return ng, no
        print("  fail arc soundness", flush=True)
    return None


def try_bypass_gate_to_input(gates: List[Gate], out: int) -> Optional[Tuple[List[Gate], int]]:
    """If a gate equals one of its inputs on arcs, bypass it."""
    print("=== bypass-to-input ===", flush=True)
    sample = list(range(0, 1 << N, 11)) + [0] + [1 << i for i in range(N)]
    for gi, (op, inp) in enumerate(gates):
        w = V + gi
        for src in inp:
            if exact_wire_eq_on_arcs(gates, w, src, sample):
                if exact_wire_eq_on_arcs(gates, w, src, range(1 << N)):
                    ng, no = rewrite_drop_equiv(gates, out, gi, src)
                    if len(ng) <= 63 and check_completeness(ng, no) and check_arc_soundness(ng, no):
                        print("FOUND bypass", gi, "->", src, "size", len(ng))
                        return ng, no
    return None


def try_drop_or_tree_leaf_on_arcs(gates: List[Gate], out: int, ands_start: int) -> Optional[Tuple[List[Gate], int]]:
    """On arcs, is OR of 13 and-signals equal to OR of 12 of them?
    If yes, rebuild with 12 leaves → size 12*4 + 11 = 59."""
    # ands are gates at indices 3,7,11,...,51 for line cover (every 4th ending with AND)
    and_wires = [V + i for i in range(len(gates)) if gates[i][0] == "and"]
    print(f"AND wires: {len(and_wires)}", flush=True)
    if len(and_wires) != 13:
        return None
    # Check whether any single AND is implied by OR of others on arcs
    sample = list(range(0, 1 << N, 7)) + [1 << i for i in range(N)]
    for omit_i, omit_w in enumerate(and_wires):
        ok = True
        for pmask in ARCS:
            for lmask in sample:
                wvals = eval_wires(gates, pack_input(pmask, lmask))
                if wvals[omit_w]:
                    if not any(wvals[aw] for j, aw in enumerate(and_wires) if j != omit_i):
                        ok = False
                        break
            if not ok:
                break
        if not ok:
            continue
        # denser check
        print(f"omit AND {omit_i} survived sample; full check...", flush=True)
        ok2 = True
        for pmask in ARCS:
            for lmask in range(1 << N):
                wvals = eval_wires(gates, pack_input(pmask, lmask))
                if wvals[omit_w] and not any(
                    wvals[aw] for j, aw in enumerate(and_wires) if j != omit_i
                ):
                    ok2 = False
                    break
            if not ok2:
                break
        if ok2:
            print(f"AND {omit_i} redundant on arcs!", flush=True)
            # rebuild circuit without that line/point gadget
            return ("redundant", omit_i)  # type: ignore
    return None


def main():
    for builder, name in [(cover_circuit_lines, "lines"), (cover_circuit_points, "points")]:
        g, o = builder()
        assert len(g) == 64
        assert check_completeness(g, o)
        r = try_drop_or_tree_leaf_on_arcs(g, o, 0)
        if r:
            print("REDUNDANT LEAF", r)
            return 0
        r = try_bypass_gate_to_input(g, o)
        if r:
            print("BYPASS", r[0])
            return 0
        r = try_merge(g, o, name)
        if r:
            print("MERGE", len(r[0]))
            return 0
    print("no merge found")
    return 1


if __name__ == "__main__":
    sys.exit(main())
