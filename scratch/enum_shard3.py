#!/usr/bin/env python3
"""
Exhaustive DAG enumeration for shard 3 (first gate NOT(0)), rest AND/OR only.

Each wire is a 1024-bit function packed as 16 uint64 words.
Prune gates that repeat an existing wire's function.
Require the NOT wire to be used at least once.

This can exhaust small sizes completely; for larger sizes it is a beam/IDDFS
guided by Hamming distance to the target on a seed set.
"""

from __future__ import annotations

import argparse
import hashlib
import sys
import time
from pathlib import Path

EDGES = [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
]
N = 10
M = 1 << N
W = M // 64


def pack_from_pred(pred):
    words = [0] * W
    for m in range(M):
        if pred(m):
            words[m >> 6] |= 1 << (m & 63)
    return tuple(words)


TARGET = pack_from_pred(
    lambda m: any(((m >> a) & 1) and ((m >> b) & 1) for a, b in EDGES)
)
INPUTS = [pack_from_pred(lambda m, i=i: ((m >> i) & 1) != 0) for i in range(N)]
NOT0 = pack_from_pred(lambda m: ((m >> 0) & 1) == 0)


def band(a, b):
    return tuple(x & y for x, y in zip(a, b))


def bor(a, b):
    return tuple(x | y for x, y in zip(a, b))


def ham(a, b):
    return sum((x ^ y).bit_count() for x, y in zip(a, b))


def exhaust(max_size: int, time_limit: float | None = None):
    """Full exhaustive search up to max_size with duplicate-function pruning."""
    t0 = time.time()
    nodes = 0
    found = None

    # state: list of wire functions; gate descriptions; whether NOT used
    start_wires = INPUTS + [NOT0]
    start_gates = [("not", 0)]

    def rec(wires, gates, used_not, remaining):
        nonlocal nodes, found
        if found is not None:
            return
        if time_limit is not None and time.time() - t0 > time_limit:
            raise TimeoutError
        nodes += 1
        if remaining == 0:
            if used_not and wires[-1] == TARGET:
                found = list(gates)
            return
        # existing function set for pruning
        seen = set(wires)
        nw = len(wires)
        # Always may add AND/OR of any pair i<=j
        for i in range(nw):
            for j in range(i, nw):  # i<=j canonical
                for op, fn in (("and", band), ("or", bor)):
                    val = fn(wires[i], wires[j])
                    if val in seen:
                        continue
                    # track use of NOT wire at index N
                    u = used_not or (i == N) or (j == N)
                    wires.append(val)
                    gates.append((op, i, j))
                    rec(wires, gates, u, remaining - 1)
                    gates.pop()
                    wires.pop()
                    if found is not None:
                        return

    try:
        for S in range(1, max_size + 1):
            # S includes the NOT gate; remaining AND/OR gates = S-1
            found = None
            nodes = 0
            rec(list(start_wires), list(start_gates), False, S - 1)
            dt = time.time() - t0
            print(
                f"exhaust S={S} nodes={nodes} found={found is not None} t={dt:.2f}s",
                flush=True,
            )
            if found is not None:
                return "sat", found
        return "unsat", None
    except TimeoutError:
        return "timeout", None


def beam_search(size: int, beam: int, rounds: int):
    """Beam search minimizing Hamming distance to TARGET; size includes NOT."""
    # state: (ham, wires_tuple_list, gates, used_not)
    start = (ham(NOT0, TARGET), INPUTS + [NOT0], [("not", 0)], False)
    # Actually after only NOT, output is NOT0 if size 1
    beam_states = [start]
    for g in range(1, size):
        cand = []
        seen_global = set()
        for h0, wires, gates, used in beam_states:
            seen = set(wires)
            nw = len(wires)
            for i in range(nw):
                for j in range(i, nw):
                    for op, fn in (("and", band), ("or", bor)):
                        val = fn(wires[i], wires[j])
                        if val in seen:
                            continue
                        u = used or (i == N) or (j == N)
                        key = (val, u)
                        # duplicate by last wire function among beam expansion
                        nh = ham(val, TARGET)
                        new_wires = wires + [val]
                        new_gates = gates + [(op, i, j)]
                        cand.append((nh, new_wires, new_gates, u))
        cand.sort(key=lambda x: (x[0], -int(x[3])))
        # uniq by last wire
        uniq = []
        seen_last = set()
        for c in cand:
            last = c[1][-1]
            if last in seen_last:
                continue
            seen_last.add(last)
            uniq.append(c)
            if len(uniq) >= beam:
                break
        beam_states = uniq
        best = beam_states[0][0]
        print(f"beam layer {g+1}: states={len(beam_states)} best_ham={best}", flush=True)
        if best == 0 and beam_states[0][3]:
            return "sat", beam_states[0][2]
    # final check
    for h, wires, gates, used in beam_states:
        if h == 0 and used:
            return "sat", gates
    return "unsat_beam", beam_states[0][2] if beam_states else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--exhaust-upto", type=int, default=8)
    ap.add_argument("--beam-size", type=int, default=19)
    ap.add_argument("--beam-width", type=int, default=2000)
    ap.add_argument("--time-limit", type=float, default=120.0)
    ap.add_argument("--sha-only", action="store_true")
    args = ap.parse_args()
    path = Path(__file__).resolve()
    print(f"program={path}")
    print(f"sha256={hashlib.sha256(path.read_bytes()).hexdigest()}")
    if args.sha_only:
        return 0
    print(f"target ham to zero={ham(pack_from_pred(lambda m: False), TARGET)}")
    st, circ = exhaust(args.exhaust_upto, args.time_limit)
    print("EXHAUST", st, circ)
    if st == "sat":
        return 0
    st2, circ2 = beam_search(args.beam_size, args.beam_width, 1)
    print("BEAM", st2, "ham" if circ2 else "", flush=True)
    if st2 == "sat":
        print("CIRCUIT", circ2)
        return 0
    if circ2:
        print("best gates sample", circ2[:5], "...", circ2[-3:])
        # compute ham of best
        wires = INPUTS + [NOT0]
        for op, i, j in circ2[1:]:
            wires.append(band(wires[i], wires[j]) if op == "and" else bor(wires[i], wires[j]))
        print("best final ham", ham(wires[-1], TARGET), "used_not_wire_in_gates",
              any(N in (i, j) for op, i, j in circ2[1:]))
    return 1


if __name__ == "__main__":
    sys.exit(main())
