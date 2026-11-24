#!/usr/bin/env python3
"""Exhaustive-ish search: is there a size-3 monotone FI2 circuit on
(a,b,c,d,L) that matches L∧(a∨b∨c∨d) whenever wt(a,b,c,d)≤2?"""
from __future__ import annotations

import itertools
import random
import sys
from typing import List, Tuple

# inputs: 0=a,1=b,2=c,3=d,4=L
Gate = Tuple[str, Tuple[int, ...]]


def eval_circ(gates, out, bits):
    w = list(bits)
    for op, inp in gates:
        vals = [w[i] if i < len(w) else False for i in inp]
        w.append(all(vals) if op == "and" else (any(vals) if vals else False) if op != "and" else False)
        if op == "and":
            w[-1] = all(vals) if vals else True
        else:
            w[-1] = any(vals) if vals else False
    return w[out]


def target(bits):
    a, b, c, d, L = bits
    return L and (a or b or c or d)


def wt_pts(bits):
    return sum(bits[:4])


def ok_partial(gates, out):
    # completeness on wt<=2 with L: must match target
    # also when L false and wt<=2: must be false (arc soundness local)
    for bits in itertools.product([False, True], repeat=5):
        if wt_pts(bits) > 2:
            continue
        if eval_circ(gates, out, bits) != target(bits):
            return False
    return True


def ok_full(gates, out):
    for bits in itertools.product([False, True], repeat=5):
        if eval_circ(gates, out, bits) != target(bits):
            return False
    return True


def enumerate_size(k: int, limit: int = 500000):
    """Enumerate circuits with k gates, fan-in ≤2, AND/OR."""
    # Each gate: op in {and,or}, inputs from {0..4+j-1} with length 0,1,2
    count = 0
    found_partial = 0
    found_full = 0
    # Use recursive build
    def rec(gates):
        nonlocal count, found_partial, found_full
        if count >= limit:
            return
        if len(gates) == k:
            count += 1
            # try each wire as output (prefer last)
            for out in [4 + k - 1]:  # last gate only to prune
                if ok_partial(gates, out):
                    found_partial += 1
                    print("PARTIAL", gates, "out", out, "full?", ok_full(gates, out))
                    if ok_full(gates, out):
                        found_full += 1
            return
        j = len(gates)
        lim = 5 + j
        # fan-in 2
        for op in ("and", "or"):
            for i1, i2 in itertools.product(range(lim), repeat=2):
                gates.append((op, (i1, i2)))
                rec(gates)
                gates.pop()
                if count >= limit:
                    return
            # fan-in 1
            for i1 in range(lim):
                gates.append((op, (i1,)))
                rec(gates)
                gates.pop()
                if count >= limit:
                    return
            # fan-in 0
            gates.append((op, ()))
            rec(gates)
            gates.pop()
            if count >= limit:
                return

    rec([])
    return count, found_partial, found_full


def random_search(k: int, trials: int = 200000):
    found = []
    for t in range(trials):
        gates = []
        for j in range(k):
            lim = 5 + j
            op = random.choice(["and", "or"])
            arity = random.choices([0, 1, 2], weights=[1, 2, 10])[0]
            if arity == 0:
                inp = ()
            elif arity == 1:
                inp = (random.randrange(lim),)
            else:
                inp = (random.randrange(lim), random.randrange(lim))
            gates.append((op, inp))
        out = 4 + k - 1
        if ok_partial(gates, out):
            print("RAND PARTIAL", gates, "full", ok_full(gates, out))
            found.append(gates)
            if len(found) >= 5:
                break
    return found


def main():
    random.seed(0)
    print("Random search size 3...")
    random_search(3, 500000)
    print("Random search size 2...")
    random_search(2, 200000)
    print("Enumerate size 2 (small)...")
    print(enumerate_size(2, limit=1000000))
    print("Enumerate size 3 (may be large)...")
    # size 3 fan-in2: lim grows 5,6,7 — number of gates choices ~ (2*(25+5+1))^3 huge
    # prune: only fan-in exactly 2
    count = 0
    found = 0
    ops = ["and", "or"]
    for g0 in itertools.product(ops, range(5), range(5)):
        for g1 in itertools.product(ops, range(6), range(6)):
            for g2 in itertools.product(ops, range(7), range(7)):
                gates = [
                    (g0[0], (g0[1], g0[2])),
                    (g1[0], (g1[1], g1[2])),
                    (g2[0], (g2[1], g2[2])),
                ]
                count += 1
                if ok_partial(gates, 7):  # 5+2=7 last wire... wires: 0-4 inputs, 5,6,7 gates
                    # out wire index = 5+2 = 7
                    found += 1
                    print("ENUM PARTIAL", gates, "full", ok_full(gates, 7))
                    if found >= 20:
                        print("count", count, "found", found)
                        return
    print("done count", count, "found", found)


if __name__ == "__main__":
    main()
