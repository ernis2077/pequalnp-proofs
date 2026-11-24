#!/usr/bin/env python3
"""Existential Monotone2 circuit search for L-meta-2571 (desk gap).

Exhaustive over gate count <= max_gates and output/aux wire indices; Z3 on sampled rows.
"""
from __future__ import annotations
import itertools
import random
import sys

from z3 import And, Bool, If, Int, Or, Solver, sat

N = 25
RES = {0, 1, 3, 9}
EXCL = {0, 2, 8}


def rel(i: int, j: int) -> bool:
    return i < 12 and j >= 12 and i not in EXCL and (i + j + 2) % 13 in RES


def target_eval(x: tuple[bool, ...]) -> bool:
    for i in range(12):
        if i in EXCL:
            continue
        for j in range(12, N):
            if rel(i, j) and x[i] and x[j]:
                return True
    return False


def aux_input(x: tuple[bool, ...]) -> bool:
    return x[13] or x[15] or x[21]


def py_eval(gates: list[tuple[str, int, int]], out: int, x: list[bool]) -> bool:
    w = list(x)
    for op, a, b in gates:
        w.append((w[a] and w[b]) if op == "and" else (w[a] or w[b]))
    return w[out]


def py_wires(gates: list[tuple[str, int, int]], x: list[bool]) -> list[bool]:
    w = list(x)
    for op, a, b in gates:
        w.append((w[a] and w[b]) if op == "and" else (w[a] or w[b]))
    return w


def minterm_rows() -> list[tuple[bool, ...]]:
    rows = []
    for i in range(12):
        if i in EXCL:
            continue
        for j in range(12, N):
            if not rel(i, j):
                continue
            x = [False] * N
            x[i] = x[j] = True
            rows.append(tuple(x))
    return rows


def false_row_sample(n: int = 220) -> list[tuple[bool, ...]]:
    rows: set[tuple[bool, ...]] = {tuple([False] * N)}
    for a, b, c in itertools.product([False, True], repeat=3):
        x = [False] * N
        x[13], x[15], x[21] = a, b, c
        if not target_eval(tuple(x)):
            rows.add(tuple(x))
    bases = list(rows)
    while len(rows) < n:
        x = list(random.choice(bases))
        for _ in range(random.randint(1, 5)):
            x[random.randrange(N)] = not x[random.randrange(N)]
        if target_eval(tuple(x)):
            continue
        rows.add(tuple(x))
        bases.append(x)
    return list(rows)


def select_wire(wires, idx):
    r = wires[0]
    for i in range(1, len(wires)):
        r = If(idx == i, wires[i], r)
    return r


def eval_row(gates_true, in1, in2, x: tuple[bool, ...]):
    wires = []
    for w in range(N):
        wires.append(x[w])
    for j in range(len(gates_true)):
        a = select_wire(wires, in1[j])
        b = select_wire(wires, in2[j])
        wires.append(If(gates_true[j], Or(a, b), And(a, b)))
    return wires


def solve_fixed_out_aux(s: int, out: int, aux: int, rows_true, rows_false, timeout_ms: int = 8_000):
    gates_true = [Bool(f"gt{j}") for j in range(s)]
    in1 = [Int(f"in1_{j}") for j in range(s)]
    in2 = [Int(f"in2_{j}") for j in range(s)]
    sol = Solver()
    sol.set(timeout=timeout_ms)
    for j in range(s):
        sol.add(in1[j] >= 0, in2[j] >= 0, in1[j] < N + j, in2[j] < N + j, in1[j] < in2[j])
    for x in rows_true:
        wires = eval_row(gates_true, in1, in2, x)
        sol.add(wires[out])
    for x in rows_false:
        wires = eval_row(gates_true, in1, in2, x)
        sol.add(wires[out] == False)
        sol.add(wires[aux] == aux_input(x))
    if sol.check() != sat:
        return None
    m = sol.model()
    gates = []
    for j in range(s):
        op = "or" if m.eval(gates_true[j]) else "and"
        gates.append((op, m.eval(in1[j]).as_long(), m.eval(in2[j]).as_long()))
    return gates


def verify(gates, out, q, samples: int = 80_000) -> bool:
    for x in minterm_rows():
        if not py_eval(gates, out, list(x)):
            return False
    for _ in range(samples):
        x = [random.choice([False, True]) for _ in range(N)]
        t = target_eval(tuple(x))
        if py_eval(gates, out, x) != t:
            return False
        if not t and py_wires(gates, x)[q] != aux_input(tuple(x)):
            return False
    return True


def main() -> int:
    max_s = int(sys.argv[1]) if len(sys.argv) > 1 else 45
    rows_t = minterm_rows()
    rows_f = false_row_sample(250)
    print(f"minterms={len(rows_t)} false_samples={len(rows_f)}", file=sys.stderr)

    for s in range(max_s, max_s - 1, -1):
        W = N + s
        print(f"try s={s}", file=sys.stderr)
        out_cands = list(range(max(N, W - 8), W))
        aux_cands = list(range(max(N, W - 12), W))
        for out in out_cands:
            for aux in aux_cands:
                if aux == out:
                    continue
                gates = solve_fixed_out_aux(s, out, aux, rows_t, rows_f)
                if gates and verify(gates, out, aux, samples=5000):
                    print("WITNESS")
                    print("size", len(gates), "out", out, "aux", aux)
                    for g in gates:
                        print(g)
                    return 0
    print("EXHAUSTED")
    return 1


if __name__ == "__main__":
    sys.exit(main())