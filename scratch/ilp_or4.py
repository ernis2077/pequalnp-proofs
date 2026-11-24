#!/usr/bin/env python3
"""ILP: minimum number of binary OR gates to compute all 13 four-ORs
of lines-through-points (point-cover neighborhood ORs).

If optimum is 39, then cover construction cannot save an OR there.
"""
from __future__ import annotations

import itertools
import sys

DIFF = (0, 1, 3, 9)
N = 13
LINE_PTS = [tuple(sorted((w + d) % N for d in DIFF)) for w in range(N)]
PT_LINES = [tuple(sorted(w for w in range(N) if p in LINE_PTS[w])) for p in range(N)]

try:
    import pulp
except ImportError:
    import subprocess
    subprocess.check_call([sys.executable, "-m", "pip", "install", "pulp", "-q"])
    import pulp


def min_or_circuit(max_gates: int = 39) -> int:
    """Return minimum gates if <= max_gates, else -1.

    Model: wires 0..12 are line inputs. Gates 0..G-1 produce wires 13..13+G-1.
    Each gate ORs two earlier wires. For each point p, some wire equals OR of PT_LINES[p]
    on all 2^13 inputs — encoded by requiring the gate's support (set of input lines)
    equals the target set. We track support as a bitset constraint.
    """
    # Support-based model without evaluating all inputs:
    # Each wire has a subset of {0..12} as its OR-support (the lines it ORs).
    # Input wire i has support {i}.
    # Gate OR of a,b has support = support(a) ∪ support(b).
    # Need for each point p a wire with support == set(PT_LINES[p]).
    #
    # Variables: for gate g, choose two parents; support computed.
    # This is still tricky in ILP. Use: enumerate all useful supports —
    # only subsets that appear as unions along the way. The relevant supports
    # are subsets of some point's 4-set (since we never need other ORs?).
    # Actually optimal may compute OR of lines from different points' sets.
    # All 2^13 subsets is too many.
    #
    # Restrict: only allow supports that are nonempty subsets of some PT_LINES[p]
    # (subsets of blocks of the dual). Each block has 4 lines, 15 nonempty subsets,
    # 13 blocks, but overlap: total unique subsets.
    allowed = set()
    for p in range(N):
        s = PT_LINES[p]
        for k in range(1, 5):
            for comb in itertools.combinations(s, k):
                allowed.add(frozenset(comb))
    allowed = list(allowed)
    print("allowed supports", len(allowed))
    idx = {s: i for i, s in enumerate(allowed)}

    # Also need singletons of all lines
    for i in range(N):
        assert frozenset([i]) in idx

    # ILP: binary var x_{s} = whether we compute support s (for |s|>1, costs a gate)
    # For |s|>1, must have s = a ∪ b with a,b proper, x_a = x_b = 1, and a,b nonempty.
    # Minimize sum_{|s|>1} x_s, subject to each target 4-set having x=1.
    prob = pulp.LpProblem("or4", pulp.LpMinimize)
    x = {
        s: pulp.LpVariable(f"s{idx[s]}", 0, 1, pulp.LpInteger) for s in allowed
    }
    # singletons free and forced
    for i in range(N):
        prob += x[frozenset([i])] == 1

    # targets
    for p in range(N):
        prob += x[frozenset(PT_LINES[p])] == 1

    # for each non-singleton, require a decomposition
    # y_{s,a,b} = use a,b to build s
    for s in allowed:
        if len(s) <= 1:
            continue
        decomps = []
        elems = list(s)
        for mask_a in range(1, 1 << len(elems)):
            a = frozenset(elems[i] for i in range(len(elems)) if mask_a & (1 << i))
            need = s - a
            base = list(need)
            free = list(a)
            for fm in range(1 << len(free)):
                b = frozenset(base) | frozenset(
                    free[i] for i in range(len(free)) if fm & (1 << i)
                )
                if not b:
                    continue
                if a not in idx or b not in idx:
                    continue
                if a == s or b == s:
                    continue
                decomps.append((a, b))
        decomps = list({(a, b) for a, b in decomps})
        if not decomps:
            prob += x[s] == 0
            continue
        ys = []
        for j, (a, b) in enumerate(decomps):
            y = pulp.LpVariable(f"y{idx[s]}_{j}", 0, 1, pulp.LpInteger)
            ys.append(y)
            prob += y <= x[a]
            prob += y <= x[b]
        prob += x[s] <= pulp.lpSum(ys)

    prob += pulp.lpSum(x[s] for s in allowed if len(s) > 1)
    status = prob.solve(pulp.PULP_CBC_CMD(msg=False, timeLimit=120))
    val = int(pulp.value(prob.objective)) if pulp.LpStatus[status] == "Optimal" else -1
    print("status", pulp.LpStatus[status], "obj", val)
    return val


def main():
    v = min_or_circuit()
    print("min OR gates for 13xOR4 (restricted supports)", v)
    # Standard lower bound without sharing across: 39
    # If v < 39, we can build size 13+v+12 = v+25 cover ≤ 63 when v≤38


if __name__ == "__main__":
    main()
