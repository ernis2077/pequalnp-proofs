#!/usr/bin/env python3
"""Bit-parallel local search for a size-19 (or less) circuit for Petersen edges.

Shard-aware modes:
  --shard 3  first gate is NOT of an input (Aut-fixed to NOT(0))
  --shard -1 any first gate

Uses 1024-bit truth tables packed into 16 uint64 words.
"""

from __future__ import annotations

import argparse
import random
import time

EDGES = [
    (0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
    (0, 5), (1, 6), (2, 7), (3, 8), (4, 9),
    (5, 7), (7, 9), (9, 6), (6, 8), (8, 5),
]
N = 10
M = 1 << N
WORDS = M // 64  # 16


def pack_targets():
    bits = [0] * M
    for a, b in EDGES:
        for m in range(M):
            if ((m >> a) & 1) and ((m >> b) & 1):
                bits[m] = 1
    words = [0] * WORDS
    for m, bit in enumerate(bits):
        if bit:
            words[m >> 6] |= 1 << (m & 63)
    return words, bits


TARGET_WORDS, TARGET_BITS = pack_targets()


def pack_input(i: int) -> list[int]:
    words = [0] * WORDS
    for m in range(M):
        if (m >> i) & 1:
            words[m >> 6] |= 1 << (m & 63)
    return words


INPUT_WORDS = [pack_input(i) for i in range(N)]


def band(a, b):
    return [x & y for x, y in zip(a, b)]


def bor(a, b):
    return [x | y for x, y in zip(a, b)]


def bnot(a):
    mask = (1 << 64) - 1
    return [mask ^ x for x in a]


def eval_words(gates):
    w = list(INPUT_WORDS)
    for op, a, b in gates:
        if op == 0:  # and
            w.append(band(w[a], w[b]))
        elif op == 1:  # or
            w.append(bor(w[a], w[b]))
        else:  # not
            w.append(bnot(w[a]))
    return w[-1]


def mismatches(words) -> int:
    # popcount of XOR with target
    x = 0
    for u, v in zip(words, TARGET_WORDS):
        x += (u ^ v).bit_count()
    return x


def random_circuit(S: int, shard: int, rng: random.Random):
    gates = []
    for g in range(S):
        nw = N + g
        if g == 0 and shard == 3:
            gates.append((2, 0, 0))  # NOT(0)
            continue
        if g == 0 and shard == 0:
            gates.append((0, 0, 1))  # AND of edge (0,1)
            continue
        op = rng.randrange(3)
        a = rng.randrange(nw)
        b = rng.randrange(nw)
        if op != 2 and a > b:
            a, b = b, a
        if op == 2:
            b = a
        gates.append((op, a, b))
    return gates


def cover_circuit():
    """Known size-20 monotone cover circuit."""
    cover = (0, 1, 3, 7, 8, 9)
    rem = list(EDGES)
    blocks = []
    for c in cover:
        neigh, new = [], []
        for e in rem:
            if e[0] == c or e[1] == c:
                neigh.append(e[1] if e[0] == c else e[0])
            else:
                new.append(e)
        rem = new
        blocks.append((c, neigh))
    gates = []

    def add(op, a, b):
        gates.append((op, a, b))
        return N + len(gates) - 1

    ands = []
    for c, neigh in blocks:
        cur = neigh[0]
        for x in neigh[1:]:
            cur = add(1, cur, x)
        ands.append(add(0, c, cur))
    cur = ands[0]
    for x in ands[1:]:
        cur = add(1, cur, x)
    return gates


def mutate(gates, shard, rng: random.Random):
    g = gates[:]
    S = len(g)
    i = rng.randrange(S)
    if i == 0 and shard in (0, 3):
        # keep first gate shape; maybe flip which input for shard3? fixed to 0
        if shard == 3:
            return g
        # shard 0: can remap edge ends among Aut-orbit — keep (0,1)
        return g
    nw = N + i
    kind = rng.randrange(3)
    if kind == 0:
        op = rng.randrange(3)
        a = rng.randrange(nw)
        b = rng.randrange(nw)
        if op != 2 and a > b:
            a, b = b, a
        if op == 2:
            b = a
        g[i] = (op, a, b)
    elif kind == 1:
        op, a, b = g[i]
        a2 = rng.randrange(nw)
        b2 = b if op == 2 else rng.randrange(nw)
        if op != 2 and a2 > b2:
            a2, b2 = b2, a2
        g[i] = (op, a2, b2)
    else:
        # swap two gates' ops if both AND/OR
        j = rng.randrange(S)
        if j == 0 and shard in (0, 3):
            return g
        if g[i][0] < 2 and g[j][0] < 2:
            gi, gj = list(g[i]), list(g[j])
            gi[0], gj[0] = gj[0], gi[0]
            g[i], g[j] = tuple(gi), tuple(gj)
    return g


def shrink_from_cover(rng: random.Random):
    """Start from size 20, delete one gate by rewiring consumers to one of its inputs."""
    base = cover_circuit()
    assert len(base) == 20
    assert mismatches(eval_words(base)) == 0
    # Try each gate deletion
    for del_i in range(20):
        op, a, b = base[del_i]
        # replacement wire candidates: a, b (or a for NOT)
        cands = [a] if op == 2 else [a, b]
        for repl in cands:
            # Build size-19: skip del_i; map old wires -> new
            # old wire N+k for k<del_i stays; for k>del_i maps to N+k-1
            def map_w(w):
                if w < N:
                    return w
                g = w - N
                if g == del_i:
                    return None  # must not appear
                if g > del_i:
                    return N + g - 1
                return w

            new = []
            ok = True
            for k, (opk, ak, bk) in enumerate(base):
                if k == del_i:
                    continue
                ak2 = repl if ak == N + del_i else map_w(ak)
                bk2 = repl if bk == N + del_i else map_w(bk)
                if ak2 is None or bk2 is None:
                    ok = False
                    break
                new.append((opk, ak2, bk2))
            if not ok or len(new) != 19:
                continue
            miss = mismatches(eval_words(new))
            if miss == 0:
                return new
    return None


def hillclimb(S: int, shard: int, seconds: float, seed: int):
    rng = random.Random(seed)
    # Prefer starting near cover for non-NOT shards
    if shard == 3:
        cur = random_circuit(S, shard, rng)
    else:
        base = cover_circuit()
        if S == 19:
            # drop last OR and hope to repair, or random
            cur = base[:-1]
            # rewire last to be OR of previous last inputs roughly
            # just randomize last few
            for i in range(max(0, S - 6), S):
                nw = N + i
                cur[i] = (1, rng.randrange(nw), rng.randrange(nw))
        elif S == 20:
            cur = base
        else:
            cur = random_circuit(S, shard, rng)
    cur_m = mismatches(eval_words(cur))
    best = cur
    best_m = cur_m
    t0 = time.time()
    steps = 0
    while time.time() - t0 < seconds:
        steps += 1
        nxt = mutate(cur, shard, rng)
        m = mismatches(eval_words(nxt))
        if m <= cur_m or rng.random() < 0.01:
            cur, cur_m = nxt, m
            if m < best_m:
                best, best_m = nxt, m
                print(f"seed={seed} best_m={best_m} steps={steps} t={time.time()-t0:.1f}", flush=True)
                if best_m == 0:
                    return best
        if steps % 50000 == 0 and time.time() - t0 > 1:
            # occasional restart
            if best_m > 0 and rng.random() < 0.3:
                cur = random_circuit(S, shard, rng)
                cur_m = mismatches(eval_words(cur))
    print(f"seed={seed} done best_m={best_m} steps={steps}", flush=True)
    return best if best_m == 0 else None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--size", type=int, default=19)
    ap.add_argument("--shard", type=int, default=3)
    ap.add_argument("--seconds", type=float, default=60)
    ap.add_argument("--seeds", type=int, default=4)
    args = ap.parse_args()

    hit = shrink_from_cover(random.Random(0))
    print("shrink_from_cover", "HIT" if hit else "miss", flush=True)
    if hit:
        print(hit)
        return

    for s in range(args.seeds):
        w = hillclimb(args.size, args.shard, args.seconds, seed=s + 1)
        if w is not None:
            print("WITNESS", w)
            assert mismatches(eval_words(w)) == 0
            return
    print("no witness")


if __name__ == "__main__":
    main()
