# L-meta-1493 — outcome

## Verdict

**NONE** — no ≤63 fan-in-two AND/OR circuit found for the order-3 plane
arc-window incidence property. Existential looks **false**; matches the
cover / paper lower bound **|E| + τ − 1 = 52 + 13 − 1 = 64** (twin
L-meta-972: size ≥ 64 for the exact edge function).

Recommended desk release: `statement_seems_false`.

## Why the existential should be false

1. **Necessary constraints from the arc statement**
   - Completeness on all 52 incident point–line pairs.
   - Every weight-2 non-edge is an arc, so soundness forces the circuit
     false on all weight-2 non-edges.
   - Monotone + those constraints ⇒ the size-2 minterms are exactly the
     edges; the circuit computes some `g ≥ f_G` that may only add
     minterms that are edge-free **non-arcs** (e.g. 3 collinear points).

2. **Matching upper bound at 64**
   - Vertex-cover construction (L-meta-105): size `|E| + |T| − 1 = 64`
     for exact `f_G`, hence also for the weaker arc property.
   - Point-cover and line-cover both realize size 64; verified
     arc-correct in `scratch/search_arc63_fast.py`.

3. **Search failed to beat 64**
   - Drop any one gate from either cover + rewire consumers → never
     keeps completeness + weight-2 soundness.
   - Single-gate rewires of the cover: 7232 tried, 0 passed completeness
     + weight-2 + no-line arc filters.
   - Mutate cover (1–3 flips/rewires) then drop a gate: 36984 drop
     attempts, 0 passed the same cheap filters at size ≤ 63.
   - Random shrink / local search from the cover: no ≤ 63 arc-correct
     circuit.
   - Per-line exact contribution `L ∧ OR4(points)` has no 3-gate
     monotone fan-in-2 circuit (exhaustive), so the separated
     cover accounting cannot fall below 13×4 + 12 = 64 without
     cross-gadget sharing that the plane’s pencil intersections
     (size 1) do not provide for free.

4. **Relation to L-meta-972**
   - 972 asks `64 ≤ size` for the **exact** edge function on this
     C4-free graph (WIP: clean bound + τ = 13).
   - 1493 is the opposite **search** for size ≤ 63 on the **arc-window**
     relaxation. No witness; bound matches. Closing the arc window as a
     place to look below the cover size.

## Lease

Original lease `1117b728-ac26-4f5a-bd84-3739dc658c95` expired mid-run
(410). Desk rate-limited reclaim. Parent should release when a lease is
held:

```
POST /desk/release?lease=<id>&reason=statement_seems_false
```

## Artifacts

- `scratch/search_arc63_fast.py` — bit-parallel completeness / arc checks,
  drop-search, shrink (sha256 `23da6fbf76c45ca2bb7fd6661eead0c1023efa3a2cb56af972cb63cbc0ffc50c`)
- `scratch/search_arc63.py` — earlier slower search harness
- No Lean file / PR (existential false; nothing to encode)

## Not done

- Full Lean refute `¬∃ C, … size ≤ 63 …` (same difficulty band as 972).
- Exhaustive synthesis over all size-63 circuits (infeasible); conclusion
  is search + matching bound, not a machine-checked nonexistence proof.
