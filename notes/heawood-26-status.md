# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover upper bound 27 (7 stars + OR-tree)
- Exact1–3 unclean ANDs: UNSAT at size 26
- Leave-k / 6-stars: UNSAT
- Star architecture cannot shave via shared pair-ORs (Fano pairs unique to lines) → always ≥27 for pure stars
- Clean circuits (L1407): C4-free ⇒ size ≥ |E|+τ−1 = 27. Any ≤26 witness **must** be unclean (≥4 unclean ANDs).
- AND-depth-1 ≥27 (hand; Lean skeleton)
- Drop-one h=1 near-misses: 1-edit UNSAT; heavy 2-edit no hit
- Bitmask fps=0 stuck at miss=1
- **Freeze 21 stars (all 7) into size-26: UNSAT** (need 6 combine ORs)
- **Freeze 18 (6 complete stars) into size-26: UNSAT** (~290s kissat). So ≤5 complete stars in any size-26.

## Open
- Freeze 15 (5 stars) — timeout 900s; 1h kissat running
- s26free cadical ~19h+, ~81M+ conflicts
- s26_e4u / e5u still open

## Blockers
- No size-26 witness; negation needs full DRAT or L612
- Leases 410 offline
