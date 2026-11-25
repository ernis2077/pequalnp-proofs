# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover upper bound 27 (7 stars + OR-tree)
- Exact1–3 unclean ANDs: UNSAT at size 26
- Leave-k / 6-stars: UNSAT
- Star architecture cannot shave via shared pair-ORs (Fano pairs unique to lines) → always ≥27 for pure stars
- Clean circuits (L1407 hypothesis): C4-free ⇒ size ≥ |E|+τ−1 = 27. So any ≤26 witness **must** be unclean (≥4 unclean ANDs by SAT).
- AND-depth-1 ≥27 (hand; Lean skeleton in HeawoodAndDepthOne.lean)
- Drop-one from cover27 yields h=1 clean near-misses (21); 1-edit exhaustive UNSAT; 2-edit 100k×21 no hit
- Bitmask BFS with fps=0 stuck at miss=1 (same near-miss phenomenon)

## Open SAT (still running, offline leases)
- s26free cadical ~18h+, ~79M+ conflicts
- s26_e4u kissat/cadical (exact 4 unclean) ~10h / 55M+
- s26_e5u cadical+kissat
- s26free kissat --sat

## Blockers
- No size-26 witness found
- Negation needs DRAT/LRAT on full encoding or full C4-free theorem (L612, unclean allowed) — both open
- Leases 410 offline; cannot release/submit via desk
