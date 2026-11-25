# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover upper bound 27 (7 stars + OR-tree)
- Exact1–3 unclean ANDs: UNSAT at size 26
- Leave-k / 6-stars: UNSAT
- Star architecture cannot shave via shared pair-ORs (Fano pairs unique to lines) → always ≥27 for pure stars
- AND-depth-1 ≥27 (hand argument; Lean skeleton)
- Drop-one from cover27 yields h=1 clean near-misses (21 such); 1-edit exhaustive UNSAT; 2-edit 100k×21 no hit

## Open SAT (still running)
- s26free cadical ~16h+, ~75M conflicts
- s26_e4u kissat/cadical (exact 4 unclean)
- s26_e5u restarted
- free26b, s25b

## Blockers
- No size-26 witness found
- Negation needs DRAT/LRAT on full encoding or C4-free theorem (L612) — both open
- Leases 410 offline
