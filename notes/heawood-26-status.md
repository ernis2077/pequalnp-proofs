# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover upper bound 27 (7 stars + OR-tree)
- Exact1–3 unclean ANDs: UNSAT at size 26
- Leave-k / 6-stars: UNSAT  
- Pure star OR-DAG sharing cannot beat 27 (Fano pairs unique per line)
- Clean circuits (L1407 / C4-free): ≥27. Any ≤26 must be unclean (≥4 unclean ANDs).
- **Freeze 21 (7 stars) size-26: UNSAT**; **freeze 18 (6 stars) size-26: UNSAT** (~290s, DRAT ~140MB)
- Drop-one / local search: h=1 clean near-misses; h=3 size-26 missing one star’s edges; no local repair
- Star OR-tree lower bound: 7 stars ⇒ 27 gates

## Open SAT (still running)
- s26free cadical **~28h+, ~108M+ conflicts** — no decision
- s26_e4u kissat **~19h / ~108M** — no decision
- freeze15 / e5 / and07 variants still open

## Blockers
- No size-26 witness; no full-encoding DRAT
- L612 open; leases 410 offline
- Branch `L-meta-2732` has sorry + notes only
