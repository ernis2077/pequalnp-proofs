# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover upper bound 27 (7 stars + OR-tree)
- Exact1–3 unclean ANDs: UNSAT at size 26
- Leave-k / 6-stars: UNSAT  
- Pure star OR-DAG sharing cannot beat 27 (Fano pairs unique per line)
- Clean circuits (L1407 / C4-free): ≥27. Any ≤26 must be unclean (≥4 unclean ANDs).
- **Freeze 21 (7 stars) size-26: UNSAT**; **freeze 18 (6 stars) size-26: UNSAT** (~290s, DRAT ~140MB at `/tmp/heawood/cnf/freeze18.drat`)
- Drop-one / local search: persistent h=1 clean near-misses; h=3 size-26 missing one vertex’s 3 edges; cannot locally repair
- Star OR-tree lower bound: t independent star outputs need t−1 ORs ⇒ 7 stars ⇒ 27

## Open SAT (still running)
- s26free cadical **~25.5h+, >100M conflicts** — no decision
- s26_e4u kissat/cadical ~17h / ~95M
- s26_e5u; freeze15 cadical (~5h); and07_nouse variants

## Blockers
- **No size-26 witness**
- **No full-encoding DRAT** for free UNSAT yet (would prove ¬∃≤26 / ¬2732)
- L612 (unclean C4-free ≥|E|+τ−1) would kill 2732 but is open
- Leases 410 offline — cannot desk submit/release

## Branch
`L-meta-2732` — sorry skeleton + research notes; no PR until green proof
