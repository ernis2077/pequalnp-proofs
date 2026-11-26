# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; ≤3 unclean / 6-stars / freeze18–21 UNSAT; h1 & h2 prefix freeze18 UNSAT
- Clean / AND-depth-1 / star+edgeAND architectures ⇒ ≥27
- Near-miss h=1 exhaustive pair_merge cannot repair
- Culled redundant solvers; focusing free / e4u / freeze15 / 4stars / ad2 / shards5

## Open (~1d19h wall)
| instance | conflicts | status |
|----------|-----------|--------|
| s26free cadical | ~130M | open |
| s26free kissat-sat | running | open |
| s26_e4u kissat | ~143M+ | open |
| freeze15 cadical | ~115M+ | open |
| 4stars / ad2 / shards5-w2 / h1 freeze12 | running | open |

## Blockers
- No witness; no free DRAT; L612 open; leases 410 offline
- Branch `L-meta-2732` building
