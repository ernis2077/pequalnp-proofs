# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; ≤3 unclean / leave-k / 6-stars / freeze18–21 size-26 UNSAT
- Clean ⇒ ≥27; AND-depth-1 ⇒ ≥27; star/edge-AND/OR-tree ⇒ ≥27
- h=1 near-miss (6 full + 1 partial); pair_merge exhaustive h≥1
- h2 prefix freeze18 UNSAT; h1 prefix freeze18 UNSAT (cadical)
- Z3 FE 2h / CP-SAT 2h UNKNOWN; beam stuck

## Open (~1d17h)
| instance | conflicts | status |
|----------|-----------|--------|
| s26free cadical | ~128M | open |
| s26free kissat-sat | ~220M+ | open |
| s26_e4u | ~143M | open |
| freeze15 | ~114M | open |
| 4stars / ad2 / shards5-w2 | running | open |
| CP-SAT unclean 24h | restarted | open |

## Blockers
- No witness; no free DRAT; L612 open; leases 410 offline
