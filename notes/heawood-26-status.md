# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; ≤3 unclean / leave-k / 6-stars / freeze18–21 size-26 UNSAT
- Clean ⇒ ≥27 (L1407); AND-depth-1 ⇒ ≥27; need unclean≥4 and AND-depth≥2
- Star/edge-AND/OR-tree lower bound ≥27 (deg≤3 arithmetic)
- Near-miss h=1 (6 full + 1 partial star); pair_merge exhaustive stays h≥1
- h2 prefix freeze18 remainder UNSAT (cadical)
- shards5 first wave: 3× TIMEOUT @ 3h; wave2 @ 6h running
- Z3 FE 2h UNKNOWN; beam400 stuck h=6

## Open (~1d16h wall)
| instance | conflicts | status |
|----------|-----------|--------|
| s26free cadical | ~128M | open |
| s26free kissat-sat | ~220M+ | open |
| s26_e4u / e5u / freeze15 / 4stars / ad2 / h1sat | running | open |
| CP-SAT unclean | slow | open |

## Blockers
- No witness; no free DRAT; L612 open; leases 410 offline
- Branch `L-meta-2732` notes + sorry skeleton; L-meta-972 same theory
