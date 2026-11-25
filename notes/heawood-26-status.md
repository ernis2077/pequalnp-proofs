# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; exact≤3 unclean UNSAT; leave-k / 6-stars UNSAT
- Clean (L1407) ⇒ ≥27; unclean ≥4 required for ≤26
- Freeze 21/18 (7/6 complete stars) size-26 UNSAT (DRAT for freeze18)
- Local search stuck at h≥1; star OR-tree ⇒ 7 stars need 27 gates

## Open SAT (~34h wall)
| instance | solver | conflicts | status |
|----------|--------|-----------|--------|
| s26free | cadical | ~122M | open |
| s26free | kissat --sat | ~200M+ | open |
| s26_e4u | kissat | ~132M | open |
| freeze15 | cadical | ~100M | open |
| e5u | kissat | ~open | open |

## Blockers
- No witness, no full DRAT, L612 open, leases 410 offline
- Branch `L-meta-2732` @ notes + sorry skeleton
