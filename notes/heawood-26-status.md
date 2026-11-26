# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; exact≤3 unclean UNSAT; leave-k / 6-stars / freeze18–21 size-26 UNSAT (DRAT freeze18)
- Clean (L1407) ⇒ ≥27; unclean ≥4 required for ≤26
- Star OR-tree barrier: pure star covers always ≥27
- AND-depth-1 ⇒ ≥27 (hand sketch); ≤26 needs AND-depth ≥2
- Local near-miss: size-26 with 6 stars misses all 3 edges of one vertex (h=3 on critical rows)
- Aut-canonical first-two-gate reps: 484 (60 with edge-AND first)

## Open SAT (wall ~1d12h+)
| instance | solver | conflicts | status |
|----------|--------|-----------|--------|
| s26free | cadical | ~125M+ | open |
| s26free | kissat --sat | ~217M+ | open |
| s26_e4u | kissat | ~138M+ | open |
| freeze15 | cadical | ~108M+ | open |
| e5u | kissat | ~109M+ | open |
| shards5 (C(7,5)) | kissat 3h | running | open |
| s26_4stars / freeze12 | kissat/cadical | relaunched | open |
| s26_ad2 | kissat/cadical | early | open |
| CP-SAT unclean / FE+ad2 | ortools | running | open |

## Blockers
- No witness; no full free DRAT; L612 (C4-free ≥|E|+τ-1) open
- Leases 410 offline; branch `L-meta-2732` notes + sorry skeleton
- L-meta-972 same theory (PP(3) ≥64)
