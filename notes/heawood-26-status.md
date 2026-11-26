# Heawood ≤26 search status (L-meta-2732)

## Settled
- Cover 27; exact≤3 unclean UNSAT; leave-k / 6-stars / freeze18–21 size-26 UNSAT (DRAT freeze18)
- Clean (L1407) ⇒ ≥27; unclean ≥4 required for ≤26; AND-depth-1 ⇒ ≥27
- Star+edgeAND+OR-tree architectures: with deg≤3, ≤6 stars cover ≤18 edges ⇒ ≥3 singleton edge-ANDs ⇒ size ≥29; 7 stars ⇒ 27. Pure star/edge-OR-tree cannot hit 26.
- Near-misses: h=1 = six full stars + one 2-edge partial (misses one graph edge); 1-edit UNSAT; exhaustive pair_merge / 3+upgrade stay at h≥1
- h=2 prefix (5 stars+star1) freeze18 remainder: cadical **UNSAT**
- Aut first-two reps: 484

## Open SAT
| instance | conflicts | status |
|----------|-----------|--------|
| s26free cadical | ~126M | open (~1d14h) |
| s26free kissat-sat | ~220M | open |
| s26_e4u | ~139M | open |
| freeze15 | ~109M | open |
| shards5 / 4stars / ad2 / h1sat | running | open |
| CP-SAT unclean, Z3 bitmask | running | open |

## Blockers
- No witness; no full free DRAT; L612 open; leases 410 offline
- L-meta-972 same C4-free ≥|E|+τ-1 theory
