# L-meta-1031 progress (blocked on lower bound / exchange)

## Status
blocked — statement appears true; no Lean proof yet; no counterexample found.

## Statement (plain)
On triangle-free C4-free G, some minimum fan-in-2 AND/OR circuit for the edge function
has every AND owning a star (owned edges share a vertex). Ownership = first true AND on
the single-edge indicator, among ANDs in its cone (TransGen of gate reads).

## Computational evidence
SAT / IDS (AND/OR fan-in 2, no NOT):

| Graph | TF+C4F | VC upper | min size | min has star? | min has nonstar? |
|-------|--------|----------|----------|---------------|------------------|
| edge | yes | 1 | 1 | yes | no |
| paths / stars / forests small | yes | =VC | =VC | yes | no |
| C5 | yes | 7 | 7 | yes | no |
| C6 | yes | 8 | 8 | yes | (star yes; nonstar SAT unfinished) |
| C7 | yes | 10 | 10 | — | — |
| C5+pendant | yes | 8 | 8 | — | — |
| C4 | NO (has C4) | 5 | 3 | no | yes — classic (x0∨x2)∧(x1∨x3) |

All 48 labeled TF+C4F graphs on n≤4: min size = |E|+τ−1.

C4 is exactly the case where min < VC and every min circuit lacks star profile
(so the hypothesis correctly excludes it).

C5 is TF+C4F but NOT Peelable (row_not_cycle5), so L104/L204/L532 do not cover all
TF+C4F graphs. VC optimality for general TF+C4F is open in the repo (note-1:
C5 is outside the long-thread peel).

## Sufficient proof routes
1. Build coverCircuitB from a min vertex cover (in Defs); prove shape, eval, star
   ownership; prove size ≥ |E|+τ−1 for every AND/OR fan-in-2 circuit on TF+C4F.
   Then VC circuit is a min star circuit. Lower bound is the hard part.
2. Take any min circuit; exchange away non-star ANDs without growing size
   (sketch on the gap). Non-star AND on TF graph owns a 2-matching; C4-freeness
   may let one replace a crossing (a∨c)∧(b∨d) block by (a∧b)∨(c∧d) size-neutrally
   when ab,cd are the owned edges — not checked as a general normal form.

## Imports constraint
Outside file may import only Mathlib + PEqualNP.Defs. CoverCircuitB and
EdgeOwnership live in Defs; proofs of L398/L402/L154/L104 do NOT — must be
inlined or rebuilt. Cannot import MetaComplexity.L*.

## Blocking item
A Lean lower bound (or size-neutral exchange to star profile) for arbitrary
triangle-free C4-free graphs on Fin n, against AND/OR fan-in-2 circuits, with
only Defs + Mathlib. Forest/peelable/girth≥7 bounds miss C5 and general cages.

## Files touched this run
Branch only: notes/l-meta-1031/PROGRESS.md (no Outside proof file).
