# L-meta-1493 search evidence (arc-correct size ≤ 63)

## Statement (search / upper band)

Exists monotone fan-in-2 circuit C, size ≤ 63, that
1. accepts every incident point–line singleton edge of PG(2,3) (difference set `{0,1,3,9}` mod 13);
2. on every input whose **point set is an arc** (≤2 true points per line), acceptance implies some incident pair is present.

Complementary to L-meta-972: exact edge function has monotone size ≥ 64 (and ≤ 64 by vertex-cover construction).

## What would prove the statement

An explicit witness circuit of size ≤ 63, then a Lean Outside file exhibiting it.

## Searches performed

### A. Standard cover = 64, verified arc-correct
Point-cover and line-cover both have size `5·13 - 1 = 64` and compute exact `f_G` (hence are arc-correct). Scripts: `search_arc63.py`, `search_collinear63.py`.

### B. Drop one gate from the cover
- Replace one line gadget by OR4 without AND (size 63): **fails arc soundness** (fires on points of that line with no line selected).
- Omit one point from one line’s OR4 (size 63): **fails completeness** on the omitted point’s edge.
- Exhaustive “drop gate + rewire to an input / false” from both covers: no survivor with full arc soundness (`search_arc63.py`).

### C. Local gadget cannot shrink under don’t-cares
For one line’s five wires `(a,b,c,d,L)`, every fan-in-2 size-3 circuit with output at the last gate was enumerated (`2·5²·2·6²·2·7² = 352800`). **None** matches `L∧(a∨b∨c∨d)` on the domain `wt(a,b,c,d)≤2` (the arc restriction local to that line). Size 2 also none. So a single cover gadget cannot be reduced from 4 to 3 gates by arc don’t-cares alone. Script: `search_local5.py`.

### D. Cover architecture locked at 64 (proof sketch)
Any two points’ line-neighborhoods intersect in **at most one** line (dual: two lines meet in one point). Therefore no size-2 or size-3 intermediate OR-support can lie in two different neighborhood-OR4 targets, so the thirteen OR4 trees share **no** internal gates: exactly `13×3 = 39` neighborhood ORs. Plus 13 ANDs and a 12-gate OR-tree ⇒ **64**. Cover-shaped circuits cannot reach 63. CSE over 200 seeds never beat 39 (`search_share63.py`).

### E. No arc-domain wire merge in the size-64 cover
Fingerprints of all wires over arcs × sampled line masks: **0** equivalent pairs among distinct wires (`search_merge63.py`). So no gate is redundant on the arc domain.

### F. Stochastic local search
Genetic/MCMC from the cover for 120s (`search_genetic63.py`): 157 trials, **0** accepts that preserve completeness + sampled soundness while shrinking; best remains `(0,0,64)`.

### G. Structural obstruction sketch (not Lean-checked)
Exact `f_G` has size exactly 64 on this C4-free incidence graph (972 + cover). Arc don’t-cares only free behaviour on inputs with some line carrying ≥3 points. Useful unclean ANDs that fire only off arcs need width ≥3 (e.g. collinear triples), which cost more than the single gate one would hope to save; unclean ANDs that fire on non-edges that are still arcs break the clean-support counting used for `|E|+τ-1` and, in cover-shaped templates, have not yielded a net saving in search.

### H. Non-cover templates
- 12 stars + 4 direct edge-ANDs: size 67
- 12 stars + (OR3∧p) + (p∧L): size 65
- Difference-set layers: ≥103 without a new idea
- Random size-63 AND-biased circuits (16k trials): best still miss ≥34 edges on completeness (`search_noncover63.py`)

### I. Minterm shape of any arc-correct monotone g
Completeness + arc soundness ⇒ size-2 minterms of g are exactly the 52 edges; any extra minterm has size ≥3, contains no edge, and its point-set is a non-arc (must include a collinear triple). So g = f_G ∨ (collinear-triple terms). Grafting Collinear3 onto the cover via `(L∨Thresh3)∧OR4` **increases** gate count; no ≤63 build found.

## Verdict tendency

**Likely `statement_seems_false`**: no ≤63 witness; cover architecture provably stuck at 64; local size-3 impossible; drop-one / merge / non-cover templates fail. Residual risk: an exotic unclean circuit outside these templates.

## Files
- `scratch/search_arc63.py`
- `scratch/search_merge63.py`
- `scratch/search_collinear63.py`
- `scratch/search_local5.py`
- `scratch/search_share63.py`
- `scratch/search_genetic63.py`
- `scratch/ilp_or4.py`
- `lean/PEqualNP/Outside/L_meta_1493.lean` (skeleton with `sorry` only — do not PR)
