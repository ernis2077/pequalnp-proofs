# VERDICT: L-meta-2029

**Gap:** L-meta-2029  
**Branch:** `cursor/l-meta-2029-49b5`  
**Disposition:** `statement_seems_false` (no PR)  
**Lease:** `495ae2e7-c034-4af9-b06e-3630994c1872` (beat/release returned HTTP 410 — expired before release)

## Posted statement (negation)

L-meta-2029 is the literal negation of **L-meta-606**:

- **L-meta-606 (conjecture):** ∃ c : ℕ, ∀ n, ∀ G on `Fin n` with girth ≥ 5, ∀ monotone-2 circuit D computing the edge function, `|E(G)| ≤ c · (D.size + 1)`.
- **L-meta-2029:** ¬ that existential.

A proof of L-meta-2029 is therefore **one explicit counterexample** to L-meta-606: for some fixed c, some girth-≥5 graph G, and some monotone circuit D for the edge function with `|E| > c · (D.size + 1)`.

The desk sketch matches this: *"A proof is one explicit counterexample to the positive statement L-meta-606; none is expected if that statement is true."*

## Assessment

### 1. Logical shape

Proving L-meta-2029 requires showing **no uniform linear compression constant** exists. Equivalently, for every c there must be n, G (girth ≥ 5), and D with `|E| > c · (D.size + 1)` while D still computes

`decide (∃ i j, G.Adj i j ∧ x i ∧ x j)`.

We found **no such family**, and the active fleet route targets the **opposite** bound with c = 1.

### 2. Parallel attack on L-meta-606 (the positive conjecture)

L-meta-606 is sharded on main; shard 3 is explicitly *"refute: a family … size below every constant times the incident pairs"* — i.e. the refutation lane lives **inside** the 606 attack, not as a finished 2029 proof.

Checked lemmas in the same regime (no 4-cycle / girth ≥ 5, monotone edge function, vertex cover):

| Lemma | Content (informal) |
|--------|---------------------|
| `L_meta_1737` | On acyclic G with no C4: `|E| + τ ≤ D.size + 1` for minimum vertex cover τ |
| `R_meta_612_*` | Reducers toward `|E| + t ≤ C.size + 1` under C4-free + cover hypotheses |
| WIP `L_meta_606` (local, ~2100 lines) | Pipeline: girth ≥ 5 ⇒ no C4 ⇒ minimum cover `t` ⇒ `Count.main_bound` ⇒ `|E| ≤ D.size + 1` (c = 1) |

The WIP `L_meta_606` file in the workspace (`lean/PEqualNP/Outside/L_meta_606.lean`, not on `main`) **does not build** (multiple Lean errors in `Count` / `Girth`), but its **`main_bound`** statement is exactly the c = 1 target:

```text
G.edgeSet.ncard + t ≤ s + 1   when C.size = s and D computes the edge function
```

With minimum vertex cover on n vertices, `t ≤ n`, so the intended conclusion is **linear** (indeed **affine**) in circuit size, not superlinear compression.

### 3. Counterexample search (informal)

To disprove the conjecture one needs **many edges** but a **small** monotone circuit. Standard tricks fail the hypotheses:

- **Dense / random graphs:** girth ≥ 5 with many edges is possible (high-girth expanders), but constructing a monotone D with `D.size ≪ |E|/c` that still recognizes an edge with both endpoints true requires encoding adjacency; without short cycles, biclique-type compression is limited — the fleet’s `CoverPromise` / `main_bound` line of attack is exactly ruling this out.
- **Wiring one AND per edge:** trivial D with `|E|` gates satisfies `|E| ≤ |E| · (size + 1)`; does **not** break c = 1 for large c, but for c = 1 one needs `size ≥ |E| - 1`, i.e. no compression — consistent with the conjecture.
- **No finite gadget** was identified where `|E| / (D.size + 1)` is unbounded under girth ≥ 5.

### 4. Could L-meta-2029 still be true?

Only if L-meta-606 is **false**. That would require a girth-≥5 family with **unbounded** ratio `|E| / (D.size + 1)` for **some** correct monotone D — i.e. asymptotic compression beyond any constant factor. The fleet’s documented strategy and partial proofs point to **|E| ≤ D.size + O(1)** (cover size folded into gates), not to separating examples.

We did **not** obtain a machine-checked proof of L-meta-606 on `main`; the local 606 file is incomplete. So this verdict is **mathematical / strategic**, not a Lean refutation of 2029 inside the repo.

## Conclusion

**L-meta-2029 should not be pursued as a provable gap:** the negation is unlikely to hold; the conjecture L-meta-606 (linear — in fact c = 1 in the WIP route) is the plausible true statement. A proof of 2029 would be a major lower-bound **failure** for the girth-≥5 monotone edge-function program.

**Recommended desk action:** release with `reason=statement_seems_false`.

**Proof route if the desk disagrees:** exhibit ∀c, an explicit `(n, G, D)` in Lean with girth ≥ 5 and `G.edgeFinset.card > c * (D.size + 1)`; otherwise the cut remains `missing_lemma` on the 606 side, not a 2029 proof.

## Verification performed

- Read gap JSON `.pnp/L-meta-2029.json` and sibling L-meta-606 metadata.
- Compared statements; inspected WIP `L_meta_606.lean` and checked `lake build PEqualNP.Outside.L_meta_606` (fails; see build log).
- Reviewed checked `L_meta_1737` and reducer lemmas `R_meta_612_*`.
- Attempted `tools/pnp.sh beat L-meta-2029` and desk `release?reason=statement_seems_false` (lease already dead, 410).