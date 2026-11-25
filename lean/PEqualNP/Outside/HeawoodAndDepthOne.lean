import Mathlib
import PEqualNP.Defs

/-!
# AND-depth-1 lower bound for the Heawood edge function

Hand derivation for L-meta-582 / L-meta-971 (research note on pequalnp): every Monotone2
circuit of AND-depth 1 for the Heawood edge function has size at least 27
(`|E| + τ - 1 = 21 + 7 - 1`). The matching upper bound of 27 is the seven-star cover
(L105 / `EdgeUpper`).

Consequence for `L-meta-2732`: a size-≤26 witness must have AND-depth at least 2
(some AND gate reads an AND wire).

Argument sketch under C4-freeness:
1. Each AND below only ORs computes `∨_{a∈A,b∈B} x_a x_b` for a biclique; C4-free ⇒ star.
2. Centres of those stars form a vertex cover (`τ ≥ 7`).
3. Leaf-OR DAGs are centre-private (two vertices share ≤1 neighbour).
4. Size ≥ ∑_c (|U_c| − m_c) + t + (t − 1) = ∑|U_c| + t − 1 ≥ 21 + 7 − 1 = 27.
-/

namespace PEqualNP.Outside.HeawoodAndDepthOne

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def heawoodEdges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

def heawoodEdgeFn (x : Fin 14 → Bool) : Bool :=
  decide (∃ u v : Fin 14, (u.val, v.val) ∈ heawoodEdges ∧ x u = true ∧ x v = true)

/-- Wire `w` is a gate wire whose gate is an AND. -/
def isAndWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  ∃ _ : n ≤ w, ∃ g, C.gates[w - n]? = some g ∧ g.op = GateOp.and

/-- AND-depth ≤ 1: every AND gate's inputs are variables or non-AND gate wires. -/
def AndDepthAtMostOne (n : ℕ) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.and → ∀ w ∈ g.inputs, ¬ isAndWire n C w

/-- AND-depth-1 Monotone2 circuits for the Heawood edge function need ≥ 27 gates. -/
theorem heawood_and_depth_one_ge_27
    (C : Circuit) (_hM : Monotone2 C)
    (_hF : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = heawoodEdgeFn x)
    (_hD : AndDepthAtMostOne 14 C) :
    27 ≤ C.size := by
  sorry

end PEqualNP.Outside.HeawoodAndDepthOne
