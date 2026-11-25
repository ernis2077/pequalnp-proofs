import Mathlib
import PEqualNP.Defs

/-!
# AND-depth-1 lower bound for the Heawood edge function

Hand derivation for L-meta-582 / L-meta-971: every Monotone2 circuit of AND-depth 1 for
the Heawood edge function has size at least 27 (`|E| + τ - 1`). Hence a size-≤26 witness
for `L-meta-2732` must have AND-depth ≥ 2.

Argument sketch (C4-free): each AND below only ORs computes a star; centres cover;
leaf-OR DAGs are centre-private; size ≥ `|E| + τ - 1`.
-/

namespace PEqualNP.Outside.HeawoodAndDepthOne

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def heawoodEdges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

def heawoodEdgeFn (x : Fin 14 → Bool) : Bool :=
  decide (∃ u v : Fin 14, (u.val, v.val) ∈ heawoodEdges ∧ x u = true ∧ x v = true)

/-- Wire `w` is a gate wire (`w ≥ n`) whose gate is an AND. -/
def isAndWire (n : ℕ) (C : Circuit) (w : ℕ) : Prop :=
  n ≤ w ∧ w - n < C.gates.length ∧ (C.gates[w - n]!).op = GateOp.and

/-- AND-depth ≤ 1: every AND gate reads only input wires or OR-gate wires
(no AND wire among its direct inputs; inductively no AND ancestors). -/
def AndDepthAtMostOne (n : ℕ) (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, g.op = GateOp.and → ∀ w ∈ g.inputs, ¬ isAndWire n C w

/-- Seven-star cover: `|E| + τ - 1 = 27` gates. -/
theorem heawood_edge_upper_27 :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ 27 ∧
      (∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = heawoodEdgeFn x) := by
  sorry

/-- AND-depth-1 Monotone2 circuits for Heawood need ≥ 27 gates. -/
theorem heawood_and_depth_one_ge_27
    (C : Circuit) (hM : Monotone2 C)
    (hF : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = heawoodEdgeFn x)
    (hD : AndDepthAtMostOne 14 C) :
    27 ≤ C.size := by
  sorry

end PEqualNP.Outside.HeawoodAndDepthOne
