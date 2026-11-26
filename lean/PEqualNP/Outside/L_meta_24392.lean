import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Local stash (no PR): two-lit H on 6 points, mask 34634582183, FanInTwo size ≤ 7.
   CP-SAT witness; lake-build green before any future submit. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_24392 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      FanInTwo C ∧ C.size ≤ 7 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (34634582183 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let c : Circuit := ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [1, 5]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [2, 7]⟩,
    ⟨.or, [6, 9]⟩,
    ⟨.and, [8, 10]⟩,
    ⟨.not, [11]⟩], 12⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [FanInTwo, c]
  · decide +kernel
