import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Local stash (no PR): two-lit H on 6 points, mask 270582943, FanInTwo size ≤ 5.
   Witness from CP-SAT; lake-build before submit when account unbanned. -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_24190 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      FanInTwo C ∧ C.size ≤ 5 ∧
      ∀ i j : Fin 6,
        C.eval (List.ofFn fun k : Fin 6 => decide (k = i ∨ k = j)) =
          (270582943 : ℕ).testBit (6 * min i.val j.val + max i.val j.val) := by
  let c : Circuit := ⟨[
    ⟨.or, [2, 3]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [6, 7]⟩,
    ⟨.or, [5, 8]⟩,
    ⟨.not, [9]⟩], 10⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [FanInTwo, c]
  · decide +kernel
