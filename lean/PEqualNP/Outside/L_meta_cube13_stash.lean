import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- Local stash: 3-cube edge ≤13 (companion to merged L-meta-970 lower bound ≥12). -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_cube13_stash :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 13 ∧
      ∀ x : Fin 8 → Bool,
        C.eval (List.ofFn x) =
          (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 4) || (x 1 && x 3) || (x 1 && x 5) || (x 2 && x 3) || (x 2 && x 6) || (x 3 && x 7) || (x 4 && x 5) || (x 4 && x 6) || (x 5 && x 7) || (x 6 && x 7)) x := by
  let c : Circuit := ⟨[
    ⟨.or, [0, 5]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.or, [3, 8]⟩,
    ⟨.or, [6, 8]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [4, 11]⟩,
    ⟨.or, [0, 9]⟩,
    ⟨.and, [2, 14]⟩,
    ⟨.and, [1, 10]⟩,
    ⟨.or, [13, 15]⟩,
    ⟨.and, [7, 12]⟩,
    ⟨.or, [16, 17]⟩,
    ⟨.or, [18, 19]⟩], 20⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [Monotone2, c]
  · decide +kernel
