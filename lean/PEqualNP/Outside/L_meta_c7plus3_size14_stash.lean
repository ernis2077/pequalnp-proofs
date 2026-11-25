import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/- C7+3 edge function size 14 (Cadical: ≤13 UNSAT ⇒ L-meta-1548 false). -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_c7plus3_size14_stash :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      Monotone2 C ∧ C.size ≤ 14 ∧
      ∀ x : Fin 10 → Bool,
        C.eval (List.ofFn x) =
          (fun x : Fin 10 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 5) || (x 5 && x 6) || (x 6 && x 0) || (x 0 && x 7) || (x 1 && x 8) || (x 4 && x 9)) x := by
  let c : Circuit := ⟨[
    ⟨.or, [1, 6]⟩,
    ⟨.or, [7, 10]⟩,
    ⟨.or, [2, 8]⟩,
    ⟨.or, [2, 4]⟩,
    ⟨.or, [5, 9]⟩,
    ⟨.and, [0, 11]⟩,
    ⟨.and, [1, 12]⟩,
    ⟨.and, [3, 13]⟩,
    ⟨.and, [4, 14]⟩,
    ⟨.and, [5, 6]⟩,
    ⟨.or, [15, 16]⟩,
    ⟨.or, [17, 18]⟩,
    ⟨.or, [20, 21]⟩,
    ⟨.or, [19, 22]⟩], 23⟩
  refine ⟨c, ?_, by decide, ?_⟩
  · simp [Monotone2, c]
  · decide +kernel
