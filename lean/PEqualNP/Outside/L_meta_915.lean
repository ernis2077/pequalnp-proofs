import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_915

open PEqualNP.CircuitLowerBounds

def baseLine : Finset (Fin 13) := {0, 1, 3, 9}

def line (w : Fin 13) : Finset (Fin 13) :=
  baseLine.image (fun u => u + w)

def weight (x : Fin 13 → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin 13 => x i = true)).card

def target (w : Fin 13) (x : Fin 13 → Bool) : Bool :=
  decide (∃ v ∈ line w, x v = true)

lemma card_baseLine : baseLine.card = 4 := by decide

lemma card_line (w : Fin 13) : (line w).card = 4 := by
  revert w
  decide

lemma line_eq_image (w : Fin 13) :
    line w = (({0, 1, 3, 9} : Finset (Fin 13)).image (fun u => u + w)) :=
  rfl

def adjGates : List Gate :=
  List.ofFn fun i : Fin 13 =>
    ⟨GateOp.or, [i.val, ((i + 1 : Fin 13) : ℕ)]⟩

def diff6Gates : List Gate :=
  List.ofFn fun i : Fin 13 =>
    ⟨GateOp.or, [i.val, ((i + 6 : Fin 13) : ℕ)]⟩

def combineGates : List Gate :=
  List.ofFn fun i : Fin 13 =>
    ⟨GateOp.or, [13 + i.val, 26 + ((i + 3 : Fin 13) : ℕ)]⟩

def gates39 : List Gate := adjGates ++ diff6Gates ++ combineGates

def out39 (w : Fin 13) : ℕ := 39 + w.val

lemma length_adjGates : adjGates.length = 13 := by simp [adjGates]

lemma length_diff6Gates : diff6Gates.length = 13 := by simp [diff6Gates]

lemma length_combineGates : combineGates.length = 13 := by simp [combineGates]

lemma length_gates39 : gates39.length = 39 := by
  simp [gates39, length_adjGates, length_diff6Gates, length_combineGates]

lemma gates39_ok :
    ∀ g ∈ gates39,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [gates39, List.mem_append] at hg
  rcases hg with (h | h) | h
  · simp only [adjGates, List.mem_ofFn] at h
    rcases h with ⟨i, rfl⟩
    exact ⟨Or.inr rfl, by simp⟩
  · simp only [diff6Gates, List.mem_ofFn] at h
    rcases h with ⟨i, rfl⟩
    exact ⟨Or.inr rfl, by simp⟩
  · simp only [combineGates, List.mem_ofFn] at h
    rcases h with ⟨i, rfl⟩
    exact ⟨Or.inr rfl, by simp⟩

lemma weight_mono {x y : Fin 13 → Bool}
    (h : ∀ i, x i = true → y i = true) :
    weight x ≤ weight y := by
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact h i hi

lemma target_mono (w : Fin 13) {x y : Fin 13 → Bool}
    (h : ∀ i, x i = true → y i = true)
    (hx : target w x = true) : target w y = true := by
  simp only [target, decide_eq_true_eq] at hx ⊢
  rcases hx with ⟨v, hv, hxv⟩
  exact ⟨v, hv, h v hxv⟩

/-
  Construction status for the posted existence claim (length at most 38):

  Pure OR is impossible at length 38 on the weight-at-least-8 promise: each output
  support must equal the corresponding Singer line, and distinct lines meet in at most
  one point, so no OR gate of support size at least two can be shared. Thus any pure-OR
  circuit needs at least 13 * 3 = 39 gates. The witness `gates39` meets that bound.

  Reaching 38 therefore requires AND gates together with promise-only identities.
  Exhaustive and heuristic searches (CEGIS with CP-SAT, annealing from the 39-gate
  forest, shared AND-trick formulas OR(trip) OR AND(d, partner), pair forests of size
  38, and a full-mask SAT check that two lines need at least six gates) did not yield an
  explicit length-38 AND/OR list. The forced 13-adj plus 13-diff6 prefix with only twelve
  free gates is CP-SAT-infeasible even on the 130 negative inputs alone.

  Missing for the posted theorem: an explicit gates list of length at most 38 and
  out : Fin 13 to nat such that Circuit.eval matches target on every weight-8 and
  weight-9 input; monotonicity then lifts to weight at least 10.
-/

end PEqualNP.Outside.L_meta_915
