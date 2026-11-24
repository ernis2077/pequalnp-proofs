import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2594

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

/-- Map wire indices when the first `n` inputs are remapped by `π` into `m` slots, and the
remaining wires (starting at the old index `n`) shift to start at `m`. -/
def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false) =
      g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    exact List.map_congr_left fun a _ => h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).isLt; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split <;> omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init_snoc (n : ℕ) (π : Fin n → Fin n) (x : Fin n → Bool) (b : Bool) :
    Rel n n π (List.ofFn (x ∘ π) ++ [b]) (List.ofFn x ++ [b]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro w
  by_cases hw : w < n
  · have hmw : wmap n n π w = (π ⟨w, hw⟩ : ℕ) := by simp [wmap, hw]
    have hπ : (π ⟨w, hw⟩ : ℕ) < (List.ofFn x).length := by
      simpa [List.length_ofFn] using (π ⟨w, hw⟩).isLt
    have hw' : w < (List.ofFn (x ∘ π)).length := by simpa [List.length_ofFn]
    rw [hmw, List.getD_append (List.ofFn x) [b] false _ hπ,
      List.getD_append (List.ofFn (x ∘ π)) [b] false _ hw']
    rw [List.getD_eq_getElem _ _ hπ, List.getD_eq_getElem _ _ hw', List.getElem_ofFn,
      List.getElem_ofFn]
    rfl
  · have hmw : wmap n n π w = w := by
      simp [wmap, hw]; omega
    rw [hmw]
    by_cases heq : w = n
    · -- both sides read the trailing bit at index n
      simp [heq, getD_snoc_eq, List.length_ofFn]
    · have hle : (List.ofFn x ++ [b]).length ≤ w := by simp [List.length_ofFn]; omega
      have hle' : (List.ofFn (x ∘ π) ++ [b]).length ≤ w := by simp [List.length_ofFn]; omega
      rw [List.getD_eq_default _ _ hle, List.getD_eq_default _ _ hle']

lemma fanInTwo_relabel (n : ℕ) (π : Fin n → Fin n) (C : Circuit) (hf : FanInTwo C) :
    FanInTwo (relabel n n π C) := by
  intro g hg
  simp only [relabel, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  simpa [relGate] using hf g0 hg0

lemma size_eq (n : ℕ) (π : Fin n → Fin n) (C : Circuit) :
    (relabel n n π C).size = C.size := by
  simp [relabel, Circuit.size]

lemma eval_eq (n : ℕ) (π : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) (b : Bool) :
    (relabel n n π C).eval (List.ofFn x ++ [b]) =
      C.eval (List.ofFn (x ∘ π) ++ [b]) := by
  simp only [Circuit.eval, relabel, Circuit.wires]
  exact (rel_fold n n π C.gates _ _ (rel_init_snoc n π x b)).2.2 C.output

end PEqualNP.Outside.L_meta_2594

theorem PEqualNP.Outside.L_meta_2594 :
    ∀ (x1 : ℕ) (x2 : Fin x1 → Fin x1) (x3 : PEqualNP.CircuitLowerBounds.Circuit),
      PEqualNP.MetaComplexity.FanInTwo x3 →
        ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit),
          PEqualNP.MetaComplexity.FanInTwo x5 ∧ x5.size = x3.size ∧
            ∀ (x6 : Fin x1 → Bool) (x7 : Bool),
              x5.eval (List.ofFn x6 ++ [x7]) =
                x3.eval (List.ofFn (x6 ∘ x2) ++ [x7]) := by
  intro x1 x2 x3 hf
  refine ⟨PEqualNP.Outside.L_meta_2594.relabel x1 x1 x2 x3, ?_, ?_, ?_⟩
  · exact PEqualNP.Outside.L_meta_2594.fanInTwo_relabel x1 x2 x3 hf
  · exact PEqualNP.Outside.L_meta_2594.size_eq x1 x2 x3
  · intro x6 x7
    exact PEqualNP.Outside.L_meta_2594.eval_eq x1 x2 x3 x6 x7
