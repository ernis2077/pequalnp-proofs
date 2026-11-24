import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2541

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edgeF : (Fin 9 → Bool) → Bool := fun x =>
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def present (pol : Bool) (x : Fin 9 → Bool) : Fin 9 → Bool :=
  fun i => if i = 0 then pol != x 0 else x i

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_snoc_lt {α : Type} (L : List α) (S d : α) (i : ℕ) (hi : i < L.length) :
    (L ++ [S]).getD i d = L.getD i d := by
  simp [List.getD_append _ _ _ _ hi]

lemma getD_keep0 (gs : List Gate) (w : List Bool) (h0 : 0 < w.length) :
    (gs.foldl step w).getD 0 false = w.getD 0 false := by
  induction gs with
  | nil => rfl
  | cons g rest ih =>
    simp only [List.foldl_cons, step]
    have hlen : 0 < (w ++ [g.op.eval _]).length := by simp [h0]
    rw [ih (w ++ _) hlen]
    exact getD_snoc_lt w _ false 0 h0

lemma no_filter_mem {α : Type} (p : α → Bool) (l : List α)
    (h : (l.filter p).length = 0) : ∀ x ∈ l, p x = false := by
  rw [List.filter_eq_nil_iff] at h
  intro x hx
  simpa [Bool.not_eq_true] using h x hx

lemma fold_agree_off0 (gs : List Gate) (hn : ∀ g ∈ gs, ¬ 0 ∈ g.inputs)
    (wF wG : List Bool) (hlen : wF.length = wG.length) (_h9 : 9 ≤ wF.length)
    (hagree : ∀ i, i ≠ 0 → wF.getD i false = wG.getD i false) :
    ∀ i, i ≠ 0 → (gs.foldl step wF).getD i false = (gs.foldl step wG).getD i false := by
  induction gs generalizing wF wG with
  | nil => exact hagree
  | cons g rest ih =>
    intro i hi
    have hg : ¬ 0 ∈ g.inputs := hn g (List.mem_cons_self g rest)
    have hv : g.op.eval (g.inputs.map fun t => wF.getD t false) =
        g.op.eval (g.inputs.map fun t => wG.getD t false) := by
      congr 1
      refine List.map_congr_left ?_
      intro t ht
      exact hagree t (fun h => hg (h ▸ ht))
    have hlen' : (step wF g).length = (step wG g).length := by simp [step, hlen]
    have hagree' : ∀ j, j ≠ 0 → (step wF g).getD j false = (step wG g).getD j false := by
      intro j hj
      simp only [step, hv]
      rcases Nat.lt_trichotomy j wF.length with hlt | heq | hgt
      · rw [getD_snoc_lt _ _ _ _ hlt, getD_snoc_lt _ _ _ _ (by omega)]
        exact hagree j hj
      · rw [heq, ← hlen, getD_snoc_eq, getD_snoc_eq]
      · have : wF.length + 1 ≤ j := by omega
        have : wG.length + 1 ≤ j := by omega
        simp [List.getD_eq_default, step, hlen, *]
    have hrest : ∀ g ∈ rest, ¬ 0 ∈ g.inputs := fun g0 hg0 =>
      hn g0 (List.mem_cons_of_mem g hg0)
    exact ih hrest (step wF g) (step wG g) hlen' (by simp [step]; omega) hagree' i hi

lemma ofFn_agree_off0 (x y : Fin 9 → Bool) (hxy : ∀ i : Fin 9, i ≠ 0 → x i = y i) :
    ∀ i, i ≠ 0 → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hlt : i < 9
  · simp [List.getD_eq_getElem, List.getElem_ofFn, hxy ⟨i, hlt⟩ (Fin.ne_of_val_ne hi)]
  · simp [List.getD_eq_default, List.length_ofFn]; omega

lemma circuitFun_ignore0 (C : Circuit)
    (hnone : (C.gates.filter (fun g => g.inputs.contains 0)).length = 0)
    (x y : Fin 9 → Bool) (hxy : ∀ i : Fin 9, i ≠ 0 → x i = y i)
    (hout : C.output ≠ 0) :
    circuitFun 9 C x = circuitFun 9 C y := by
  have hn : ∀ g ∈ C.gates, ¬ 0 ∈ g.inputs := by
    intro g hg
    have := no_filter_mem (fun g => decide (g.inputs.contains 0)) C.gates hnone g hg
    simpa [List.contains_iff] using this
  simp only [circuitFun, Circuit.eval, Circuit.wires]
  exact fold_agree_off0 C.gates hn (List.ofFn x) (List.ofFn y) (by simp) (by simp)
    (ofFn_agree_off0 x y hxy) C.output hout

lemma edgeF_01 : edgeF (fun i => decide (i = (0 : Fin 9) ∨ i = (1 : Fin 9))) = true := by decide
lemma edgeF_1 : edgeF (fun i => decide (i = (1 : Fin 9))) = false := by decide

lemma circuitFun_output_zero (C : Circuit) (pol : Bool) (x : Fin 9 → Bool) (hout : C.output = 0) :
    circuitFun 9 C (present pol x) = (present pol x 0) := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, present, hout]
  have hw : 0 < (List.ofFn (present pol x)).length := by simp
  rw [getD_keep0 C.gates _ hw]
  simp [present, List.getD_eq_getElem, List.getElem_ofFn]

lemma exclude_output_zero (C : Circuit) (pol : Bool) (hout : C.output = 0) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  refine ⟨fun i => decide (i = (1 : Fin 9)), ?_⟩
  rw [circuitFun_output_zero C pol _ hout, edgeF_1]
  cases pol <;> decide

lemma exclude_zero_readers (C : Circuit) (pol : Bool)
    (hnone : (C.gates.filter (fun g => g.inputs.contains 0)).length = 0) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  by_cases hout : C.output = 0
  · exact exclude_output_zero C pol hout
  · have hout' : C.output ≠ 0 := hout
    let x : Fin 9 → Bool := fun i => decide (i = 0 ∨ i = 1)
    let x' : Fin 9 → Bool := fun i => decide (i = 1)
    have hp : ∀ i : Fin 9, i ≠ 0 → present pol x i = present pol x' i := by
      intro i hi
      simp only [present, x, x']
      fin_cases i <;> simp_all
    have hc' : circuitFun 9 C (present pol x) = circuitFun 9 C (present pol x') :=
      circuitFun_ignore0 C hnone _ _ hp hout'
    by_cases h : circuitFun 9 C (present pol x) = edgeF x
    · refine ⟨x', ?_⟩
      intro h'
      have : circuitFun 9 C (present pol x') = true := by
        rw [← hc', h, edgeF_01]
      exact h' this
    · exact ⟨x, h⟩

lemma exclude_one_reader (C : Circuit) (pol : Bool)
    (_hfan : FanInTwo C) (_hsz : C.size ≤ 14)
    (_hone : (C.gates.filter (fun g => g.inputs.contains 0)).length = 1) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  sorry

theorem exclude (C : Circuit) (pol : Bool) (hfan : FanInTwo C) (hsz : C.size ≤ 14)
    (hfew : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  by_cases h0 : (C.gates.filter (fun g => g.inputs.contains 0)).length = 0
  · exact exclude_zero_readers C pol h0
  · have h1 : (C.gates.filter (fun g => g.inputs.contains 0)).length = 1 := by omega
    exact exclude_one_reader C pol hfan hsz h1

end PEqualNP.Outside.L_meta_2541

theorem PEqualNP.Outside.L_meta_2541 :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Bool),
      PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (14 : ℕ) →
        (List.filter (fun (x5 : PEqualNP.CircuitLowerBounds.Gate) =>
          x5.inputs.contains (0 : ℕ)) x1.gates).length ≤ (1 : ℕ) →
          ∃ (x6 : Fin (9 : ℕ) → Bool),
            PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 (PEqualNP.Outside.L_meta_2541.present x2 x6) ≠
              PEqualNP.Outside.L_meta_2541.edgeF x6 := by
  intro C pol hfan hsz hfew
  obtain ⟨x, hx⟩ := PEqualNP.Outside.L_meta_2541.exclude C pol hfan hsz hfew
  exact ⟨x, hx⟩
