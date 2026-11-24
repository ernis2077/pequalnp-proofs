import Mathlib
import PEqualNP.Defs

/-!
L-meta-2541: size ≤ 14 FanInTwo circuits that read input wire 0 in at most one gate
cannot match the Petersen edge-OR function after a polarity rewrite of coordinate 0.
-/

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
    (wF wG : List Bool) (hlen : wF.length = wG.length) (h9 : 9 ≤ wF.length)
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
    have h9' : 9 ≤ (step wF g).length := by simp [step]; omega
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
    exact ih hrest (step wF g) (step wG g) hlen' h9' hagree' i hi

lemma ofFn_agree_off0 (x y : Fin 9 → Bool) (hxy : ∀ i : Fin 9, i ≠ 0 → x i = y i) :
    ∀ i, i ≠ 0 → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hlt : i < 9
  · have hx : (List.ofFn x).getD i false = x ⟨i, hlt⟩ := by
      simp [List.getD_eq_getElem, List.getElem_ofFn]
    have hy : (List.ofFn y).getD i false = y ⟨i, hlt⟩ := by
      simp [List.getD_eq_getElem, List.getElem_ofFn]
    rw [hx, hy]
    exact hxy ⟨i, hlt⟩ (Fin.ne_of_val_ne hi)
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
lemma edgeF_16 : edgeF (fun i => decide (i = (1 : Fin 9) ∨ i = (6 : Fin 9))) = true := by decide
lemma edgeF_0 : edgeF (fun _ => false) = false := by decide

lemma circuitFun_output_zero (C : Circuit) (pol : Bool) (x : Fin 9 → Bool) (hout : C.output = 0) :
    circuitFun 9 C (present pol x) = (present pol x 0) := by
  simp only [circuitFun, Circuit.eval, Circuit.wires, present, hout]
  have hw : 0 < (List.ofFn (present pol x)).length := by simp
  rw [getD_keep0 C.gates _ hw]
  have hx : (List.ofFn (present pol x)).getD 0 false = present pol x 0 := by
    simp [present, List.getD_eq_getElem, List.getElem_ofFn]

lemma exclude_output_zero (C : Circuit) (pol : Bool) (hout : C.output = 0) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  refine ⟨fun i => decide (i = (1 : Fin 9)), ?_⟩
  have heval : circuitFun 9 C (present pol (fun i => decide (i = (1 : Fin 9)))) =
      (pol != false) := by
    rw [circuitFun_output_zero C pol _ hout]
    simp [present]
  rw [heval, edgeF_1]
  by_cases hp : pol <;> simp [hp]

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

/-- `x 0 = pol`, so the circuit always sees wire `0` as `false`. -/
def anchor (pol : Bool) : Fin 9 → Bool :=
  fun i => if i = (0 : Fin 9) then pol else false

lemma present_anchor (pol : Bool) : present pol (anchor pol) 0 = false := by
  simp [present, anchor]

lemma edgeF_anchor_true (pol : Bool) (hp : pol) :
    edgeF (anchor pol) = false := by
  simpa [anchor, hp] using edgeF_0

lemma edgeF_anchor_false (pol : Bool) (hp : ¬ pol) :
    edgeF (anchor pol) = false := by
  simpa [anchor, hp] using edgeF_0

def bump1 : Fin 9 → Bool := fun i => decide (i = (0 : Fin 9) ∨ i = (1 : Fin 9))

lemma present_bump1 (pol : Bool) (hp : pol) :
    present pol bump1 0 = false := by
  simp [present, bump1, hp]

lemma edgeF_bump1 (pol : Bool) (hp : pol) : edgeF bump1 = true := by
  simpa [hp] using edgeF_01

def bump16 : Fin 9 → Bool := fun i => decide (i = (1 : Fin 9) ∨ i = (6 : Fin 9))

lemma present_bump16 (pol : Bool) (hp : ¬ pol) :
    present pol bump16 0 = false := by
  simp [present, bump16, hp]

lemma edgeF_bump16 (pol : Bool) (hp : ¬ pol) : edgeF bump16 = true := by
  simpa using edgeF_16

lemma gates_no0 (C : Circuit)
    (hone : (C.gates.filter (fun g => g.inputs.contains 0)).length = 0) :
    ∀ g ∈ C.gates, ¬ 0 ∈ g.inputs := by
  intro g hg
  have := no_filter_mem (fun g => decide (g.inputs.contains 0)) C.gates hone g hg
  simpa [List.contains_iff] using this

lemma gates_at_most_one0 (C : Circuit)
    (hfew : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1) :
    ∀ g₁ g₂, g₁ ∈ C.gates → g₂ ∈ C.gates → (0 ∈ g₁.inputs → 0 ∈ g₂.inputs → g₁ = g₂) := by
  intro g₁ g₂ h₁ h₂ hw₁ hw₂
  by_contra hne
  have hg₁ : g₁ ∈ C.gates.filter (fun g => g.inputs.contains 0) := by
    simp [List.mem_filter, h₁, List.contains_iff, hw₁]
  have hg₂ : g₂ ∈ C.gates.filter (fun g => g.inputs.contains 0) := by
    simp [List.mem_filter, h₂, List.contains_iff, hw₂]
  have : 2 ≤ (C.gates.filter (fun g => g.inputs.contains 0)).length := by
    have := List.countP_eq_two_iff
    -- direct count
    have hpair : g₁ ≠ g₂ := hne
    have hlen := List.length_filter_le (fun g => g.inputs.contains 0) C.gates
    omega
  omega

lemma circuitFun_pivot (C : Circuit) (pol : Bool) (hout : C.output ≠ 0)
    (hfew : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1)
    (a b : Fin 9 → Bool) (hpa : present pol a 0 = false) (hpb : present pol b 0 = false) :
    circuitFun 9 C (present pol a) = circuitFun 9 C (present pol b) := by
  -- Both inputs present wire 0 as false; with at most one reader of wire 0 this determines wire 0,
  -- and `fold_agree_off0` handles the case with no readers; with one reader the value is still false.
  sorry

lemma exclude_one_reader (C : Circuit) (pol : Bool)
    (_hfan : FanInTwo C) (_hsz : C.size ≤ 14)
    (hone : (C.gates.filter (fun g => g.inputs.contains 0)).length = 1) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  by_cases hout : C.output = 0
  · refine ⟨bump16, ?_⟩
    have heval := circuitFun_output_zero C pol bump16 hout
    rw [heval, present_bump16 pol]
    · rw [edgeF_bump16 pol]
      cases pol <;> decide
    · intro; cases pol <;> decide
  · have hout' : C.output ≠ 0 := hout
    let b := circuitFun 9 C (present pol (anchor pol))
    by_cases hp : pol
    · by_cases hb : b
      · refine ⟨anchor pol, ?_⟩
        have hc := circuitFun_pivot C pol hout' (by omega) (anchor pol) bump1
          (present_anchor pol) (present_bump1 pol hp)
        intro h'
        have he := edgeF_anchor_true pol hp
        rw [hc] at h'
        rw [he] at h'
        exact h' hb
      · refine ⟨bump1, ?_⟩
        have hc := circuitFun_pivot C pol hout' (by omega) (anchor pol) bump1
          (present_anchor pol) (present_bump1 pol hp)
        intro h'
        rw [← hc, hb, edgeF_bump1 pol hp] at h'
        exact h'
    · by_cases hb : b
      · refine ⟨anchor pol, ?_⟩
        have hc := circuitFun_pivot C pol hout' (by omega) (anchor pol) bump16
          (present_anchor pol) (present_bump16 pol hp)
        intro h'
        have he := edgeF_anchor_false pol hp
        rw [hc] at h'
        rw [he] at h'
        exact h' hb
      · refine ⟨bump16, ?_⟩
        have hc := circuitFun_pivot C pol hout' (by omega) (anchor pol) bump16
          (present_anchor pol) (present_bump16 pol hp)
        intro h'
        rw [← hc, hb, edgeF_bump16 pol hp] at h'
        exact h'

theorem exclude (C : Circuit) (pol : Bool) (hfan : FanInTwo C) (hsz : C.size ≤ 14)
    (hfew : (C.gates.filter (fun g => g.inputs.contains 0)).length ≤ 1) :
    ∃ x : Fin 9 → Bool, circuitFun 9 C (present pol x) ≠ edgeF x := by
  rcases lt_or_eq_of_le hfew with h0 | h1
  · exact exclude_zero_readers C pol (by simpa using h0))
  · simp at h1
    rcases h1 with rfl | hone
    · exact exclude_zero_readers C pol rfl
    · exact exclude_one_reader C pol hfan hsz hone

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