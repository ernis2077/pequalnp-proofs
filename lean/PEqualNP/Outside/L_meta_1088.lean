import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1088
open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

variable {n : ℕ}

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, g.inputs.length ≤ 2) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hfan h
    have := ih (t + 1) (L ++ [gateSupp L g])
      (fun g' hg' => hfan g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hfan g List.mem_cons_self) h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem ofFn_getD (x : List Bool) (hx : x.length = n) :
    List.ofFn (fun j : Fin n => x.getD j.val false) = x := by
  apply List.ext_getElem
  · simp [hx]
  · intro k hk hk'
    have hk2 : k < x.length := by omega
    simp [List.getElem_ofFn, hk2]

theorem ofFn_update_set (x : List Bool) (hx : x.length = n) (i : Fin n) :
    List.ofFn (Function.update (fun j : Fin n => x.getD j.val false) i (!(x.getD i.val false)))
      = x.set i.val (!(x.getD i.val false)) := by
  set b : Bool := !(x.getD i.val false)
  set f := Function.update (fun j : Fin n => x.getD j.val false) i b
  have hlenL : (List.ofFn f).length = n := by simp [f]
  have hlenR : (x.set i.val b).length = n := by simp [List.length_set, hx]
  apply List.ext_getElem
  · rw [hlenL, hlenR]
  · intro k hk hk'
    have hk2 : k < x.length := by omega
    have hk3 : k < n := by omega
    simp only [List.getElem_ofFn]
    by_cases hki : k = i.val
    · subst hki
      have hupd : f ⟨i.val, hk3⟩ = b := by simp [f]
      have hset : (x.set i.val b)[i.val]'(by omega) = b := List.getElem_set_self (by omega)
      rw [hupd, hset]
    · have hupd : f ⟨k, hk3⟩ = x.getD k false := by
        simp [f, Fin.ext_iff, hki]
      have hset : (x.set i.val b)[k]'(by omega) = x[k] :=
        List.getElem_set_ne (Ne.symm hki) (by omega)
      rw [hupd, List.getD_eq_getElem _ _ hk2, hset]

theorem size_of_essential (n : ℕ) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i < n, ∃ x : List Bool, x.length = n ∧
      C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) :
    n ≤ C.size + 1 := by
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hxlen, hx⟩ := hdep i.val i.isLt
    set y : Fin n → Bool := fun j => x.getD j.val false
    set y' : Fin n → Bool := Function.update y i (!y i)
    have hag := (agree_wiresFrom y' y C.gates _ _ _ (agree_inputs _ _)).2.2 C.output (by
      intro k hk
      have : k ≠ i := fun e => hi (e ▸ hk)
      simp [y', Function.update_of_ne this])
    have hy : List.ofFn y = x := ofFn_getD x hxlen
    have hy' : List.ofFn y' = x.set i.val (!(x.getD i.val false)) := by
      simpa [y, y'] using ofFn_update_set x hxlen i
    have heq : C.eval (List.ofFn y') = C.eval (List.ofFn y) := by
      simpa [Circuit.eval, wires_eq] using hag
    rw [hy, hy'] at heq
    exact hx heq.symm
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) hfan cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  simpa [Circuit.size] using hc

end PEqualNP.Outside.L_meta_1088

theorem PEqualNP.Outside.L_meta_1088 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ g ∈ C.gates, g.inputs.length ≤ 2) →
      (∀ i < n, ∃ x : List Bool, x.length = n ∧
        C.eval x ≠ C.eval (x.set i (!(x.getD i false)))) →
      n ≤ C.size + 1 :=
  PEqualNP.Outside.L_meta_1088.size_of_essential
