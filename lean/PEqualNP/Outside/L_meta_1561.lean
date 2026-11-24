import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1561

def T : Finset (Fin 21) := {0, 1, 2}

def line (t : Fin 21) : Finset (Fin 21) := {t, t + 1, t + 4, t + 14, t + 16}

def base (c : Fin 21 → Bool) (s p : Fin 21) : Finset (Fin 21) :=
  if p ∈ T then (∅ : Finset (Fin 21))
  else if (line s ∩ T).card = 2 then T \ line s
  else if (line s ∩ T).card = 1 then
    (if c s then (line s ∩ T).image (fun v : Fin 21 => if v = 2 then 0 else v + 1)
     else (line s ∩ T).image (fun v : Fin 21 => if v = 0 then 2 else v - 1))
  else {0}

def hits (c : Fin 21 → Bool) (s s' : Fin 21) : Bool :=
  decide (∃ p ∈ line s \ line s', (base c s p ∩ line s').Nonempty)

def mutualB (c : Fin 21 → Bool) (s s' : Fin 21) : Bool :=
  hits c s s' && hits c s' s

def conflictPairs (c : Fin 21 → Bool) : Finset (Fin 21 × Fin 21) :=
  (Finset.univ : Finset (Fin 21 × Fin 21)).filter
    (fun e => e.1 < e.2 ∧ mutualB c e.1 e.2 = true)

def charB (s s' : Fin 21) : Bool :=
  let ks := (line s ∩ T).card
  let ks' := (line s' ∩ T).card
  (ks == 2 && ks' == 2) ||
  (ks == 2 && ks' == 1 && (line s' ∩ T ∩ line s).card == 0) ||
  (ks' == 2 && ks == 1 && (line s ∩ T ∩ line s').card == 0)

lemma charB_iff (s s' : Fin 21) :
    charB s s' = true ↔
      (((line s ∩ T).card = 2 ∧ (line s' ∩ T).card = 2) ∨
       ((line s ∩ T).card = 2 ∧ (line s' ∩ T).card = 1 ∧ line s' ∩ T ∩ line s = ∅) ∨
       ((line s' ∩ T).card = 2 ∧ (line s ∩ T).card = 1 ∧ line s ∩ T ∩ line s' = ∅)) := by
  simp [charB, Bool.and_eq_true, Bool.or_eq_true, Finset.card_eq_zero, and_assoc]
  tauto

def card1Vals : Fin 9 → Fin 21 := ![2, 5, 6, 8, 9, 17, 18, 19, 20]

def lift (f : Fin 9 → Bool) : Fin 21 → Bool := fun s =>
  if s = 2 then f 0
  else if s = 5 then f 1
  else if s = 6 then f 2
  else if s = 8 then f 3
  else if s = 9 then f 4
  else if s = 17 then f 5
  else if s = 18 then f 6
  else if s = 19 then f 7
  else if s = 20 then f 8
  else false

def extract (c : Fin 21 → Bool) : Fin 9 → Bool := fun i => c (card1Vals i)

def fixedPairs : Finset (Fin 21 × Fin 21) :=
  ([(0, 1), (0, 2), (0, 7), (0, 9), (0, 19), (1, 5), (1, 7), (1, 17), (1, 20),
    (6, 7), (7, 8), (7, 18)] : List (Fin 21 × Fin 21)).toFinset

def G0 : Finset (Fin 9) := {1, 5, 8}
def G1 : Finset (Fin 9) := {2, 3, 6}
def G2 : Finset (Fin 9) := {0, 4, 7}

def nTrue (f : Fin 9 → Bool) (S : Finset (Fin 9)) : ℕ :=
  (S.filter (fun i => f i = true)).card

def extraNum (f : Fin 9 → Bool) : ℕ :=
  nTrue f G0 * (3 - nTrue f G1) + nTrue f G1 * (3 - nTrue f G2) +
    nTrue f G2 * (3 - nTrue f G0)

def extraIndexPairs (f : Fin 9 → Bool) : Finset (Fin 9 × Fin 9) :=
  (Finset.univ : Finset (Fin 9 × Fin 9)).filter
    (fun ij => ij.1 < ij.2 ∧ mutualB (lift f) (card1Vals ij.1) (card1Vals ij.2) = true)

def extraPairs (f : Fin 9 → Bool) : Finset (Fin 21 × Fin 21) :=
  (extraIndexPairs f).image (fun ij => (card1Vals ij.1, card1Vals ij.2))

lemma card1_eq : ∀ s : Fin 21, (line s ∩ T).card = 1 ↔
    s = 2 ∨ s = 5 ∨ s = 6 ∨ s = 8 ∨ s = 9 ∨ s = 17 ∨ s = 18 ∨ s = 19 ∨ s = 20 := by
  decide

lemma card1Vals_is_card1 : ∀ i : Fin 9, (line (card1Vals i) ∩ T).card = 1 := by
  decide

lemma card_le_two : ∀ s : Fin 21, (line s ∩ T).card ≤ 2 := by
  decide

lemma card1Vals_strictMono : StrictMono card1Vals := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [card1Vals] at hij ⊢ <;> omega

lemma card1Vals_inj : Function.Injective card1Vals := card1Vals_strictMono.injective

lemma exists_card1_index (s : Fin 21) (hs : (line s ∩ T).card = 1) :
    ∃ i : Fin 9, card1Vals i = s := by
  have hs' := (card1_eq s).1 hs
  rcases hs' with h | h | h | h | h | h | h | h | h
  · exact ⟨0, by simp [card1Vals, h]⟩
  · exact ⟨1, by simp [card1Vals, h]⟩
  · exact ⟨2, by simp [card1Vals, h]⟩
  · exact ⟨3, by simp [card1Vals, h]⟩
  · exact ⟨4, by simp [card1Vals, h]⟩
  · exact ⟨5, by simp [card1Vals, h]⟩
  · exact ⟨6, by simp [card1Vals, h]⟩
  · exact ⟨7, by simp [card1Vals, h]⟩
  · exact ⟨8, by simp [card1Vals, h]⟩

lemma extract_agrees (c : Fin 21 → Bool) (s : Fin 21) (hs : (line s ∩ T).card = 1) :
    lift (extract c) s = c s := by
  have hs' := (card1_eq s).1 hs
  rcases hs' with h | h | h | h | h | h | h | h | h <;>
    simp [lift, extract, card1Vals, h]

lemma base_depends (c c' : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = c' s) (s p : Fin 21) :
    base c s p = base c' s p := by
  unfold base
  by_cases hT : p ∈ T
  · simp [hT]
  · simp only [hT, ↓reduceIte]
    by_cases h2 : (line s ∩ T).card = 2
    · simp [h2]
    · simp only [h2, ↓reduceIte]
      by_cases h1 : (line s ∩ T).card = 1
      · have hc : c s = c' s := h s h1
        simp [h1, hc]
      · simp [h1]

lemma hits_depends (c c' : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = c' s) (s s' : Fin 21) :
    hits c s s' = hits c' s s' := by
  simp only [hits, base_depends c c' h]

lemma mutualB_depends (c c' : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = c' s) (s s' : Fin 21) :
    mutualB c s s' = mutualB c' s s' := by
  simp only [mutualB, hits_depends c c' h]

lemma conflictPairs_depends (c c' : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = c' s) :
    conflictPairs c = conflictPairs c' := by
  ext e
  simp only [conflictPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    mutualB_depends c c' h]

lemma conflictPairs_eq_lift (c : Fin 21 → Bool) :
    conflictPairs c = conflictPairs (lift (extract c)) :=
  conflictPairs_depends _ _ (fun s hs => (extract_agrees c s hs).symm)

lemma hits_iff (c : Fin 21 → Bool) (s s' : Fin 21) :
    hits c s s' = true ↔ ∃ p ∈ line s \ line s', (base c s p ∩ line s').Nonempty := by
  simp [hits]

lemma mutual_iff (c : Fin 21 → Bool) (s s' : Fin 21) :
    mutualB c s s' = true ↔
      ((∃ p ∈ line s \ line s', (base c s p ∩ line s').Nonempty) ∧
        (∃ p ∈ line s' \ line s, (base c s' p ∩ line s).Nonempty)) := by
  simp [mutualB, hits_iff, Bool.and_eq_true]

lemma base_subset_T (c : Fin 21 → Bool) (s p : Fin 21) : base c s p ⊆ T := by
  unfold base
  split_ifs with hT h2 h1 hc
  · simp
  · intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    have hvT : v ∈ T := (Finset.mem_inter.mp hv).2
    split_ifs
    · exact Finset.mem_insert_self _ _
    · have : v = (0 : Fin 21) ∨ v = 1 ∨ v = 2 := by
        simpa [T, Finset.mem_insert, Finset.mem_singleton] using hvT
      rcases this with hv' | hv' | hv'
      · simp [hv', T]
      · simp [hv', T]
      · simp [hv', T]
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨v, hv, rfl⟩
    have hvT : v ∈ T := (Finset.mem_inter.mp hv).2
    split_ifs
    · exact Finset.mem_insert_self _ _
    · have : v = (0 : Fin 21) ∨ v = 1 ∨ v = 2 := by
        simpa [T, Finset.mem_insert, Finset.mem_singleton] using hvT
      rcases this with hv' | hv' | hv'
      · simp [hv', T]
      · simp [hv', T]
      · simp [hv', T]
  · simp [T]

lemma mutual_of_empty_inter (c : Fin 21 → Bool) (s s' : Fin 21)
    (hs : line s ∩ T = ∅) : mutualB c s s' = false := by
  simp only [mutualB, Bool.and_eq_false_eq_eq_false_or_eq_false]
  refine Or.inr ?_
  simp only [hits, decide_eq_false_iff_not]
  intro ⟨p, _, hpne⟩
  obtain ⟨q, hq⟩ := hpne
  have hqB : q ∈ base c s' p := (Finset.mem_inter.mp hq).1
  have hqL : q ∈ line s := (Finset.mem_inter.mp hq).2
  have hqT : q ∈ T := base_subset_T c s' p hqB
  have : q ∈ line s ∩ T := Finset.mem_inter.mpr ⟨hqL, hqT⟩
  simp [hs] at this

lemma hits_of_card2 (c c' : Fin 21 → Bool) (s s' : Fin 21)
    (hs : (line s ∩ T).card = 2) : hits c s s' = hits c' s s' := by
  simp [hits, base, hs]

lemma hits_of_card1 (c c' : Fin 21 → Bool) (s s' : Fin 21)
    (hs : (line s ∩ T).card = 1) (he : c s = c' s) :
    hits c s s' = hits c' s s' := by
  simp [hits, base, hs, he]

lemma mutual_card2_card2 (c : Fin 21 → Bool) (s s' : Fin 21)
    (hs : (line s ∩ T).card = 2) (hs' : (line s' ∩ T).card = 2) :
    mutualB c s s' = mutualB (fun _ => true) s s' := by
  simp only [mutualB]
  rw [hits_of_card2 c (fun _ => true) s s' hs]
  rw [hits_of_card2 c (fun _ => true) s' s hs']

lemma mutual_card2_card1 (c : Fin 21 → Bool) (s s' : Fin 21)
    (hs : (line s ∩ T).card = 2) (hs' : (line s' ∩ T).card = 1) :
    mutualB c s s' = mutualB (fun _ => c s') s s' := by
  simp only [mutualB]
  rw [hits_of_card2 c (fun _ => c s') s s' hs]
  rw [hits_of_card1 c (fun _ => c s') s' s hs' rfl]

lemma mutual_card1_card2 (c : Fin 21 → Bool) (s s' : Fin 21)
    (hs : (line s ∩ T).card = 1) (hs' : (line s' ∩ T).card = 2) :
    mutualB c s s' = mutualB (fun _ => c s) s s' := by
  simp only [mutualB]
  rw [hits_of_card1 c (fun _ => c s) s s' hs rfl]
  rw [hits_of_card2 c (fun _ => c s) s' s hs']

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma char_iff_true : ∀ s s' : Fin 21, s ≠ s' →
    mutualB (fun _ => true) s s' = charB s s' := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma conflict_card_true : (conflictPairs (fun _ => true)).card = 12 := by
  decide

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma fixedPairs_card : fixedPairs.card = 12 := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma fixed_eq_char : ∀ s s' : Fin 21, s < s' →
    ((s, s') ∈ fixedPairs ↔ charB s s' = true) := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma both_orients_card2_card1 : ∀ s s' : Fin 21,
    (line s ∩ T).card = 2 → (line s' ∩ T).card = 1 →
      mutualB (fun _ => true) s s' = charB s s' ∧
      mutualB (fun _ => false) s s' = charB s s' := by
  decide

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma both_orients_card1_card2 : ∀ s s' : Fin 21,
    (line s ∩ T).card = 1 → (line s' ∩ T).card = 2 →
      mutualB (fun _ => true) s s' = charB s s' ∧
      mutualB (fun _ => false) s s' = charB s s' := by
  decide

lemma char_implies_mutual (c : Fin 21 → Bool) (s s' : Fin 21) (hne : s ≠ s')
    (hchar : charB s s' = true) : mutualB c s s' = true := by
  have hcases := (charB_iff s s').1 hchar
  rcases hcases with h | h | h
  · rw [mutual_card2_card2 c s s' h.1 h.2, char_iff_true s s' hne, hchar]
  · rw [mutual_card2_card1 c s s' h.1 h.2.1]
    cases hc : c s'
    · have hbo := (both_orients_card2_card1 s s' h.1 h.2.1).2
      simp [hc, hbo, hchar]
    · have hbo := (both_orients_card2_card1 s s' h.1 h.2.1).1
      simp [hc, hbo, hchar]
  · rw [mutual_card1_card2 c s s' h.2.1 h.1]
    cases hc : c s
    · have hbo := (both_orients_card1_card2 s s' h.2.1 h.1).2
      simp [hc, hbo, hchar]
    · have hbo := (both_orients_card1_card2 s s' h.2.1 h.1).1
      simp [hc, hbo, hchar]

lemma mutual_implies_char_of_card2 (c : Fin 21 → Bool) (s s' : Fin 21) (hne : s ≠ s')
    (h2 : (line s ∩ T).card = 2 ∨ (line s' ∩ T).card = 2)
    (hm : mutualB c s s' = true) : charB s s' = true := by
  rcases h2 with hs | hs'
  · have hs'le := card_le_two s'
    interval_cases hsc : (line s' ∩ T).card
    · have hempty : line s' ∩ T = ∅ := Finset.card_eq_zero.mp hsc
      have := mutual_of_empty_inter c s' s hempty
      have hsym : mutualB c s' s = mutualB c s s' := by
        simp [mutualB, Bool.and_comm]
      simp [hsym, hm] at this
    · have hs1 : (line s' ∩ T).card = 1 := hsc
      rw [mutual_card2_card1 c s s' hs hs1] at hm
      cases hc : c s'
      · have hbo := (both_orients_card2_card1 s s' hs hs1).2
        simpa [hc, hbo] using hm
      · have hbo := (both_orients_card2_card1 s s' hs hs1).1
        simpa [hc, hbo] using hm
    · have hs2 : (line s' ∩ T).card = 2 := hsc
      rw [mutual_card2_card2 c s s' hs hs2, char_iff_true s s' hne] at hm
      exact hm
  · have hsle := card_le_two s
    interval_cases hsc : (line s ∩ T).card
    · have hempty : line s ∩ T = ∅ := Finset.card_eq_zero.mp hsc
      have := mutual_of_empty_inter c s s' hempty
      simp [hm] at this
    · have hs1 : (line s ∩ T).card = 1 := hsc
      rw [mutual_card1_card2 c s s' hs1 hs'] at hm
      cases hc : c s
      · have hbo := (both_orients_card1_card2 s s' hs1 hs').2
        simpa [hc, hbo] using hm
      · have hbo := (both_orients_card1_card2 s s' hs1 hs').1
        simpa [hc, hbo] using hm
    · have hs2 : (line s ∩ T).card = 2 := hsc
      rw [mutual_card2_card2 c s s' hs2 hs', char_iff_true s s' hne] at hm
      exact hm

lemma mutual_classification (c : Fin 21 → Bool) (s s' : Fin 21) (hlt : s < s')
    (hm : mutualB c s s' = true) :
    (s, s') ∈ fixedPairs ∨ ((line s ∩ T).card = 1 ∧ (line s' ∩ T).card = 1) := by
  have hne : s ≠ s' := ne_of_lt hlt
  have hsle := card_le_two s
  have hs'le := card_le_two s'
  interval_cases hsc : (line s ∩ T).card
  · have := mutual_of_empty_inter c s s' (Finset.card_eq_zero.mp hsc)
    simp [hm] at this
  · interval_cases hsc' : (line s' ∩ T).card
    · have := mutual_of_empty_inter c s' s (Finset.card_eq_zero.mp hsc')
      have hsym : mutualB c s' s = mutualB c s s' := by simp [mutualB, Bool.and_comm]
      simp [hsym, hm] at this
    · exact Or.inr ⟨by omega, by omega⟩
    · left
      exact (fixed_eq_char s s' hlt).2
        (mutual_implies_char_of_card2 c s s' hne (Or.inr (by omega)) hm)
  · left
    exact (fixed_eq_char s s' hlt).2
      (mutual_implies_char_of_card2 c s s' hne (Or.inl (by omega)) hm)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma fixed_mem_lt : ∀ e ∈ fixedPairs, e.1 < e.2 := by
  decide

lemma fixed_subset_conflicts (c : Fin 21 → Bool) : fixedPairs ⊆ conflictPairs c := by
  intro e he
  have hlt : e.1 < e.2 := fixed_mem_lt e he
  have hchar : charB e.1 e.2 = true := (fixed_eq_char e.1 e.2 hlt).1 he
  have hne : e.1 ≠ e.2 := ne_of_lt hlt
  have hm : mutualB c e.1 e.2 = true := char_implies_mutual c e.1 e.2 hne hchar
  simp [conflictPairs, hlt, hm]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 10000 in
lemma extra_card_eq_num : ∀ f : Fin 9 → Bool, (extraIndexPairs f).card = extraNum f := by
  decide

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 5000 in
lemma extraNum_min : ∀ f : Fin 9 → Bool,
    extraNum f = 0 ↔ (∀ i : Fin 9, f i = true) ∨ (∀ i : Fin 9, f i = false) := by
  decide

lemma extraPairs_card (f : Fin 9 → Bool) : (extraPairs f).card = extraNum f := by
  rw [extraPairs, Finset.card_image_of_injective]
  · exact extra_card_eq_num f
  · intro a b h
    exact Prod.ext (card1Vals_inj (congrArg Prod.fst h))
      (card1Vals_inj (congrArg Prod.snd h))

lemma index_lt_of_vals (i j : Fin 9) (hij : card1Vals i < card1Vals j) : i < j := by
  by_contra h
  have : j ≤ i := le_of_not_gt h
  have : card1Vals j ≤ card1Vals i := card1Vals_strictMono.monotone this
  exact absurd hij (not_lt_of_ge this)

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
lemma fixed_has_card2 : ∀ e ∈ fixedPairs,
    (line e.1 ∩ T).card = 2 ∨ (line e.2 ∩ T).card = 2 := by
  decide

lemma fixed_disjoint_extra (f : Fin 9 → Bool) : Disjoint fixedPairs (extraPairs f) := by
  refine Finset.disjoint_left.2 ?_
  intro e hefix heex
  have h2 := fixed_has_card2 e hefix
  simp only [extraPairs, Finset.mem_image, extraIndexPairs, Finset.mem_filter] at heex
  obtain ⟨⟨i, j⟩, ⟨_, _⟩, rfl⟩ := heex
  have hi : (line (card1Vals i) ∩ T).card = 1 := card1Vals_is_card1 i
  have hj : (line (card1Vals j) ∩ T).card = 1 := card1Vals_is_card1 j
  rcases h2 with h | h
  · exact (by omega : ¬(line (card1Vals i) ∩ T).card = 2) h
  · exact (by omega : ¬(line (card1Vals j) ∩ T).card = 2) h

lemma conflictPairs_lift_eq (f : Fin 9 → Bool) :
    conflictPairs (lift f) = fixedPairs ∪ extraPairs f := by
  ext e
  constructor
  · intro he
    simp only [conflictPairs, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with ⟨hlt, hm⟩
    rcases mutual_classification (lift f) e.1 e.2 hlt hm with hfix | ⟨hs, hs'⟩
    · exact Finset.mem_union_left _ hfix
    · obtain ⟨i, hi⟩ := exists_card1_index e.1 hs
      obtain ⟨j, hj⟩ := exists_card1_index e.2 hs'
      have hij : i < j := index_lt_of_vals i j (by simpa [hi, hj] using hlt)
      refine Finset.mem_union_right _ ?_
      simp only [extraPairs, Finset.mem_image, extraIndexPairs, Finset.mem_filter,
        Finset.mem_univ, true_and]
      refine ⟨(i, j), ⟨hij, ?_⟩, ?_⟩
      · simpa [hi, hj] using hm
      · simp [hi, hj]
  · intro he
    simp only [Finset.mem_union] at he
    rcases he with hfix | hex
    · exact fixed_subset_conflicts (lift f) hfix
    · simp only [extraPairs, Finset.mem_image, extraIndexPairs, Finset.mem_filter,
        Finset.mem_univ, true_and] at hex
      obtain ⟨⟨i, j⟩, ⟨hij, hm⟩, rfl⟩ := hex
      have hlt : card1Vals i < card1Vals j := card1Vals_strictMono hij
      simp [conflictPairs, hlt, hm]

lemma conflict_card_eq_formula (f : Fin 9 → Bool) :
    (conflictPairs (lift f)).card = 12 + extraNum f := by
  have hcup := conflictPairs_lift_eq f
  have hdis := fixed_disjoint_extra f
  calc (conflictPairs (lift f)).card
      = (fixedPairs ∪ extraPairs f).card := by rw [hcup]
    _ = fixedPairs.card + (extraPairs f).card := Finset.card_union_of_disjoint hdis
    _ = 12 + (extraPairs f).card := by rw [fixedPairs_card]
    _ = 12 + extraNum f := by rw [extraPairs_card]

lemma min_over_lift (f : Fin 9 → Bool) :
    12 ≤ (conflictPairs (lift f)).card ∧
      ((conflictPairs (lift f)).card = 12 ↔
        (∀ i : Fin 9, f i = true) ∨ (∀ i : Fin 9, f i = false)) := by
  have hform := conflict_card_eq_formula f
  have hmin := extraNum_min f
  constructor
  · omega
  · constructor
    · intro hc
      have : extraNum f = 0 := by omega
      exact hmin.1 this
    · intro hc
      have : extraNum f = 0 := hmin.2 hc
      omega

lemma card1_of_all_true (c : Fin 21 → Bool)
    (h : ∀ i : Fin 9, extract c i = true) :
    ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = true := by
  intro s hs
  have hs' := (card1_eq s).1 hs
  rcases hs' with h' | h' | h' | h' | h' | h' | h' | h' | h'
  · simpa [h', extract, card1Vals] using h 0
  · simpa [h', extract, card1Vals] using h 1
  · simpa [h', extract, card1Vals] using h 2
  · simpa [h', extract, card1Vals] using h 3
  · simpa [h', extract, card1Vals] using h 4
  · simpa [h', extract, card1Vals] using h 5
  · simpa [h', extract, card1Vals] using h 6
  · simpa [h', extract, card1Vals] using h 7
  · simpa [h', extract, card1Vals] using h 8

lemma card1_of_all_false (c : Fin 21 → Bool)
    (h : ∀ i : Fin 9, extract c i = false) :
    ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = false := by
  intro s hs
  have hs' := (card1_eq s).1 hs
  rcases hs' with h' | h' | h' | h' | h' | h' | h' | h' | h'
  · simpa [h', extract, card1Vals] using h 0
  · simpa [h', extract, card1Vals] using h 1
  · simpa [h', extract, card1Vals] using h 2
  · simpa [h', extract, card1Vals] using h 3
  · simpa [h', extract, card1Vals] using h 4
  · simpa [h', extract, card1Vals] using h 5
  · simpa [h', extract, card1Vals] using h 6
  · simpa [h', extract, card1Vals] using h 7
  · simpa [h', extract, card1Vals] using h 8

lemma all_true_of_card1 (c : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = true) :
    ∀ i : Fin 9, extract c i = true := by
  intro i
  exact h (card1Vals i) (card1Vals_is_card1 i)

lemma all_false_of_card1 (c : Fin 21 → Bool)
    (h : ∀ s : Fin 21, (line s ∩ T).card = 1 → c s = false) :
    ∀ i : Fin 9, extract c i = false := by
  intro i
  exact h (card1Vals i) (card1Vals_is_card1 i)

lemma no_conflict_empty (B' : Fin 21 → Fin 21 → Finset (Fin 21))
    (hB : ∀ s p : Fin 21, B' s p ⊆ T)
    (s s' : Fin 21) (hs : line s ∩ T = ∅) :
    ¬ ((∃ p ∈ line s \ line s', (B' s p ∩ line s').Nonempty) ∧
        (∃ p ∈ line s' \ line s, (B' s' p ∩ line s).Nonempty)) := by
  rintro ⟨_, ⟨p, _, hpne⟩⟩
  obtain ⟨q, hq⟩ := hpne
  have hqB : q ∈ B' s' p := (Finset.mem_inter.mp hq).1
  have hqL : q ∈ line s := (Finset.mem_inter.mp hq).2
  have hqT : q ∈ T := hB s' p hqB
  have : q ∈ line s ∩ T := Finset.mem_inter.mpr ⟨hqL, hqT⟩
  simp [hs] at this

lemma B_eq_base (L : Fin 21 → Finset (Fin 21))
    (hL : ∀ t : Fin 21, L t = line t)
    (B : (Fin 21 → Bool) → Fin 21 → Fin 21 → Finset (Fin 21))
    (hB : ∀ (c : Fin 21 → Bool) (s p : Fin 21), B c s p =
      if p ∈ ({0, 1, 2} : Finset (Fin 21)) then (∅ : Finset (Fin 21))
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 then
        ({0, 1, 2} : Finset (Fin 21)) \ L s
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 then
        (if c s then (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image
          (fun v : Fin 21 => if v = 2 then 0 else v + 1)
         else (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image
          (fun v : Fin 21 => if v = 0 then 2 else v - 1))
      else {0})
    (c : Fin 21 → Bool) (s p : Fin 21) :
    B c s p = base c s p := by
  rw [hB, base, hL s]
  rfl

end PEqualNP.Outside.L_meta_1561

open PEqualNP.Outside.L_meta_1561

theorem PEqualNP.Outside.L_meta_1561 : ∀ L : Fin 21 → Finset (Fin 21), (∀ t : Fin 21, L t = {t, t + 1, t + 4, t + 14, t + 16}) →
    ∀ B : (Fin 21 → Bool) → Fin 21 → Fin 21 → Finset (Fin 21),
    (∀ (c : Fin 21 → Bool) (s p : Fin 21), B c s p =
      if p ∈ ({0, 1, 2} : Finset (Fin 21)) then (∅ : Finset (Fin 21))
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 then ({0, 1, 2} : Finset (Fin 21)) \ L s
      else if (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 then
        (if c s then (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 2 then 0 else v + 1)
         else (L s ∩ ({0, 1, 2} : Finset (Fin 21))).image (fun v : Fin 21 => if v = 0 then 2 else v - 1))
      else {0}) →
    (∀ s s' : Fin 21, s ≠ s' → (((∃ p ∈ L s \ L s', ((B (fun _ => true)) s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, ((B (fun _ => true)) s' p ∩ L s).Nonempty)) ↔
      (((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2) ∨
       ((L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s' ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s = ∅) ∨
       ((L s' ∩ ({0, 1, 2} : Finset (Fin 21))).card = 2 ∧ (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 ∧ L s ∩ ({0, 1, 2} : Finset (Fin 21)) ∩ L s' = ∅)))) ∧
    ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B (fun _ => true)) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B (fun _ => true)) e.2 p ∩ L e.1).Nonempty)))).card = 12 ∧
    (∀ B' : Fin 21 → Fin 21 → Finset (Fin 21), (∀ s p : Fin 21, B' s p ⊆ ({0, 1, 2} : Finset (Fin 21))) →
      ∀ s s' : Fin 21, L s ∩ ({0, 1, 2} : Finset (Fin 21)) = ∅ → ¬ ((∃ p ∈ L s \ L s', (B' s p ∩ L s').Nonempty) ∧ (∃ p ∈ L s' \ L s, (B' s' p ∩ L s).Nonempty))) ∧
    (∀ c : Fin 21 → Bool, 12 ≤ ((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card ∧
      (((Finset.univ : Finset (Fin 21 × Fin 21)).filter (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, ((B c) e.1 p ∩ L e.2).Nonempty) ∧ (∃ p ∈ L e.2 \ L e.1, ((B c) e.2 p ∩ L e.1).Nonempty)))).card = 12 ↔
        ((∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = true) ∨ (∀ s : Fin 21, (L s ∩ ({0, 1, 2} : Finset (Fin 21))).card = 1 → c s = false)))) := by
  intro L hL B hB
  have hLine : ∀ t, L t = line t := fun t => by
    simpa [line] using hL t
  have hBase : ∀ c s p, B c s p = base c s p := fun c s p =>
    B_eq_base L hLine B hB c s p
  have hMut : ∀ c s s',
      (((∃ p ∈ L s \ L s', (B c s p ∩ L s').Nonempty) ∧
        (∃ p ∈ L s' \ L s, (B c s' p ∩ L s).Nonempty)) ↔ mutualB c s s' = true) := by
    intro c s s'
    simp only [hLine s, hLine s', hBase, mutual_iff]
  have hPairs : ∀ c,
      (Finset.univ : Finset (Fin 21 × Fin 21)).filter
        (fun e => e.1 < e.2 ∧ ((∃ p ∈ L e.1 \ L e.2, (B c e.1 p ∩ L e.2).Nonempty) ∧
          (∃ p ∈ L e.2 \ L e.1, (B c e.2 p ∩ L e.1).Nonempty))) =
      conflictPairs c := by
    intro c
    ext e
    simp only [conflictPairs, Finset.mem_filter, Finset.mem_univ, true_and, hMut c]
  refine ⟨?char, ?card, ?empty, ?min⟩
  · intro s s' hs
    have h1 := char_iff_true s s' hs
    have h2 := charB_iff s s'
    rw [hMut, hLine s, hLine s',
      show ({0, 1, 2} : Finset (Fin 21)) = T from rfl]
    have hm : mutualB (fun _ => true) s s' = true ↔ charB s s' = true := by
      simp [h1]
    exact hm.trans h2
  · rw [hPairs]
    exact conflict_card_true
  · intro B' hB' s s' hs
    have hs' : line s ∩ T = ∅ := by
      simpa [hLine, show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hs
    have hB'' : ∀ s p, B' s p ⊆ T := by
      intro s p
      simpa [show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hB' s p
    simpa [hLine] using no_conflict_empty B' hB'' s s' hs'
  · intro c
    have hmin := min_over_lift (extract c)
    have hEq : conflictPairs c = conflictPairs (lift (extract c)) := conflictPairs_eq_lift c
    refine And.intro ?le ?iff
    · rw [hPairs, hEq]
      exact hmin.1
    · constructor
      · intro hc
        have hc' : (conflictPairs (lift (extract c))).card = 12 := by
          rwa [hPairs, hEq] at hc
        rcases (hmin.2).1 hc' with ht | hf
        · left
          intro s hsL
          have hs' : (line s ∩ T).card = 1 := by
            simpa [hLine, show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hsL
          exact card1_of_all_true c ht s hs'
        · right
          intro s hsL
          have hs' : (line s ∩ T).card = 1 := by
            simpa [hLine, show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hsL
          exact card1_of_all_false c hf s hs'
      · intro hconst
        have hbits : (∀ i : Fin 9, extract c i = true) ∨ (∀ i : Fin 9, extract c i = false) := by
          rcases hconst with ht | hf
          · left
            exact all_true_of_card1 c (fun s hs => ht s (by
              simpa [hLine, show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hs))
          · right
            exact all_false_of_card1 c (fun s hs => hf s (by
              simpa [hLine, show ({0, 1, 2} : Finset (Fin 21)) = T from rfl] using hs))
        have : (conflictPairs (lift (extract c))).card = 12 := (hmin.2).2 hbits
        rwa [hPairs, hEq]
