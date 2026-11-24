import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1600

open PEqualNP.CircuitLowerBounds
open PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def unitInput {n : ℕ} (u : Fin n) : Fin n → Bool :=
  fun w => decide (w = u)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma getD_append_left_lt (w t : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ t).getD i false = w.getD i false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_self (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (le_refl w.length)]
  simp

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]

lemma foldl_step_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (step w g).length := by
      simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
    rw [ih (step w g) hlt]
    exact getD_append_left_lt w _ i hi

lemma foldl_step_getD_ge (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : w.length + gs.length ≤ i) :
    (gs.foldl step w).getD i false = false := by
  apply getD_ge_len; rw [foldl_step_len]; exact hi

lemma foldl_step_gate (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate)
    (hj : gs[j]? = some g) :
    (gs.foldl step w).getD (w.length + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < w.length + j then (gs.foldl step w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g0 gs ih =>
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      rw [Nat.add_zero, List.foldl_cons]
      have hlt : w.length < (step w g0).length := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [foldl_step_getD_lt gs (step w g0) w.length hlt]
      have hself : (step w g0).getD w.length false =
          g0.op.eval (g0.inputs.map fun i => w.getD i false) := getD_append_self w _
      rw [hself]; congr 1; apply List.map_congr_left; intro i _
      by_cases hi : i < w.length
      · have hilt : i < (step w g0).length := by
          simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
        simp only [hi, ↓reduceIte, foldl_step_getD_lt gs (step w g0) i hilt]
        exact (getD_append_left_lt w _ i hi).symm
      · simp only [hi, ↓reduceIte]; exact getD_ge_len w i (Nat.le_of_not_lt hi)
    | succ j' =>
      simp only [List.getElem?_cons_succ] at hj
      have hlen : (step w g0).length + j' = w.length + (j' + 1) := by
        simp only [step, List.length_append, List.length_cons, List.length_nil]; omega
      rw [List.foldl_cons, ← hlen]; exact ih (step w g0) j' hj

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma wires_gate_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j : ℕ) (g : Gate)
    (hj : C.gates[j]? = some g) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i =>
        if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
  have h := foldl_step_gate C.gates (List.ofFn x) j g hj
  simpa only [List.length_ofFn, ← wires_eq_foldl] using h

lemma ofFn_getD_lt {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (List.ofFn x).getD w false = x ⟨w, hw⟩ := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]

lemma wires_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
  rw [wires_eq_foldl, foldl_step_getD_lt C.gates (List.ofFn x) w (by simp [hw]), ofFn_getD_lt]

lemma wires_oob {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.gates.length ≤ w) :
    (C.wires (List.ofFn x)).getD w false = false := by
  rw [wires_eq_foldl]; exact foldl_step_getD_ge C.gates (List.ofFn x) w (by simp [hw])

lemma gateOp_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f1 f2 : ℕ → Bool) (hle : ∀ i ∈ l, f1 i = true → f2 i = true) :
    op.eval (l.map f1) = true → op.eval (l.map f2) = true := by
  rcases hop with rfl | rfl
  · intro h
    change (l.map f1).all id = true at h
    change (l.map f2).all id = true
    rw [List.all_eq_true] at h ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact hle i hi (h _ (List.mem_map_of_mem hi))
  · intro h
    change (l.map f1).any id = true at h
    change (l.map f2).any id = true
    rw [List.any_eq_true] at h ⊢
    obtain ⟨b, hb, hbt⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨f2 i, List.mem_map_of_mem hi, hle i hi hbt⟩

lemma wires_mono {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ u, x u = true → y u = true) :
    ∀ w : ℕ, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw1 : w < n
    · rw [wires_input C x w hw1, wires_input C y w hw1]; exact hxy ⟨w, hw1⟩
    · by_cases hw2 : n + C.gates.length ≤ w
      · rw [wires_oob C x w hw2]; intro h; exact absurd h Bool.false_ne_true
      · have hjlt : w - n < C.gates.length := by omega
        set j := w - n
        have hwj : w = n + j := by omega
        have hg : C.gates[j]? = some (C.gates[j]'hjlt) := List.getElem?_eq_getElem hjlt
        have hgop : (C.gates[j]'hjlt).op = GateOp.and ∨ (C.gates[j]'hjlt).op = GateOp.or := by
          simpa using (hmono _ (List.mem_of_getElem? hg)).1
        rw [hwj, wires_gate_ofFn C x j _ hg, wires_gate_ofFn C y j _ hg]
        apply gateOp_mono _ hgop
        intro i _ hi
        by_cases hi' : i < n + j
        · simp only [hi', ↓reduceIte] at hi ⊢; exact ih i (by omega) hi
        · simp only [hi', ↓reduceIte] at hi; exact absurd hi Bool.false_ne_true

lemma gateVal_wires {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = (C.wires (List.ofFn x)).getD (n + j) false := rfl

lemma gateAt_get {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by simp [gateAt, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by rw [gateAt_get hj]; exact List.getElem_mem hj

lemma mono_op {C : Circuit} (hmono : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
  simpa [gateAt_get hj] using (hmono _ (gateAt_mem hj)).1

lemma mono_fanin {C : Circuit} (hmono : Monotone2 C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs.length ≤ 2 := by
  simpa [gateAt_get hj] using (hmono _ (gateAt_mem hj)).2

lemma unit_le_pair {n : ℕ} (u v x : Fin n) :
    unitInput u x = true → pairInput u v x = true := by
  simp [unitInput, pairInput]; intro h; exact Or.inl h

lemma unit_le_pair' {n : ℕ} (u v x : Fin n) :
    unitInput v x = true → pairInput u v x = true := by
  simp [unitInput, pairInput]; intro h; exact Or.inr h

lemma wires_mono_unit_pair {n : ℕ} (C : Circuit) (hmono : Monotone2 C) (u v : Fin n) :
    ∀ w : ℕ, (C.wires (List.ofFn (unitInput u))).getD w false = true →
      (C.wires (List.ofFn (pairInput u v))).getD w false = true :=
  wires_mono C hmono _ _ (fun x hx => unit_le_pair u v x hx)

lemma wires_mono_unit_pair' {n : ℕ} (C : Circuit) (hmono : Monotone2 C) (u v : Fin n) :
    ∀ w : ℕ, (C.wires (List.ofFn (unitInput v))).getD w false = true →
      (C.wires (List.ofFn (pairInput u v))).getD w false = true :=
  wires_mono C hmono _ _ (fun x hx => unit_le_pair' u v x hx)

lemma coneStep_length (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).length = cs.length + 1 := by simp [coneStep]

lemma foldl_cone_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, coneStep_length, List.length_cons]
    simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  simpa [cones] using foldl_cone_length n C.gates []

lemma getD_coneStep_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (i : ℕ) (hi : i < cs.length) :
    (coneStep n cs g).getD i [] = cs.getD i [] := by
  simpa [coneStep] using (List.getD_append cs _ ([] : List ℕ) i hi)

lemma getD_coneStep_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  have h := List.getD_append_right cs
    [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])] ([] : List ℕ) cs.length (Nat.le_refl _)
  simpa [coneStep, Nat.sub_self] using h
lemma foldl_cone_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (i : ℕ)
    (hi : i < cs.length) :
    (gs.foldl (coneStep n) cs).getD i [] = cs.getD i [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (coneStep n cs g).length := by rw [coneStep_length]; omega
    rw [ih _ hlt, getD_coneStep_lt _ _ _ _ hi]

lemma foldl_cone_snoc (n : ℕ) (gs : List Gate) (g : Gate) :
    (gs ++ [g]).foldl (coneStep n) [] =
      coneStep n (gs.foldl (coneStep n) []) g := by
  simp [List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma take_len_le (gs : List Gate) (j : ℕ) (hj : j ≤ gs.length) :
    (gs.take j).length = j := List.length_take_of_le hj

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      (coneStep n ((C.gates.take j).foldl (coneStep n) []) (C.gates[j])).getD
        ((C.gates.take j).foldl (coneStep n) []).length [] := by
  have htake : C.gates.take (j + 1) = C.gates.take j ++ [C.gates[j]] :=
    (List.take_concat_get' C.gates j hj).symm
  have hrest : C.gates = C.gates.take (j + 1) ++ C.gates.drop (j + 1) :=
    (List.take_append_drop (j + 1) C.gates).symm
  have hfold_take : (C.gates.take (j + 1)).foldl (coneStep n) [] =
      coneStep n ((C.gates.take j).foldl (coneStep n) []) (C.gates[j]) := by
    rw [htake, foldl_cone_snoc]
  have hlen_take : ((C.gates.take (j + 1)).foldl (coneStep n) []).length = j + 1 := by
    rw [foldl_cone_length, take_len_le _ _ (Nat.succ_le_of_lt hj), List.length_nil, zero_add]
  have hlen_cs : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_cone_length, take_len_le _ _ (le_of_lt hj), List.length_nil, zero_add]
  have hstable :
      ((C.gates.take (j + 1) ++ C.gates.drop (j + 1)).foldl (coneStep n) []).getD j [] =
        ((C.gates.take (j + 1)).foldl (coneStep n) []).getD j [] := by
    have hi : j < ((C.gates.take (j + 1)).foldl (coneStep n) []).length := by
      rw [hlen_take]; omega
    have : (C.gates.take (j + 1) ++ C.gates.drop (j + 1)).foldl (coneStep n) [] =
        (C.gates.drop (j + 1)).foldl (coneStep n)
          ((C.gates.take (j + 1)).foldl (coneStep n) []) := by
      rw [List.foldl_append]
    rw [this]; exact foldl_cone_getD_lt n _ _ _ hi
  have : cones n C =
      (C.gates.take (j + 1) ++ C.gates.drop (j + 1)).foldl (coneStep n) [] := by
    unfold cones
    exact congrArg (List.foldl (coneStep n) []) hrest
  rw [this, hstable, hfold_take]
  congr 1
  exact hlen_cs.symm

lemma cones_getD_prefix (n : ℕ) (C : Circuit) (i j : ℕ)
    (hj : j < C.gates.length) (hi : i < j) :
    (cones n C).getD i [] = ((C.gates.take j).foldl (coneStep n) []).getD i [] := by
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j :=
    (List.take_append_drop j C.gates).symm
  have : cones n C =
      (C.gates.drop j).foldl (coneStep n) ((C.gates.take j).foldl (coneStep n) []) := by
    unfold cones
    have h := congrArg (List.foldl (coneStep n) []) hsplit
    rw [h, List.foldl_append]
  rw [this]
  exact foldl_cone_getD_lt n _ _ i (by
    rw [foldl_cone_length, take_len_le _ _ (le_of_lt hj), List.length_nil, zero_add]; omega)

lemma cone_mem_lt (n : ℕ) (C : Circuit) :
    ∀ t < C.gates.length, ∀ x ∈ (cones n C).getD t [], x < t := by
  intro t ht
  induction t using Nat.strong_induction_on with
  | ind t ih =>
    intro x hx
    have hgett := cones_getD_eq n C t ht
    have hcs : ((C.gates.take t).foldl (coneStep n) []).length = t := by
      rw [foldl_cone_length, take_len_le _ _ (le_of_lt ht), List.length_nil, zero_add]
    rw [hgett, getD_coneStep_last] at hx
    obtain ⟨w, hw, hx2⟩ := List.mem_flatMap.mp hx
    simp only [List.mem_filter, decide_eq_true_eq, hcs] at hw
    simp only [List.mem_cons] at hx2
    rcases hx2 with rfl | hx2
    · omega
    · have hwlt : w - n < t := by omega
      have hpref := cones_getD_prefix n C (w - n) t ht hwlt
      have hx2' : x ∈ (cones n C).getD (w - n) [] := hpref.symm ▸ hx2
      have := ih (w - n) hwlt (lt_trans hwlt ht) x hx2'
      omega

lemma InCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length)
    (h : InCone n C i j) : i < j := by
  unfold InCone at h
  have hget := cones_getD_eq n C j hj
  have hcs : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_cone_length, take_len_le _ _ (le_of_lt hj), List.length_nil, zero_add]
  rw [hget, getD_coneStep_last] at h
  obtain ⟨w, hw, hmem⟩ := List.mem_flatMap.mp h
  simp only [List.mem_filter, decide_eq_true_eq, hcs] at hw
  simp only [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · omega
  · have hwlt : w - n < j := by omega
    have hpref := cones_getD_prefix n C (w - n) j hj hwlt
    have hmem' : i ∈ (cones n C).getD (w - n) [] := hpref.symm ▸ hmem
    have := cone_mem_lt n C (w - n) (lt_trans hwlt hj) i hmem'
    omega

lemma InCone_of_input (n : ℕ) (C : Circuit) (j i : ℕ)
    (hj : j < C.gates.length) (hin : n + i ∈ (gateAt C j).inputs) (hi : i < j) :
    InCone n C i j := by
  unfold InCone
  have hcs : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_cone_length, take_len_le _ _ (le_of_lt hj), List.length_nil, zero_add]
  have hget := cones_getD_eq n C j hj
  rw [hget, getD_coneStep_last]
  refine List.mem_flatMap.mpr ⟨n + i, ?_, ?_⟩
  · have hin' : n + i ∈ (C.gates[j]).inputs := by simpa [gateAt_get hj] using hin
    simp [List.mem_filter, hin', hi, hcs]
  · simp

lemma InCone_nest (n : ℕ) (C : Circuit) :
    ∀ b < C.gates.length, ∀ a, a ∈ (cones n C).getD b [] →
      ∀ c, c ∈ (cones n C).getD a [] → c ∈ (cones n C).getD b [] := by
  intro b hb
  induction b using Nat.strong_induction_on with
  | ind b ih =>
    intro a ha c hc
    have hgett := cones_getD_eq n C b hb
    have hcsb : ((C.gates.take b).foldl (coneStep n) []).length = b := by
      rw [foldl_cone_length, take_len_le _ _ (le_of_lt hb), List.length_nil, zero_add]
    rw [hgett, getD_coneStep_last] at ha ⊢
    obtain ⟨w2, hw2, ha2⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_filter, decide_eq_true_eq, hcsb] at hw2
    simp only [List.mem_cons] at ha2
    have hw2lt : w2 - n < b := by omega
    have hpref := cones_getD_prefix n C (w2 - n) b hb hw2lt
    refine List.mem_flatMap.mpr ⟨w2, ?_, ?_⟩
    · simpa [List.mem_filter, decide_eq_true_eq, hcsb] using hw2
    · simp only [List.mem_cons]
      rcases ha2 with rfl | ha2
      · exact Or.inr (hpref ▸ hc)
      · have ha' : a ∈ (cones n C).getD (w2 - n) [] := hpref.symm ▸ ha2
        have hc' := ih (w2 - n) hw2lt (lt_trans hw2lt hb) a ha' c hc
        exact Or.inr (hpref ▸ hc')

lemma InCone_trans (n : ℕ) (C : Circuit) (k i j : ℕ)
    (hj : j < C.gates.length) (hki : InCone n C k i) (hij : InCone n C i j) :
    InCone n C k j := by
  have hi := InCone_lt n C i j hj hij
  unfold InCone at *
  have hcs : ((C.gates.take j).foldl (coneStep n) []).length = j := by
    rw [foldl_cone_length, take_len_le _ _ (le_of_lt hj), List.length_nil, zero_add]
  have hget := cones_getD_eq n C j hj
  rw [hget, getD_coneStep_last] at hij ⊢
  obtain ⟨w, hw, hmem⟩ := List.mem_flatMap.mp hij
  simp only [List.mem_filter, decide_eq_true_eq, hcs] at hw
  simp only [List.mem_cons] at hmem
  refine List.mem_flatMap.mpr ⟨w, ?_, ?_⟩
  · simpa [List.mem_filter, decide_eq_true_eq, hcs] using hw
  · simp only [List.mem_cons]
    have hwlt : w - n < j := by omega
    have hpref := cones_getD_prefix n C (w - n) j hj hwlt
    rcases hmem with rfl | hmem
    · exact Or.inr (hpref ▸ hki)
    · have hi_in : i ∈ (cones n C).getD (w - n) [] := hpref.symm ▸ hmem
      have hk_in := InCone_nest n C (w - n) (lt_trans hwlt hj) i hi_in k hki
      exact Or.inr (hpref ▸ hk_in)

lemma InCone_of_input_of_InCone (n : ℕ) (C : Circuit) (j i k : ℕ)
    (hj : j < C.gates.length) (hij : InCone n C i j)
    (hin : n + k ∈ (gateAt C i).inputs) (hki : k < i) :
    InCone n C k j := by
  have hi := InCone_lt n C i j hj hij
  have hi_len : i < C.gates.length := lt_trans hi hj
  exact InCone_trans n C k i j hj (InCone_of_input n C i k hi_len hin hki) hij

def readWire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (j w : ℕ) : Bool :=
  if w < n + j then (C.wires (List.ofFn x)).getD w false else false

lemma gateVal_and_reads {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔ ∀ w ∈ (gateAt C j).inputs, readWire C x j w = true := by
  rw [gateVal_wires, wires_gate_ofFn C x j (gateAt C j)
    (by rw [gateAt_get hj]; exact List.getElem?_eq_getElem hj)]
  simp only [hand, GateOp.eval, List.all_eq_true, List.mem_map, id]
  constructor
  · intro h w hw
    exact h _ ⟨w, hw, rfl⟩
  · intro h b hb
    obtain ⟨w, hw, rfl⟩ := hb
    exact h w hw

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : graphFun G ∅ (unitInput u) = false := by
  simp only [graphFun]
  have hA : decide (∃ a ∈ (∅ : Finset (Fin n)), unitInput u a = true) = false := by simp
  have hE : decide (∃ a b : Fin n, G.Adj a b ∧ unitInput u a = true ∧ unitInput u b = true) =
      false := by
    simp only [decide_eq_false_iff_not, unitInput, decide_eq_true_eq]
    rintro ⟨a, b, hab, ha, hb⟩
    subst ha; subst hb
    exact G.irrefl hab
  simp [hA, hE]

lemma false_on_units {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ)
    (hsupp : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true)
    (u : Fin n) : gateVal n C j (unitInput u) = false := by
  cases h : gateVal n C j (unitInput u) with
  | false => rfl
  | true =>
    have := hsupp _ h
    rw [graphFun_unit_false G u] at this
    exact (Bool.false_ne_true this).elim

lemma adj_of_graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {u v : Fin n} (hne : u ≠ v) (h : graphFun G ∅ (pairInput u v) = true) :
    G.Adj u v := by
  simp only [graphFun, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with hA | hE
  · obtain ⟨a, ha, _⟩ := hA
    exact (Finset.notMem_empty a ha).elim
  · obtain ⟨a, b, hab, ha, hb⟩ := hE
    have ha' : a = u ∨ a = v := by
      simp only [pairInput, decide_eq_true_eq] at ha; exact ha
    have hb' : b = u ∨ b = v := by
      simp only [pairInput, decide_eq_true_eq] at hb; exact hb
    rcases ha' with hau | hav
    · rcases hb' with hbu | hbv
      · subst hau; subst hbu; exact (G.irrefl hab).elim
      · subst hau; subst hbv; exact hab
    · rcases hb' with hbu | hbv
      · subst hav; subst hbu; exact hab.symm
      · subst hav; subst hbv; exact (G.irrefl hab).elim

lemma wire_true_iff_units {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (u v : Fin n)
    (hand_cone : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput u v) = false)
    (w : ℕ) (hw : w < n + j)
    (hincone : w < n ∨ InCone n C (w - n) j) :
    (C.wires (List.ofFn (pairInput u v))).getD w false = true ↔
      (C.wires (List.ofFn (unitInput u))).getD w false = true ∨
        (C.wires (List.ofFn (unitInput v))).getD w false = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwin : w < n
    · constructor
      · intro h
        rw [wires_input C _ w hwin] at h
        rw [wires_input C _ w hwin, wires_input C _ w hwin]
        simpa [pairInput, unitInput] using h
      · intro h
        rw [wires_input C _ w hwin, wires_input C _ w hwin] at h
        rw [wires_input C _ w hwin]
        simpa [pairInput, unitInput] using h
    · have hwgate : n ≤ w := Nat.le_of_not_lt hwin
      have hi : w - n < j := by omega
      have hcone : InCone n C (w - n) j := by
        cases hincone with
        | inl h => exact absurd h (Nat.not_lt.mpr hwgate)
        | inr h => exact h
      set i := w - n
      have hi_len : i < C.gates.length := lt_trans hi hj
      have hg : C.gates[i]? = some (gateAt C i) := by
        rw [gateAt_get hi_len]; exact List.getElem?_eq_getElem hi_len
      have hw_eq : w = n + i := by omega
      have hop := mono_op hmono hi_len
      constructor
      · intro htrue
        rcases hop with hand | hor
        · have hfalse := hand_cone i hi hcone hand
          have htrue' : gateVal n C i (pairInput u v) = true := by
            rwa [gateVal_wires, ← hw_eq]
          exact (Bool.false_ne_true (hfalse ▸ htrue')).elim
        · rw [hw_eq, wires_gate_ofFn C _ i _ hg] at htrue
          simp only [hor, GateOp.eval, List.any_eq_true, List.mem_map, id] at htrue
          obtain ⟨b, ⟨t, ht_in, rfl⟩, hbt⟩ := htrue
          have ht_lt : t < n + i := by
            by_contra hnge
            have : ¬ t < n + i := hnge
            simp only [this, ↓reduceIte] at hbt
            exact Bool.false_ne_true hbt
          simp only [ht_lt, ↓reduceIte] at hbt
          have ht_cone : t < n ∨ InCone n C (t - n) j := by
            by_cases ht_n : t < n
            · exact Or.inl ht_n
            · have ht_gate : n ≤ t := Nat.le_of_not_lt ht_n
              have htk : t - n < i := by omega
              have hinp' : n + (t - n) ∈ (gateAt C i).inputs := by
                rwa [Nat.add_sub_of_le ht_gate]
              exact Or.inr (InCone_of_input_of_InCone n C j i (t - n) hj hcone hinp' htk)
          have ih_t := ih t (by omega) (by omega) ht_cone
          rcases ih_t.mp hbt with hu | hv
          · refine Or.inl ?_
            rw [hw_eq, wires_gate_ofFn C (unitInput u) i _ hg]
            simp only [hor, GateOp.eval, List.any_eq_true, List.mem_map, id]
            exact ⟨_, ⟨t, ht_in, rfl⟩, by simpa [ht_lt] using hu⟩
          · refine Or.inr ?_
            rw [hw_eq, wires_gate_ofFn C (unitInput v) i _ hg]
            simp only [hor, GateOp.eval, List.any_eq_true, List.mem_map, id]
            exact ⟨_, ⟨t, ht_in, rfl⟩, by simpa [ht_lt] using hv⟩
      · intro hunits
        rcases hunits with hu | hv
        · exact wires_mono_unit_pair C hmono u v w hu
        · exact wires_mono_unit_pair' C hmono u v w hv

lemma read_true_iff_units {n : ℕ} (C : Circuit) (hmono : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (u v : Fin n)
    (hand_cone : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
      gateVal n C i (pairInput u v) = false)
    (w : ℕ) (hw_in : w ∈ (gateAt C j).inputs)
    (hpair : readWire C (pairInput u v) j w = true) :
    readWire C (unitInput u) j w = true ∨ readWire C (unitInput v) j w = true := by
  simp only [readWire] at hpair ⊢
  by_cases hw : w < n + j
  · simp only [hw, ↓reduceIte] at hpair ⊢
    have hincone : w < n ∨ InCone n C (w - n) j := by
      by_cases hwn : w < n
      · exact Or.inl hwn
      · have : n ≤ w := Nat.le_of_not_lt hwn
        have hi : w - n < j := by omega
        have hinp : n + (w - n) ∈ (gateAt C j).inputs := by
          rwa [Nat.add_sub_of_le this]
        exact Or.inr (InCone_of_input n C j (w - n) hj hinp hi)
    exact (wire_true_iff_units C hmono j hj u v hand_cone w hw hincone).mp hpair
  · simp only [hw, ↓reduceIte] at hpair
    exact (Bool.false_ne_true hpair).elim

lemma biclique_c4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    {a1 a2 b1 b2 : Fin n}
    (ha : a1 ≠ a2) (hb : b1 ≠ b2)
    (h11 : G.Adj a1 b1) (h21 : G.Adj a2 b1) (h22 : G.Adj a2 b2) (h12 : G.Adj a1 b2) :
    False := by
  have h := hc4 a1 b1 a2 b2 ha hb
  exact h ⟨h11, h21.symm, h22, h12.symm⟩

lemma star_of_and {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hc4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit) (hmono : Monotone2 C)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hsupp : ∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) :
    (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
      ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  classical
  let inputs := (gateAt C j).inputs
  let left : ℕ := inputs.headD (n + j)
  let right : ℕ := (inputs.drop 1).headD (n + j)
  let A : Finset (Fin n) :=
    Finset.univ.filter fun x => readWire C (unitInput x) j left = true
  let B : Finset (Fin n) :=
    Finset.univ.filter fun x => readWire C (unitInput x) j right = true
  have hfan : inputs.length ≤ 2 := mono_fanin hmono hj
  have hfalse_unit := false_on_units G C j hsupp
  have hall_of_LR (x : Fin n → Bool)
      (hL : readWire C x j left = true) (hR : readWire C x j right = true) :
      ∀ w ∈ (gateAt C j).inputs, readWire C x j w = true := by
    intro w hw
    cases hinputs : (gateAt C j).inputs with
    | nil => simp [hinputs] at hw
    | cons a rest =>
      cases hrest : rest with
      | nil =>
        have hw' : w = a := by simpa [hinputs, hrest, List.mem_singleton] using hw
        have hleft : left = a := by simp [left, inputs, hinputs, hrest]
        subst hw'; simpa [hleft] using hL
      | cons b rest' =>
        have hlen : rest'.length + 2 ≤ 2 := by
          have := hfan
          simp only [inputs, hinputs, hrest, List.length_cons] at this
          omega
        have hrest' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest'
        have hw' : w = a ∨ w = b := by
          simpa [hinputs, hrest, List.mem_cons, List.mem_singleton] using hw
        have hleft : left = a := by simp [left, inputs, hinputs, hrest]
        have hright : right = b := by simp [right, inputs, hinputs, hrest]
        rcases hw' with rfl | rfl
        · simpa [hleft] using hL
        · simpa [hright] using hR
  have hcross : ∀ u ∈ A, ∀ v ∈ B, u ≠ v → G.Adj u v := by
    intro u hu v hv hne
    have hlu : readWire C (unitInput u) j left = true := (Finset.mem_filter.mp hu).2
    have hrv : readWire C (unitInput v) j right = true := (Finset.mem_filter.mp hv).2
    have hltL : left < n + j := by
      by_contra hnge
      simp only [readWire, hnge, ↓reduceIte] at hlu
      exact Bool.false_ne_true hlu
    have hltR : right < n + j := by
      by_contra hnge
      simp only [readWire, hnge, ↓reduceIte] at hrv
      exact Bool.false_ne_true hrv
    have hpairL : readWire C (pairInput u v) j left = true := by
      simp only [readWire, hltL, ↓reduceIte] at hlu ⊢
      exact wires_mono_unit_pair C hmono u v left hlu
    have hpairR : readWire C (pairInput u v) j right = true := by
      simp only [readWire, hltR, ↓reduceIte] at hrv ⊢
      exact wires_mono_unit_pair' C hmono u v right hrv
    have hgate : gateVal n C j (pairInput u v) = true :=
      (gateVal_and_reads C hj hand _).2 (hall_of_LR _ hpairL hpairR)
    exact adj_of_graphFun_pair G hne (hsupp _ hgate)
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro u huA huB
    have hLu : readWire C (unitInput u) j left = true := (Finset.mem_filter.mp huA).2
    have hRu : readWire C (unitInput u) j right = true := (Finset.mem_filter.mp huB).2
    have ht : gateVal n C j (unitInput u) = true :=
      (gateVal_and_reads C hj hand _).2 (hall_of_LR _ hLu hRu)
    exact Bool.false_ne_true (hfalse_unit u ▸ ht)
  have hneAB : ∀ u ∈ A, ∀ v ∈ B, u ≠ v := fun u hu v hv heq =>
    Finset.disjoint_left.mp hdisj hu (heq ▸ hv)
  have hcard : A.card ≤ 1 ∨ B.card ≤ 1 := by
    by_contra h
    push Not at h
    obtain ⟨a1, a2, ha1, ha2, hane⟩ := Finset.one_lt_card_iff.mp h.1
    obtain ⟨b1, b2, hb1, hb2, hbne⟩ := Finset.one_lt_card_iff.mp h.2
    exact biclique_c4 G hc4 hane hbne
      (hcross a1 ha1 b1 hb1 (hneAB a1 ha1 b1 hb1))
      (hcross a2 ha2 b1 hb1 (hneAB a2 ha2 b1 hb1))
      (hcross a2 ha2 b2 hb2 (hneAB a2 ha2 b2 hb2))
      (hcross a1 ha1 b2 hb2 (hneAB a1 ha1 b2 hb2))
  have howned :
      ∀ u v : Fin n, G.Adj u v → Owns n C j u v →
        (u ∈ A ∧ v ∈ B) ∨ (u ∈ B ∧ v ∈ A) := by
    intro u v _hadj howns
    unfold Owns at howns
    obtain ⟨_, _, htrue, hcone⟩ := howns
    have hall := (gateVal_and_reads C hj hand _).1 htrue
    have hcone' : ∀ i < j, InCone n C i j → (gateAt C i).op = GateOp.and →
        gateVal n C i (pairInput u v) = false := fun i hi h1 h2 => hcone i hi h1 h2
    cases hinputs : (gateAt C j).inputs with
    | nil =>
      have ht : gateVal n C j (unitInput u) = true := by
        rw [gateVal_and_reads C hj hand]
        intro w hw; simp [hinputs] at hw
      exact (Bool.false_ne_true (hfalse_unit u ▸ ht)).elim
    | cons w0 rest =>
      cases hrest : rest with
      | nil =>
        have hread : readWire C (pairInput u v) j w0 = true :=
          hall w0 (by simp [hinputs, hrest])
        have hdecomp := read_true_iff_units C hmono j hj u v hcone' w0
          (by simp [hinputs, hrest]) hread
        rcases hdecomp with hu | hv
        · have ht : gateVal n C j (unitInput u) = true := by
            rw [gateVal_and_reads C hj hand]
            intro w hw; simp only [hinputs, hrest, List.mem_singleton] at hw; subst hw; exact hu
          exact (Bool.false_ne_true (hfalse_unit u ▸ ht)).elim
        · have ht : gateVal n C j (unitInput v) = true := by
            rw [gateVal_and_reads C hj hand]
            intro w hw; simp only [hinputs, hrest, List.mem_singleton] at hw; subst hw; exact hv
          exact (Bool.false_ne_true (hfalse_unit v ▸ ht)).elim
      | cons w1 rest' =>
        have hlen : rest'.length + 2 ≤ 2 := by
          have := hfan
          simp only [inputs, hinputs, hrest, List.length_cons] at this
          omega
        have hrest' : rest' = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst hrest'
        have hL := read_true_iff_units C hmono j hj u v hcone' w0
          (by simp [hinputs, hrest]) (hall w0 (by simp [hinputs, hrest]))
        have hR := read_true_iff_units C hmono j hj u v hcone' w1
          (by simp [hinputs, hrest]) (hall w1 (by simp [hinputs, hrest]))
        have memA : ∀ x, x ∈ A ↔ readWire C (unitInput x) j w0 = true := by
          intro x; simp [A, left, inputs, hinputs, hrest]
        have memB : ∀ x, x ∈ B ↔ readWire C (unitInput x) j w1 = true := by
          intro x; simp [B, right, inputs, hinputs, hrest]
        rcases hL with huL | hvL
        · have huA : u ∈ A := (memA u).mpr huL
          rcases hR with huR | hvR
          · exact (Finset.disjoint_left.mp hdisj huA ((memB u).mpr huR)).elim
          · exact Or.inl ⟨huA, (memB v).mpr hvR⟩
        · have hvA : v ∈ A := (memA v).mpr hvL
          rcases hR with huR | hvR
          · exact Or.inr ⟨(memB u).mpr huR, hvA⟩
          · exact (Finset.disjoint_left.mp hdisj hvA ((memB v).mpr hvR)).elim
  rcases hcard with hA | hB
  · by_cases hA0 : A.card = 0
    · have hAempty : A = ∅ := Finset.card_eq_zero.mp hA0
      refine Or.inl ?_
      intro u v hadj howns
      rcases howned u v hadj howns with ⟨huA, _⟩ | ⟨_, hvA⟩
      · simp [hAempty] at huA
      · simp [hAempty] at hvA
    · have hA1 : A.card = 1 := by omega
      obtain ⟨s, hsA⟩ := Finset.card_eq_one.mp hA1
      refine Or.inr ⟨s, ?_⟩
      intro p q hpq howns
      rcases howned p q hpq howns with ⟨hpA, _⟩ | ⟨_, hqA⟩
      · exact Or.inl (Finset.mem_singleton.mp (hsA ▸ hpA))
      · exact Or.inr (Finset.mem_singleton.mp (hsA ▸ hqA))
  · by_cases hB0 : B.card = 0
    · have hBempty : B = ∅ := Finset.card_eq_zero.mp hB0
      refine Or.inl ?_
      intro u v hadj howns
      rcases howned u v hadj howns with ⟨_, hvB⟩ | ⟨huB, _⟩
      · simp [hBempty] at hvB
      · simp [hBempty] at huB
    · have hB1 : B.card = 1 := by omega
      obtain ⟨s, hsB⟩ := Finset.card_eq_one.mp hB1
      refine Or.inr ⟨s, ?_⟩
      intro p q hpq howns
      rcases howned p q hpq howns with ⟨_, hqB⟩ | ⟨hpB, _⟩
      · exact Or.inr (Finset.mem_singleton.mp (hsB ▸ hqB))
      · exact Or.inl (Finset.mem_singleton.mp (hsB ▸ hpB))

theorem main : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    (∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) →
    ∀ C : Circuit, Monotone2 C → ∀ j : ℕ, j < C.gates.length →
      (gateAt C j).op = GateOp.and →
      (∀ x : Fin n → Bool, gateVal n C j x = true → graphFun G ∅ x = true) →
      (∀ u v : Fin n, G.Adj u v → ¬ Owns n C j u v) ∨
        ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → Owns n C j p q → p = s ∨ q = s := by
  intro n G _ hc4 C hmono j hj hand hsupp
  exact star_of_and G hc4 C hmono j hj hand hsupp

end PEqualNP.Outside.L_meta_1600

theorem PEqualNP.Outside.L_meta_1600 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c d : Fin n, a ≠ c → b ≠ d → ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a)) → ∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C → ∀ j : ℕ, j < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ x : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n C j x = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true) → (∀ u v : Fin n, G.Adj u v → ¬ PEqualNP.EdgeOwnership.Owns n C j u v) ∨ ∃ s : Fin n, ∀ p q : Fin n, G.Adj p q → PEqualNP.EdgeOwnership.Owns n C j p q → p = s ∨ q = s :=
  PEqualNP.Outside.L_meta_1600.main
