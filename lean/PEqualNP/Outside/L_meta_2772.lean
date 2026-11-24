import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2772

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl step x := rfl

lemma length_foldl (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

lemma getD_foldl_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (step w g).length := by simp [step]; omega
    rw [ih (step w g) hlt]
    simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma gateAt_get {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_get hj]; exact List.getElem_mem hj

def patchGate (C : Circuit) (g b w' : ℕ) : Gate :=
  ⟨(gateAt C g).op, (gateAt C g).inputs.set b w'⟩

def patchC (C : Circuit) (g b w' : ℕ) : Circuit :=
  ⟨C.gates.set g (patchGate C g b w'), C.output⟩

lemma patch_size (C : Circuit) (g b w' : ℕ) : (patchC C g b w').size = C.size := by
  simp [patchC, Circuit.size]

lemma patch_gates_length (C : Circuit) (g b w' : ℕ) :
    (patchC C g b w').gates.length = C.gates.length := by
  simp [patchC]

lemma patch_output (C : Circuit) (g b w' : ℕ) :
    (patchC C g b w').output = C.output := rfl

lemma wires_of_gates_output (gs : List Gate) (o o' : ℕ) (x : List Bool) :
    (⟨gs, o⟩ : Circuit).wires x = (⟨gs, o'⟩ : Circuit).wires x := by
  simp [Circuit.wires]

lemma patch_gateAt_self {C : Circuit} (g b w' : ℕ) (hg : g < C.gates.length) :
    gateAt (patchC C g b w') g = patchGate C g b w' := by
  have hg' : g < (C.gates.set g (patchGate C g b w')).length := by simpa using hg
  simp [patchC, gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg',
    List.getElem_set_self]

lemma patch_gateAt_ne {C : Circuit} (g k b w' : ℕ) (hne : g ≠ k) (_hk : k < C.gates.length) :
    gateAt (patchC C g b w') k = gateAt C k := by
  simp [patchC, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma patch_getElem_self {C : Circuit} (g b w' : ℕ) (hg : g < C.gates.length) :
    (patchC C g b w').gates[g]'(by simpa [patchC] using hg) = patchGate C g b w' := by
  simp [patchC, List.getElem_set_self]

lemma patch_getElem_ne {C : Circuit} (g k b w' : ℕ) (hne : g ≠ k) (hk : k < C.gates.length) :
    (patchC C g b w').gates[k]'(by simpa [patchC] using hk) = C.gates[k] :=
  List.getElem_set_ne hne (by simpa [patchC] using hk)

lemma patch_AndOrOnly (C : Circuit) (g b w' : ℕ) (hg : g < C.gates.length)
    (h : AndOrOnly C) : AndOrOnly (patchC C g b w') := by
  intro gg hgg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (by simpa [patchC] using hgg)
  have hkC : k < C.gates.length := by simpa [patchC] using hk
  by_cases hgk : g = k
  · subst hgk
    simpa [List.getElem_set_self, patchGate, gateAt_get hg, patchC] using h _ (gateAt_mem hg)
  · rw [List.getElem_set_ne hgk (by simpa [patchC] using hk)]
    exact h _ (List.getElem_mem hkC)

lemma patch_len2 (C : Circuit) (g b w' : ℕ) (hg : g < C.gates.length)
    (h : ∀ gg ∈ C.gates, gg.inputs.length = 2) :
    ∀ gg ∈ (patchC C g b w').gates, gg.inputs.length = 2 := by
  intro gg hgg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (by simpa [patchC] using hgg)
  have hkC : k < C.gates.length := by simpa [patchC] using hk
  by_cases hgk : g = k
  · subst hgk
    have hlen : (gateAt C g).inputs.length = 2 := h _ (gateAt_mem hg)
    simp [List.getElem_set_self, patchGate, List.length_set, hlen, patchC]
  · rw [List.getElem_set_ne hgk (by simpa [patchC] using hk)]
    exact h _ (List.getElem_mem hkC)

lemma patch_ReadsBack (n : ℕ) (C : Circuit) (g b w' : ℕ)
    (hg : g < C.gates.length) (hw' : w' < n + g) (_hb : b < 2)
    (hRB : ReadsBack n C) (_hlen2 : (gateAt C g).inputs.length = 2) :
    ReadsBack n (patchC C g b w') := by
  intro j hj i hi
  have hjC : j < C.gates.length := by simpa [patchC] using hj
  by_cases hgj : g = j
  · subst hgj
    have hi' : i ∈ (gateAt C g).inputs.set b w' := by
      simpa [patch_gateAt_self g b w' hg, patchGate] using hi
    rcases List.mem_or_eq_of_mem_set hi' with h | rfl
    · exact hRB g hg i h
    · exact hw'
  · have hgate : gateAt (patchC C g b w') j = gateAt C j :=
      patch_gateAt_ne g j b w' hgj hjC
    rw [hgate] at hi
    exact hRB j hjC i hi

lemma patch_IsAO2 (n : ℕ) (C : Circuit) (g b w' : ℕ)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hw' : w' < n + g) (hb : b < 2) :
    IsAO2 n (patchC C g b w') :=
  ⟨patch_AndOrOnly C g b w' hg hAO.1,
    patch_ReadsBack n C g b w' hg hw' hb hAO.2.1 (hAO.2.2 _ (gateAt_mem hg)),
    patch_len2 C g b w' hg hAO.2.2⟩

def pref (C : Circuit) (x : List Bool) (j : ℕ) : List Bool :=
  (C.gates.take j).foldl step x

lemma pref_zero (C : Circuit) (x : List Bool) : pref C x 0 = x := by simp [pref]

lemma pref_succ (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    pref C x (j + 1) = step (pref C x j) C.gates[j] := by
  simp only [pref]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons, List.foldl_nil]

lemma length_pref (C : Circuit) (x : List Bool) (j : ℕ) (hj : j ≤ C.gates.length) :
    (pref C x j).length = x.length + j := by
  simp [pref, length_foldl, List.length_take, Nat.min_eq_left hj]

lemma pref_full (C : Circuit) (x : List Bool) :
    pref C x C.gates.length = C.wires x := by
  simp [pref, wires_eq_foldl, List.take_length]

lemma pref_get_as_wires (C : Circuit) (x : List Bool) (j i : ℕ)
    (hj : j ≤ C.gates.length) (hi : i < x.length + j) :
    (pref C x j).getD i false = (C.wires x).getD i false := by
  have hdrop : C.wires x = (C.gates.drop j).foldl step (pref C x j) := by
    simp only [wires_eq_foldl, pref]
    conv_lhs => rw [← List.take_append_drop j C.gates]
    rw [List.foldl_append]
  have hlen : (pref C x j).length = x.length + j := length_pref C x j hj
  rw [hdrop]
  exact (getD_foldl_lt _ _ _ (by rw [hlen]; exact hi)).symm

lemma prefs_agree_before (_n : ℕ) (C : Circuit) (g b w' : ℕ) (x : List Bool)
    (hg : g < C.gates.length) :
    ∀ j ≤ g, pref (patchC C g b w') x j = pref C x j := by
  intro j hj
  induction j with
  | zero => simp [pref_zero]
  | succ j ih =>
    have hjl : j < C.gates.length := by omega
    rw [pref_succ C x j hjl, pref_succ (patchC C g b w') x j (by simpa [patchC] using hjl),
      ih (by omega)]
    rw [patch_getElem_ne g j b w' (by omega) hjl]

lemma eval_mono_andOr (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (f h : ℕ → Bool) (hm : ∀ i ∈ ins, f i = true → h i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map h) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro hall i hi; exact hm i hi (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, hf⟩; exact ⟨i, hi, hm i hi hf⟩

lemma both_false {n : ℕ} (C : Circuit) (w w' : ℕ) (x : Fin n → Bool)
    (hfun : circuitFun n C x = false)
    (hw' : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true →
      circuitFun n C y = true)
    (himp : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w⟩ (List.ofFn y) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true) :
    Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = false ∧
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = false := by
  refine ⟨?_, ?_⟩
  · by_contra h
    have ht : Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true := Bool.eq_true_of_ne_false h
    exact Bool.eq_false_iff.mp hfun (hw' x (himp x ht))
  · by_contra h
    have ht : Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true := Bool.eq_true_of_ne_false h
    exact Bool.eq_false_iff.mp hfun (hw' x ht)

lemma map_set_eq (ins : List ℕ) (b w' : ℕ) (f : ℕ → Bool) (_hb : b < ins.length) :
    (ins.set b w').map f = (ins.map f).set b (f w') := by
  refine List.ext_getElem (by simp [List.length_set]) ?_
  intro i hi hi2
  rw [List.getElem_map, List.getElem_set, List.getElem_set]
  split_ifs with h
  · rfl
  · rw [List.getElem_map]

lemma andOr_mono_set (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (L : List Bool) (b : ℕ) (v : Bool) (hb : b < L.length)
    (hv : L.getD b false = true → v = true) :
    op.eval L = true → op.eval (L.set b v) = true := by
  have hb' : b < (L.set b v).length := by simpa using hb
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, id_eq]
    intro hall x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_set]
    split_ifs with hEq
    · exact hv (by
        have : L[b] = true := hall _ (List.getElem_mem hb)
        rwa [List.getD_eq_getElem L false hb])
    · exact hall _ (List.getElem_mem (by simpa [List.length_set] using hi))
  · simp only [GateOp.eval, List.any_eq_true, id_eq]
    intro h
    obtain ⟨x, hx, hxtrue⟩ := h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    by_cases hbi : b = i
    · have hvtrue : v = true := hv (by
        have : L[b] = true := by
          have hiL : i < L.length := by simpa [List.length_set] using hi
          have : L[i] = true := hxtrue
          convert this
        rwa [List.getD_eq_getElem L false hb])
      refine ⟨(L.set b v)[b], List.getElem_mem hb', ?_⟩
      rwa [List.getElem_set_self hb']
    · have hi' : i < (L.set b v).length := by simpa using hi
      have hiL : i < L.length := by simpa [List.length_set] using hi
      refine ⟨L[i], ?_, hxtrue⟩
      have : (L.set b v)[i] = L[i] := List.getElem_set_ne hbi hi'
      exact this ▸ List.getElem_mem hi'

lemma andOr_same_on_set_false (op : GateOp) (_hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (b w w' : ℕ) (f : ℕ → Bool)
    (hb : b < ins.length) (hw : ins.getD b 0 = w)
    (hf : f w = false) (hf' : f w' = false) :
    op.eval ((ins.set b w').map f) = op.eval (ins.map f) := by
  have hmap := map_set_eq ins b w' f hb
  have hb' : b < (ins.map f).length := by simpa using hb
  have hget : (ins.map f).getD b false = f w := by
    have hins : ins[b] = w := by
      rwa [← List.getD_eq_getElem ins 0 hb]
    rw [List.getD_eq_getElem _ _ hb', List.getElem_map, hins]
  have heq : (ins.map f).set b (f w') = ins.map f := by
    refine List.ext_getElem (by simp) ?_
    intro i hi hi2
    rw [List.getElem_set]
    split_ifs with hEq
    · have hib : i = b := hEq.symm
      subst hib
      rw [hf', ← hf, ← hget, List.getD_eq_getElem _ _ hb']
    · rfl
  rw [hmap, heq]

lemma wires_eq_false_case (n : ℕ) (C : Circuit) (g b w w' : ℕ) (x : List Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2) (hx : x.length = n)
    (hw : (gateAt C g).inputs.getD b 0 = w) (hw'lt : w' < n + g)
    (hwv : (C.wires x).getD w false = false)
    (hw'v : (C.wires x).getD w' false = false) :
    (patchC C g b w').wires x = C.wires x := by
  have hlen2 : (gateAt C g).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hg)
  have hb' : b < (gateAt C g).inputs.length := by omega
  have hwlt : w < n + g := hAO.2.1 g hg w (by
    have : (gateAt C g).inputs[b] = w := by
      rwa [← List.getD_eq_getElem _ _ hb']
    exact this ▸ List.getElem_mem hb')
  have hw_pref : (pref C x g).getD w false = false := by
    rw [pref_get_as_wires C x g w (by omega) (by omega), hwv]
  have hw'_pref : (pref C x g).getD w' false = false := by
    rw [pref_get_as_wires C x g w' (by omega) (by omega), hw'v]
  have hpref : ∀ j ≤ C.gates.length, pref (patchC C g b w') x j = pref C x j := by
    intro j hj
    induction j with
    | zero => simp [pref_zero]
    | succ j ih =>
      have hjl : j < C.gates.length := by omega
      rw [pref_succ C x j hjl, pref_succ (patchC C g b w') x j (by simpa [patchC] using hjl),
        ih (by omega)]
      by_cases hjg : j = g
      · have hop : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or :=
          hAO.1 _ (gateAt_mem hg)
        have heq := andOr_same_on_set_false (gateAt C g).op hop (gateAt C g).inputs b w w'
          (fun i => (pref C x g).getD i false) hb' hw hw_pref hw'_pref
        have hjlp : j < (patchC C g b w').gates.length := by simpa [patchC] using hjl
        have hgateP : (patchC C g b w').gates[j]'(hjlp) = patchGate C g b w' := by
          simpa [hjg] using patch_getElem_self g b w' hg
        have hgateC : C.gates[j] = gateAt C g := by
          simpa [hjg] using (gateAt_get hg).symm
        rw [hgateP, hgateC, patchGate]
        have heq' :
            (gateAt C g).op.eval
              (((gateAt C g).inputs.set b w').map fun i => (pref C x j).getD i false) =
            (gateAt C g).op.eval
              ((gateAt C g).inputs.map fun i => (pref C x j).getD i false) := by
          simpa [hjg] using heq
        simp only [step]
        rw [heq']
      · rw [patch_getElem_ne g j b w' (Ne.symm hjg) hjl]
  rw [← pref_full C x, ← pref_full (patchC C g b w') x, patch_gates_length]
  exact hpref _ le_rfl

lemma circuitFun_false_case {n : ℕ} (C : Circuit) (g b w w' : ℕ) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hw : (gateAt C g).inputs.getD b 0 = w) (hw'lt : w' < n + g)
    (hfun : circuitFun n C x = false)
    (himp : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w⟩ (List.ofFn y) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true)
    (hw'fun : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true →
      circuitFun n C y = true) :
    circuitFun n (patchC C g b w') x = false := by
  have hboth := both_false C w w' x hfun hw'fun himp
  have hx : (List.ofFn x).length = n := by simp
  have hwires := wires_eq_false_case n C g b w w' (List.ofFn x) hAO hg hb hx hw hw'lt
    (by
      have h1 := hboth.1
      simp only [Circuit.eval] at h1
      rwa [wires_of_gates_output C.gates w C.output (List.ofFn x)] at h1)
    (by
      have h1 := hboth.2
      simp only [Circuit.eval] at h1
      rwa [wires_of_gates_output C.gates w' C.output (List.ofFn x)] at h1)
  simp only [circuitFun, Circuit.eval, patch_output, hwires]
  exact hfun

lemma pref_le_g_eq (n : ℕ) (C : Circuit) (g b w' : ℕ) (x : List Bool)
    (hg : g < C.gates.length) :
    pref (patchC C g b w') x g = pref C x g :=
  prefs_agree_before n C g b w' x hg g le_rfl

lemma getD_step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_step_new (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp [step, List.getD_eq_getElem?_getD]

lemma wires_mono {n : ℕ} (C : Circuit) (g b w w' : ℕ) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hw : (gateAt C g).inputs.getD b 0 = w) (hw'lt : w' < n + g)
    (himp : Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) :
    ∀ i, (C.wires (List.ofFn x)).getD i false = true →
      ((patchC C g b w').wires (List.ofFn x)).getD i false = true := by
  intro i hi
  let xL := List.ofFn x
  have hx : xL.length = n := by simp [xL]
  have hlen2 : (gateAt C g).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hg)
  have hb' : b < (gateAt C g).inputs.length := by omega
  have hwlt : w < n + g := hAO.2.1 g hg w (by
    have : (gateAt C g).inputs[b] = w := by
      rwa [← List.getD_eq_getElem _ _ hb']
    exact this ▸ List.getElem_mem hb')
  have himp_pref :
      (pref C xL g).getD w false = true → (pref C xL g).getD w' false = true := by
    intro hwtrue
    have heval : Circuit.eval ⟨C.gates, w⟩ xL = true := by
      simp only [Circuit.eval]
      rw [wires_of_gates_output C.gates w C.output xL,
        ← pref_get_as_wires C xL g w (by omega) (by omega)]
      exact hwtrue
    have heval' := himp heval
    simp only [Circuit.eval] at heval'
    rw [wires_of_gates_output C.gates w' C.output xL,
      ← pref_get_as_wires C xL g w' (by omega) (by omega)] at heval'
    exact heval'
  have getD_true_lt : ∀ (L : List Bool) (t : ℕ), L.getD t false = true → t < L.length := by
    intro L t ht
    by_contra hge
    have hfalse : L.getD t false = false := List.getD_eq_default L false (Nat.not_lt.mp hge)
    rw [hfalse] at ht
    exact Bool.false_ne_true ht
  have hmono :
      ∀ j ≤ C.gates.length, ∀ t,
        (pref C xL j).getD t false = true →
          (pref (patchC C g b w') xL j).getD t false = true := by
    intro j hj
    induction j with
    | zero =>
      intro t ht; simpa [pref_zero] using ht
    | succ j ih =>
      intro t ht
      have hjl : j < C.gates.length := by omega
      have hlenC : (pref C xL j).length = n + j := by
        simpa [hx] using length_pref C xL j (by omega)
      have hlenP : (pref (patchC C g b w') xL j).length = n + j := by
        have hjle : j ≤ (patchC C g b w').gates.length := by
          simpa [patch_gates_length] using Nat.le_of_lt hjl
        simpa [hx] using length_pref (patchC C g b w') xL j hjle
      rw [pref_succ C xL j hjl] at ht
      rw [pref_succ (patchC C g b w') xL j (by simpa [patchC] using hjl)]
      by_cases hlt : t < n + j
      · have ht' : (pref C xL j).getD t false = true := by
          rwa [getD_step_lt (pref C xL j) _ t (by omega)] at ht
        have ih' := ih (by omega) t ht'
        rwa [getD_step_lt (pref (patchC C g b w') xL j) _ t (by rw [hlenP]; exact hlt)]
      · have ht_len : t = n + j := by
          have ht_range : t < (step (pref C xL j) C.gates[j]).length := getD_true_lt _ _ ht
          have : (step (pref C xL j) C.gates[j]).length = n + j + 1 := by
            simp [step, hlenC]
          omega
        have ht_gate : (C.gates[j]).op.eval
            ((C.gates[j]).inputs.map fun i => (pref C xL j).getD i false) = true := by
          have ht' : (step (pref C xL j) C.gates[j]).getD (n + j) false = true := by
            rwa [ht_len] at ht
          have ht'' : (step (pref C xL j) C.gates[j]).getD (pref C xL j).length false = true := by
            rwa [← hlenC] at ht'
          exact (getD_step_new (pref C xL j) C.gates[j]) ▸ ht''
        by_cases hjg : j = g
        · have hprefEq : pref (patchC C g b w') xL g = pref C xL g :=
            pref_le_g_eq n C g b w' xL hg
          have hop : (gateAt C g).op = GateOp.and ∨ (gateAt C g).op = GateOp.or :=
            hAO.1 _ (gateAt_mem hg)
          have hgateC : C.gates[g] = gateAt C g := (gateAt_get hg).symm
          have ht_gate' : (gateAt C g).op.eval
              ((gateAt C g).inputs.map fun i => (pref C xL g).getD i false) = true := by
            simpa [hjg, hgateC] using ht_gate
          have hjlp : j < (patchC C g b w').gates.length := by simpa [patchC] using hjl
          have hgateP : (patchC C g b w').gates[j]'(hjlp) = patchGate C g b w' := by
            simpa [hjg] using patch_getElem_self g b w' hg
          have hlenPj : (pref (patchC C g b w') xL j).length = n + j := by
            simpa [hx, patch_gates_length] using
              length_pref (patchC C g b w') xL j (Nat.le_of_lt hjlp)
          rw [ht_len, hgateP, patchGate, ← hlenPj, getD_step_new]
          have hprefJ : pref (patchC C g b w') xL j = pref C xL g := by
            simpa [hjg] using hprefEq
          rw [hprefJ]
          have hmap := map_set_eq (gateAt C g).inputs b w'
            (fun i => (pref C xL g).getD i false) hb'
          rw [hmap]
          refine andOr_mono_set (gateAt C g).op hop
            ((gateAt C g).inputs.map fun i => (pref C xL g).getD i false) b
            ((pref C xL g).getD w' false) (by simpa using hb') ?_ ht_gate'
          · intro hwtrue
            have hget : ((gateAt C g).inputs.map fun i =>
                (pref C xL g).getD i false).getD b false =
              (pref C xL g).getD w false := by
              have hins : (gateAt C g).inputs[b] = w := by
                rwa [← List.getD_eq_getElem _ _ hb']
              rw [List.getD_eq_getElem _ _ (by simpa using hb'), List.getElem_map, hins]
            exact himp_pref (hget ▸ hwtrue)
        · have hne : g ≠ j := Ne.symm hjg
          have hjlp : j < (patchC C g b w').gates.length := by
            simpa [patch_gates_length] using hjl
          have hgate : (patchC C g b w').gates[j]'(hjlp) = C.gates[j] :=
            patch_getElem_ne g j b w' hne hjl
          rw [ht_len, hgate, ← hlenP, getD_step_new]
          exact eval_mono_andOr (C.gates[j]).op (hAO.1 _ (List.getElem_mem hjl))
            (C.gates[j]).inputs
            (fun i => (pref C xL j).getD i false)
            (fun i => (pref (patchC C g b w') xL j).getD i false)
            (fun i _ hi => ih (by omega) i hi) ht_gate
  have hi_pref : (pref C xL C.gates.length).getD i false = true := by
    simpa [xL, pref_full] using hi
  have hi' := hmono C.gates.length le_rfl i hi_pref
  have hlenEq : (patchC C g b w').gates.length = C.gates.length := patch_gates_length C g b w'
  have hpref' : (pref (patchC C g b w') xL (patchC C g b w').gates.length).getD i false = true := by
    rwa [hlenEq]
  simpa [xL, pref_full] using hpref'

lemma circuitFun_eq {n : ℕ} (C : Circuit) (g b w w' : ℕ) (x : Fin n → Bool)
    (hAO : IsAO2 n C) (hg : g < C.gates.length) (hb : b < 2)
    (hw : (gateAt C g).inputs.getD b 0 = w) (hw'lt : w' < n + g)
    (himp : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w⟩ (List.ofFn y) = true →
      Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true)
    (hw'fun : ∀ y : Fin n → Bool, Circuit.eval ⟨C.gates, w'⟩ (List.ofFn y) = true →
      circuitFun n C y = true) :
    circuitFun n (patchC C g b w') x = circuitFun n C x := by
  by_cases hfun : circuitFun n C x = true
  · have hm := wires_mono C g b w w' x hAO hg hb hw hw'lt (himp x)
    have hout : (C.wires (List.ofFn x)).getD C.output false = true := by
      simpa [circuitFun, Circuit.eval] using hfun
    have hpatchOut : ((patchC C g b w').wires (List.ofFn x)).getD C.output false = true :=
      hm C.output hout
    have : circuitFun n (patchC C g b w') x = true := by
      simp only [circuitFun, Circuit.eval, patch_output]
      exact hpatchOut
    rw [hfun, this]
  · have hfalse : circuitFun n C x = false := by
      cases hx : circuitFun n C x with
      | false => rfl
      | true => exact (hfun hx).elim
    have := circuitFun_false_case C g b w w' x hAO hg hb hw hw'lt hfalse himp hw'fun
    rw [hfalse, this]

end PEqualNP.Outside.L_meta_2772

theorem PEqualNP.Outside.L_meta_2772 :
    ∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit) (g b w w' : ℕ),
      (PEqualNP.TopForm.IsAO2 n C ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack n C ∧ g < C.gates.length ∧ b < 2 ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.getD b 0 = w ∧ w' < n + g ∧
        (∀ x : Fin n → Bool,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w⟩ (List.ofFn x) = true →
            PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true) ∧
        (∀ x : Fin n → Bool,
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, w'⟩ (List.ofFn x) = true →
            PEqualNP.MetaComplexity.circuitFun n C x = true)) →
      PEqualNP.TopForm.IsAO2 n
          (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op,
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩) ∧
        PEqualNP.MetaComplexity.circuitFun n
            (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op,
              (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩) =
          PEqualNP.MetaComplexity.circuitFun n C ∧
        (⟨C.gates.set g ⟨(PEqualNP.MetaComplexity.NestedCover.gateAt C g).op,
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs.set b w'⟩, C.output⟩ :
            PEqualNP.CircuitLowerBounds.Circuit).size = C.size := by
  intro n C g b w w' h
  have hAO := h.1
  have hg := h.2.2.1
  have hb := h.2.2.2.1
  have hw := h.2.2.2.2.1
  have hw'lt := h.2.2.2.2.2.1
  have himp := h.2.2.2.2.2.2.1
  have hw'fun := h.2.2.2.2.2.2.2
  change PEqualNP.TopForm.IsAO2 n (PEqualNP.Outside.L_meta_2772.patchC C g b w') ∧
      PEqualNP.MetaComplexity.circuitFun n (PEqualNP.Outside.L_meta_2772.patchC C g b w') =
        PEqualNP.MetaComplexity.circuitFun n C ∧
      (PEqualNP.Outside.L_meta_2772.patchC C g b w').size = C.size
  refine ⟨PEqualNP.Outside.L_meta_2772.patch_IsAO2 n C g b w' hAO hg hw'lt hb, ?_,
    PEqualNP.Outside.L_meta_2772.patch_size C g b w'⟩
  funext x
  exact PEqualNP.Outside.L_meta_2772.circuitFun_eq C g b w w' x hAO hg hb hw hw'lt himp hw'fun
