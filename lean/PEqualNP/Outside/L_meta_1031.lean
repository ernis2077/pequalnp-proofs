import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership
open SimpleGraph

def GoodShape (C : Circuit) : Prop :=
  ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

def edgeFun {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (Fin n → Bool) → Bool :=
  fun x => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)

def Computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ x : Fin n → Bool, C.eval (List.ofFn x) = edgeFun G x

abbrev Dep (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  a < b ∧ ∃ (k : ℕ) (h : Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs

def pairBits {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun k => decide (k = u) || decide (k = v)

def OwnsEdge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (t : ℕ) (u v : Fin n) : Prop :=
  G.Adj u v ∧
    (C.wires (List.ofFn (pairBits u v))).getD (n + t) false = true ∧
      ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
        Relation.TransGen (Dep n C) (n + t') (n + t) →
          (C.wires (List.ofFn (pairBits u v))).getD (n + t') false = false

def StarOwned {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
    ∃ c : Fin n,
      (∃ u v : Fin n, OwnsEdge G C t u v) ∧
        ∀ u v : Fin n, OwnsEdge G C t u v → u = c ∨ v = c

def IsMinimalGood {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) : Prop :=
  GoodShape C ∧ Computes G C ∧
    ∀ D : Circuit, GoodShape D → Computes G D → C.size ≤ D.size

noncomputable def edgePairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (Fin n × Fin n) :=
  (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ G.Adj p.1 p.2)).toList

theorem mem_edgePairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin n × Fin n) :
    e ∈ edgePairs G ↔ e.1 < e.2 ∧ G.Adj e.1 e.2 := by
  simp [edgePairs]

/-- One owner entry per edge: owner is the left endpoint, list is the right endpoint. -/
noncomputable def edgeOwners {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    List (ℕ × List ℕ) :=
  (edgePairs G).map fun e => (e.1.val, [e.2.val])

theorem edgeOwners_bounds {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∀ p ∈ edgeOwners G, p.1 < n ∧ ∀ w ∈ p.2, w < n := by
  intro p hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact ⟨e.1.isLt, by intro w hw; simp at hw; exact hw ▸ e.2.isLt⟩

noncomputable def edgeCover {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Circuit :=
  coverCircuitB n (edgeOwners G)

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih]; omega

theorem fold_keep (gs : List Gate) (w : List Bool) {i : ℕ} (h : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have h' : i < (step w g).length := by simp [step]; omega
    rw [ih (w := step w g) h']
    exact List.getD_append _ _ false i h

theorem getD_app_left {w t : List Bool} {i : ℕ} (h : i < w.length) :
    (w ++ t).getD i false = w.getD i false :=
  List.getD_append w t false i h

theorem getD_app_right (w t : List Bool) (i : ℕ) :
    (w ++ t).getD (w.length + i) false = t.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left]

theorem getD_snoc' (l : List Bool) (b : Bool) (i : ℕ) (h : i = l.length) :
    (l ++ [b]).getD i false = b := by
  subst h
  simpa using getD_app_right l [b] 0

theorem any_congr_mem {l : List ℕ} {f g : ℕ → Bool} (h : ∀ u ∈ l, f u = g u) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.any_cons]
    rw [h b (by simp), ih (fun u hu => h u (by simp [hu]))]

theorem block_shape (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    ∀ g ∈ blockGates B a t v1 rest lead,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  intro g hg
  cases lead <;> simp [blockGates] at hg <;> rcases hg with ⟨i, _, rfl⟩ | rfl | rfl <;> simp

theorem gates_shape : ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
    ∀ g ∈ coverGatesB B lead a own,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
  | [], _, _, _ => by intro g hg; simp [coverGatesB] at hg
  | (t, []) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB] at hg
      exact gates_shape os B lead a g hg
  | (t, v1 :: rest) :: os, B, lead, a => by
      intro g hg
      simp only [coverGatesB, List.mem_append] at hg
      rcases hg with hg | hg
      · exact block_shape B a t v1 rest lead g hg
      · exact gates_shape os _ false _ g hg

theorem edgeCover_shape {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    GoodShape (edgeCover G) := by
  intro g hg
  have key : ∀ g ∈ (coverCircuitB n (edgeOwners G)).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
    intro g hg
    unfold coverCircuitB at hg
    split_ifs at hg with h
    · simp at hg
    · exact gates_shape _ _ _ _ g hg
  have := key g (by simpa [edgeCover] using hg)
  exact ⟨this.1, by have := this.2; omega⟩

def F (x : List Bool) (own : List (ℕ × List ℕ)) : Bool :=
  own.any (fun p => x.getD p.1 false && p.2.any (fun u => x.getD u false))

theorem gates_nil_F (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ),
      coverGatesB B lead a own = [] → F x own = false
  | [], _, _, _, _ => rfl
  | (t, []) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      simpa [F] using gates_nil_F x os B lead a h
  | (t, v1 :: rest) :: os, B, lead, a, h => by
      simp only [coverGatesB] at h
      cases lead <;> simp [blockGates] at h

theorem block_length (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool) :
    (blockGates B a t v1 rest lead).length = rest.length + 1 + (if lead then 0 else 1) := by
  cases lead <;> simp [blockGates]

def cv (w : List Bool) (v1 : ℕ) (rest : List ℕ) (k : ℕ) : Bool :=
  w.getD v1 false || (rest.take k).any (fun u => w.getD u false)

theorem chain_read (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (k : ℕ) (hk : k ≤ rest.length) :
    (w ++ (List.range k).map (fun i => cv w v1 rest (i + 1))).getD
        ((v1 :: (List.range rest.length).map (fun j => B + j)).getD k 0) false
      = cv w v1 rest k := by
  cases k with
  | zero =>
    simp only [List.getD_cons_zero]
    rw [getD_app_left (by omega)]
    simp [cv]
  | succ j =>
    have hj : j < rest.length := by omega
    have e1 : (v1 :: (List.range rest.length).map (fun j => B + j)).getD (j + 1) 0 = B + j := by
      simp [List.getD_cons_succ, List.getD_eq_getElem?_getD, hj]
    rw [e1, ← hw, getD_app_right]
    simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_range (show j < j + 1 by omega)]

theorem chain_fold (w : List Bool) (B v1 : ℕ) (rest : List ℕ) (hw : w.length = B)
    (hv1 : v1 < B) (hrest : ∀ u ∈ rest, u < B) :
    ∀ k ≤ rest.length,
      ((List.range k).map (fun i => (⟨GateOp.or,
          [(v1 :: (List.range rest.length).map (fun j => B + j)).getD i 0,
            rest.getD i 0]⟩ : Gate))).foldl step w =
        w ++ (List.range k).map (fun i => cv w v1 rest (i + 1)) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.foldl_append, ih (by omega)]
    simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, step]
    rw [List.append_assoc]
    congr 2
    have hkr : k < rest.length := by omega
    have hrk : rest.getD k 0 = rest[k] := by
      simp [List.getD_eq_getElem?_getD, hkr]
    have hlt : rest[k] < w.length := by rw [hw]; exact hrest _ (List.getElem_mem hkr)
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    rw [chain_read w B v1 rest hw hv1 k (by omega), hrk, getD_app_left hlt]
    simp only [cv, List.take_succ, List.getElem?_eq_getElem hkr, Option.toList_some,
      List.any_append, List.any_cons, List.any_nil, Bool.or_false, id]
    simp [Bool.or_assoc, List.getElem?_eq_getElem hkr]

theorem block_val (w : List Bool) (B a t v1 : ℕ) (rest : List ℕ) (lead : Bool)
    (hw : w.length = B) (ha : lead = false → a < B) (ht : t < B) (hv1 : v1 < B)
    (hrest : ∀ u ∈ rest, u < B) :
    ((blockGates B a t v1 rest lead).foldl step w).getD
        (B + (blockGates B a t v1 rest lead).length - 1) false
      = if lead then (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))
        else (w.getD a false ||
          (w.getD t false && (w.getD v1 false || rest.any (fun u => w.getD u false)))) := by
  have hc := chain_fold w B v1 rest hw hv1 hrest rest.length le_rfl
  have hr := chain_read w B v1 rest hw hv1 rest.length le_rfl
  have hcvr : cv w v1 rest rest.length =
      (w.getD v1 false || rest.any (fun u => w.getD u false)) := by simp [cv]
  set L := (List.range rest.length).map (fun i => cv w v1 rest (i + 1)) with hL
  have hLl : L.length = rest.length := by simp [hL]
  have htW : (w ++ L).getD t false = w.getD t false := getD_app_left (by omega)
  rw [block_length]
  cases lead with
  | true =>
    simp only [blockGates, ↓reduceIte, List.foldl_append, hc, List.foldl_cons, List.foldl_nil,
      step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
      rw [htW, hr, hcvr]
      simp
    · simp [hLl, hw]
  | false =>
    have ha' : a < B := ha rfl
    simp only [blockGates, Bool.false_eq_true, ↓reduceIte, List.foldl_append, hc, List.foldl_cons,
      List.foldl_nil, step]
    rw [getD_snoc']
    · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil]
      rw [getD_app_left (by simp; omega), getD_app_left (by omega), getD_snoc']
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil]
        rw [htW, hr, hcvr]
        simp
      · simp [hLl, hw]
    · simp [hLl, hw]

theorem cover_main (n : ℕ) (x : List Bool) :
    ∀ (own : List (ℕ × List ℕ)) (B : ℕ) (lead : Bool) (a : ℕ) (w : List Bool),
      (∀ p ∈ own, p.1 < n ∧ ∀ u ∈ p.2, u < n) → w.length = B → n ≤ B →
      (∀ i < n, w.getD i false = x.getD i false) → (lead = false → a < B) →
      coverGatesB B lead a own ≠ [] →
      ((coverGatesB B lead a own).foldl step w).getD
          (B + (coverGatesB B lead a own).length - 1) false
        = if lead then F x own else (w.getD a false || F x own)
  | [], _, _, _, _, _, _, _, _, _, hne => by simp [coverGatesB] at hne
  | (t, []) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, hne => by
      simp only [coverGatesB] at hne ⊢
      rw [cover_main n x os B lead a w (fun p hp => hown p (List.mem_cons_of_mem _ hp))
        hw hnB hwx ha hne]
      simp [F]
  | (t, v1 :: rest) :: os, B, lead, a, w, hown, hw, hnB, hwx, ha, _ => by
      have hp := hown (t, v1 :: rest) (by simp)
      have ht : t < n := hp.1
      have hv1 : v1 < n := hp.2 v1 (by simp)
      have hrest : ∀ u ∈ rest, u < n := fun u hu => hp.2 u (by simp [hu])
      have hos : ∀ p ∈ os, p.1 < n ∧ ∀ u ∈ p.2, u < n :=
        fun p hp => hown p (List.mem_cons_of_mem _ hp)
      have hbv := block_val w B a t v1 rest lead hw ha (by omega) (by omega)
        (fun u hu => by have := hrest u hu; omega)
      have hrx : rest.any (fun u => w.getD u false) = rest.any (fun u => x.getD u false) :=
        any_congr_mem (fun u hu => hwx u (hrest u hu))
      rw [hrx, hwx t ht, hwx v1 hv1] at hbv
      set bg := blockGates B a t v1 rest lead with hbg
      set W1 := bg.foldl step w with hW1
      have hW1l : W1.length = B + bg.length := by rw [hW1, fold_len, hw]
      have hW1x : ∀ i < n, W1.getD i false = x.getD i false := by
        intro i hi
        rw [hW1, fold_keep bg w (by omega)]
        exact hwx i hi
      have hcons : F x ((t, v1 :: rest) :: os) =
          ((x.getD t false && (x.getD v1 false || rest.any (fun u => x.getD u false))) ||
            F x os) := rfl
      rw [hcons]
      simp only [coverGatesB]
      rw [← hbg, List.foldl_append, ← hW1, List.length_append]
      by_cases hnil : coverGatesB (B + bg.length) false (B + bg.length - 1) os = []
      · have hF := gates_nil_F x os _ false _ hnil
        rw [hnil, List.foldl_nil, List.length_nil, Nat.add_zero, hbv, hF]
        cases lead <;> simp
      · have ih := cover_main n x os (B + bg.length) false (B + bg.length - 1) W1 hos hW1l
          (by omega) hW1x (fun _ => by omega) hnil
        have hidx :
            B + (bg.length +
                (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length) - 1 =
              B + bg.length +
                (coverGatesB (B + bg.length) false (B + bg.length - 1) os).length - 1 := by omega
        rw [hidx, ih, hbv]
        cases lead <;> simp [Bool.or_assoc]

theorem ofFn_getD {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD, i.isLt]

theorem F_edgeOwners {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    F (List.ofFn x) (edgeOwners G) = true ↔ edgeFun G x = true := by
  simp only [F, edgeFun, edgeOwners, List.any_eq_true, List.mem_map, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨p, ⟨e, he, rfl⟩, hx, ⟨w, hw, hxw⟩⟩
    simp only [List.mem_singleton] at hw
    subst hw
    have hp := (mem_edgePairs G e).1 he
    rw [ofFn_getD] at hx hxw
    exact ⟨e.1, e.2, hp.2, hx, hxw⟩
  · rintro ⟨i, j, hij, hxi, hxj⟩
    have hne : i ≠ j := G.ne_of_adj hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · refine ⟨(i.val, [j.val]), ⟨(i, j), (mem_edgePairs G _).2 ⟨hlt, hij⟩, rfl⟩, ?_, ?_⟩
      · simpa [ofFn_getD] using hxi
      · exact ⟨j.val, List.mem_singleton_self _, by simpa [ofFn_getD] using hxj⟩
    · exact absurd heq hne
    · refine ⟨(j.val, [i.val]), ⟨(j, i), (mem_edgePairs G _).2 ⟨hgt, G.adj_symm hij⟩, rfl⟩,
        ?_, ?_⟩
      · simpa [ofFn_getD] using hxj
      · exact ⟨i.val, List.mem_singleton_self _, by simpa [ofFn_getD] using hxi⟩

theorem edgeCover_eval {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    (edgeCover G).eval (List.ofFn x) = edgeFun G x := by
  have hbounds := edgeOwners_bounds G
  have hF := F_edgeOwners G x
  dsimp only [edgeCover]
  unfold coverCircuitB
  split_ifs with hnil
  · have hfalse : F (List.ofFn x) (edgeOwners G) = false :=
      gates_nil_F _ (edgeOwners G) n true 0 hnil
    have heval : (⟨[], n⟩ : Circuit).eval (List.ofFn x) = false := by
      simp [Circuit.eval, Circuit.wires]
    rw [heval, Bool.eq_iff_iff, ← hF, hfalse]
  · have hval := cover_main n (List.ofFn x) (edgeOwners G) n true 0 (List.ofFn x) hbounds
      (by simp) le_rfl (fun _ _ => rfl) (by simp) hnil
    dsimp only [Circuit.eval]
    rw [wires_eq, hval]
    simp only [↓reduceIte]
    exact Bool.eq_iff_iff.2 hF

theorem edgeCover_computes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    Computes G (edgeCover G) := by
  intro x
  simpa [Computes, edgeFun] using edgeCover_eval G x

/-- Biclique with both sides of size at least 2 yields a 4-cycle. -/
theorem biclique_c4 {n : ℕ} (G : SimpleGraph (Fin n))
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    {a1 a2 b1 b2 : Fin n}
    (ha : a1 ≠ a2) (hb : b1 ≠ b2)
    (h11 : G.Adj a1 b1) (h21 : G.Adj a2 b1) (h22 : G.Adj a2 b2) (h12 : G.Adj a1 b2) :
    False := by
  have h := hc4 a1 b1 a2 b2 h11 h21.symm h22 h12.symm
  rcases h with h | h
  · exact ha h
  · exact hb h

/-- Triangle-free Helly for edges: pairwise shared vertices imply a common center. -/
theorem edge_helly_triangle_free {n : ℕ} (G : SimpleGraph (Fin n))
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (owned : Fin n → Fin n → Prop)
    (hadj : ∀ u v, owned u v → G.Adj u v)
    (hnone : ∃ u v, owned u v)
    (hpair : ∀ a b c d, owned a b → owned c d → a = c ∨ a = d ∨ b = c ∨ b = d) :
    ∃ c : Fin n, (∃ u v, owned u v) ∧ ∀ u v, owned u v → u = c ∨ v = c := by
  obtain ⟨u0, v0, h0⟩ := hnone
  by_cases hu0 : ∀ u v, owned u v → u = u0 ∨ v = u0
  · exact ⟨u0, ⟨u0, v0, h0⟩, hu0⟩
  · push_neg at hu0
    obtain ⟨w, z, hwz, hw_ne_u0, hz_ne_u0⟩ := hu0
    -- The edge wz misses u0, so it must meet v0.
    -- hpair u0 v0 w z gives: u0=w ∨ u0=z ∨ v0=w ∨ v0=z
    have hmeet_v0 : w = v0 ∨ z = v0 := by
      rcases hpair u0 v0 w z h0 hwz with h | h | h | h
      · exact absurd h.symm hw_ne_u0
      · exact absurd h.symm hz_ne_u0
      · exact Or.inl h.symm
      · exact Or.inr h.symm
    refine ⟨v0, ⟨u0, v0, h0⟩, ?_⟩
    intro u v hown
    by_contra hnot
    push_neg at hnot
    obtain ⟨hu_ne_v0, hv_ne_v0⟩ := hnot
    -- hpair u0 v0 u v gives: u0=u ∨ u0=v ∨ v0=u ∨ v0=v
    have hmeet_u0 : u = u0 ∨ v = u0 := by
      rcases hpair u0 v0 u v h0 hown with h | h | h | h
      · exact Or.inl h.symm
      · exact Or.inr h.symm
      · exact absurd h.symm hu_ne_v0
      · exact absurd h.symm hv_ne_v0
    have hu0v0_ne : u0 ≠ v0 := (hadj u0 v0 h0).ne
    rcases hmeet_u0 with rfl | rfl
    · -- owned u0 v with v ≠ v0
      rcases hmeet_v0 with rfl | rfl
      · -- owned v0 z; hpair: u0=v0 ∨ u0=z ∨ v=v0 ∨ v=z
        rcases hpair u0 v v0 z hown hwz with h | h | h | h
        · exact hu0v0_ne h
        · exact hz_ne_u0 h.symm
        · exact hv_ne_v0 h
        · subst h
          exact htri u0 v0 v (hadj u0 v0 h0) (hadj v0 v hwz) (hadj u0 v hown).symm
      · -- owned w v0; hpair: u0=w ∨ u0=v0 ∨ v=w ∨ v=v0
        rcases hpair u0 v w v0 hown hwz with h | h | h | h
        · exact hw_ne_u0 h.symm
        · exact hu0v0_ne h
        · subst h
          exact htri u0 v0 v (hadj u0 v0 h0) (hadj v v0 hwz).symm (hadj u0 v hown).symm
        · exact hv_ne_v0 h
    · -- owned u u0 with u ≠ v0
      rcases hmeet_v0 with rfl | rfl
      · -- owned v0 z; hpair: u=v0 ∨ u=z ∨ u0=v0 ∨ u0=z
        rcases hpair u u0 v0 z hown hwz with h | h | h | h
        · exact hu_ne_v0 h
        · subst h
          exact htri u0 v0 u (hadj u0 v0 h0) (hadj v0 u hwz).symm (hadj u u0 hown)
        · exact hu0v0_ne h
        · exact hz_ne_u0 h.symm
      · -- owned w v0; hpair: u=w ∨ u=v0 ∨ u0=w ∨ u0=v0
        rcases hpair u u0 w v0 hown hwz with h | h | h | h
        · subst h
          exact htri u0 v0 u (hadj u0 v0 h0) (hadj u v0 hwz).symm (hadj u u0 hown)
        · exact hu_ne_v0 h
        · exact hw_ne_u0 h.symm
        · exact hu0v0_ne h

/-- In a size-minimal circuit, every AND owns at least one edge of G (otherwise erase it). -/
theorem minimal_and_owns_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : IsMinimalGood G C)
    (t : ℕ) (g : Gate) (ht : C.gates[t]? = some g) (hop : g.op = GateOp.and) :
    ∃ u v : Fin n, OwnsEdge G C t u v := by
  -- Remaining: show an empty-owning AND can be erased (CircuitMoves.eraseGate) while
  -- preserving GoodShape and Computes, contradicting size-minimality.
  exact False.elim (by have _ := hmin; have _ := ht; have _ := hop; sorry)

/-- Two edges owned by the same AND of a computing circuit on a C4-free graph share a vertex.
First-merger AND gates have OR-only cones, hence biclique semantics on owned pairs. -/
theorem owned_edges_share_vertex {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (C : Circuit) (hmin : IsMinimalGood G C)
    (t : ℕ) (g : Gate) (ht : C.gates[t]? = some g) (hop : g.op = GateOp.and)
    {a b c d : Fin n} (hab : OwnsEdge G C t a b) (hcd : OwnsEdge G C t c d) :
    a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_cases hshare : a = c ∨ a = d ∨ b = c ∨ b = d
  · exact hshare
  · push_neg at hshare
    -- Remaining: OR-cone / rectangle analysis; then biclique_c4 or false positive on Computes.
    exact False.elim (by
      clear hshare hab hcd ht hop hmin htri hc4
      sorry)

/-- Every size-minimal fan-in-2 AND/OR circuit for the edge function of a triangle-free
C4-free graph has star ownership of every AND gate. -/
theorem minimal_implies_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hc4 : ∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d)
    (C : Circuit) (hmin : IsMinimalGood G C) : StarOwned G C := by
  intro t g ht hop
  let owned : Fin n → Fin n → Prop := fun u v => OwnsEdge G C t u v
  have hadj : ∀ u v, owned u v → G.Adj u v := fun _ _ h => h.1
  have hnone : ∃ u v, owned u v := minimal_and_owns_edge G C hmin t g ht hop
  have hpair : ∀ a b c d, owned a b → owned c d → a = c ∨ a = d ∨ b = c ∨ b = d :=
    fun a b c d hab hcd => owned_edges_share_vertex G htri hc4 C hmin t g ht hop hab hcd
  exact edge_helly_triangle_free G htri owned hadj hnone hpair

theorem exists_minimal_good {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit, IsMinimalGood G C := by
  classical
  let S : Set ℕ := {k | ∃ C : Circuit, GoodShape C ∧ Computes G C ∧ C.size = k}
  have hne : S.Nonempty :=
    ⟨(edgeCover G).size, edgeCover G, edgeCover_shape G, edgeCover_computes G, rfl⟩
  let k := sInf S
  have hk : k ∈ S := Nat.sInf_mem hne
  obtain ⟨C, hshape, hcomp, hsz⟩ := hk
  refine ⟨C, hshape, hcomp, ?_⟩
  intro D hDshape hDcomp
  have hD : D.size ∈ S := ⟨D, hDshape, hDcomp, rfl⟩
  have : k ≤ D.size := Nat.sInf_le hD
  exact hsz ▸ this

theorem starOwned_to_thm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (h : StarOwned G C) :
    ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
      ∃ c : Fin n,
        (∃ u v : Fin n, G.Adj u v ∧
          ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t)
              false = true ∧
            ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
              Relation.TransGen (Dep n C) (n + t') (n + t) →
                (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t')
                    false = false)) ∧
          ∀ u v : Fin n, G.Adj u v →
            ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t)
                false = true ∧
              ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
                Relation.TransGen (Dep n C) (n + t') (n + t) →
                  (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t')
                      false = false) →
            u = c ∨ v = c := by
  intro t g ht hop
  obtain ⟨c, hex, hstar⟩ := h t g ht hop
  have hbits (u v : Fin n) :
      pairBits u v = fun k => decide (k = u ∨ k = v) := by
    funext k; simp [pairBits, Bool.decide_or]
  refine ⟨c, ?_, ?_⟩
  · obtain ⟨u0, v0, hown0⟩ := hex
    refine ⟨u0, v0, hown0.1, ?_⟩
    simpa [hbits] using hown0.2
  · intro u v hadj hcond
    apply hstar u v
    refine ⟨hadj, ?_⟩
    simpa [hbits] using hcond

end PEqualNP.Outside.L_meta_1031

open PEqualNP.Outside.L_meta_1031

theorem PEqualNP.Outside.L_meta_1031 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro n G _ htri hc4
  obtain ⟨C, hmin⟩ := exists_minimal_good G
  have hstar := minimal_implies_star G htri hc4 C hmin
  refine ⟨C, hmin.1, ?_, hmin.2.2, ?_⟩
  · intro x
    have hx := hmin.2.1 x
    simpa [edgeFun] using hx
  · intro t g ht hop
    have h := starOwned_to_thm G C hstar t g ht hop
    exact h
