import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_195
noncomputable section

namespace Aa
open Finset

abbrev aC := Fin 4 × Fin 6 → ℂ
abbrev aH := Fin 6 → ℂ

abbrev row (i : Fin 4) : aC →ₗ[ℂ] aH :=
  LinearMap.funLeft ℂ ℂ fun j => (i, j)

def aO (M : aC) : ℂ := ∑ e : Fin 4 ↪ Fin 6, ∏ r, M (r, e r)

abbrev aHw := Fin 6 × Fin 6 × Fin 6 × Fin 6

def yH : aHw ≃ (Fin 4 → Fin 6) where
  toFun p := ![p.1, p.2.1, p.2.2.1, p.2.2.2]
  invFun z := (z 0, z 1, z 2, z 3)
  left_inv _ := rfl
  right_inv z := by ext i; fin_cases i <;> rfl

lemma cK (M : aC) :
    aO M = ∑ j, ∑ l, ∑ m, ∑ n,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
        M (0, j) * M (1, l) * M (2, m) * M (3, n) := by
  classical
  let u (z : Fin 4 → Fin 6) := ∏ r, M (r, z r)
  have A : aO M = ∑ z : Fin 4 → Fin 6, if Function.Injective z then u z else 0 := by
    let E := Equiv.subtypeInjectiveEquivEmbedding (Fin 4) (Fin 6)
    change (∑ e : Fin 4 ↪ Fin 6, u e) = _
    rw [← E.sum_comp (fun e : Fin 4 ↪ Fin 6 => u e), ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (by simp) u).symm
  rw [A, ← yH.sum_comp (fun z => if Function.Injective z then u z else 0)]
  simp only [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ =>
    sum_congr rfl fun c _ => sum_congr rfl fun d _ => ?_
  let z := yH (a, b, c, d)
  have p : z 0 = a := rfl
  have q : z 1 = b := rfl
  have s : z 2 = c := rfl
  have t : z 3 = d := rfl
  have f : Function.Injective z ↔
      ¬ (a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d) := by
    constructor
    · intro o
      have h (i j : Fin 4) (g : i ≠ j) : z i ≠ z j := fun h => g (o h)
      exact not_or_intro (h 0 1 (by decide))
        (not_or_intro (h 0 2 (by decide))
          (not_or_intro (h 0 3 (by decide))
            (not_or_intro (h 1 2 (by decide))
              (not_or_intro (h 1 3 (by decide)) (h 2 3 (by decide))))))
    · intro g i j v
      simp only [not_or] at g
      fin_cases i <;> fin_cases j <;> first | rfl | grind
  change (if Function.Injective z then u z else 0) = _
  by_cases g : a = b ∨ a = c ∨ a = d ∨ b = c ∨ b = d ∨ c = d
  · have k : ¬ Function.Injective z := fun h => f.mp h g
    rw [ite_eq_right k, ite_eq_left g]
  · rw [ite_eq_left (f.mpr g), ite_eq_right g]
    change (∏ r, M (r, z r)) = _
    simp [Fin.prod_univ_succ, p, q, s, t, mul_assoc]

def cW (t : aC) : ℂ := ∑ i : Fin 4, ∑ j, t (i, j)
def pQ (t : aC) : ℂ :=
  ∑ j, ∑ l, if j = l then 0 else ∑ a : Fin 4, ∑ b : Fin 4, if a < b then t (a, j) * t (b, l) else 0
def pR (t : aC) : ℂ :=
  ∑ j, ∑ l, ∑ m, if j = l ∨ j = m ∨ l = m then 0 else
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      if a < b ∧ b < c then t (a, j) * t (b, l) * t (c, m) else 0
def yW (t : aC) : ℂ :=
  ∑ j, ∑ l, ∑ m, ∑ n,
    if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else
      t (0, j) * t (1, l) * t (2, m) * t (3, n)

lemma vH (f : Fin 6 → ℂ) : ∑ j, f j = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  simp [Fin.sum_univ_succ]
  ring

lemma injCount :
    (∑ j : Fin 6, ∑ l : Fin 6, ∑ m : Fin 6, ∑ n : Fin 6,
      if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then (0 : ℕ) else 1) = 360 := by
  decide

set_option maxHeartbeats 8000000 in
lemma oD (t : aC) :
    aO (1 + t) = 360 + 60 * cW t + 12 * pQ t + 3 * pR t + yW t := by
  rw [cK]
  simp (config := { decide := true }) only [cW, pQ, pR, yW, vH, Fin.sum_univ_four,
    Pi.add_apply, Pi.one_apply, ite_true, ite_false, add_zero, zero_add]
  ring

lemma lO (L : Submodule ℂ aC) (hL : ∀ t ∈ L, aO (1 + t) ≠ 0) (i : Fin 4) :
    ∃ f : Module.Dual ℂ aH, f 1 = 1 ∧ ∀ t ∈ L, f (row i t) = 0 := by
  classical
  have a : (1 : aH) ∉ L.map (row i) := by
    rintro ⟨t, d, g⟩
    apply hL (-t) (L.neg_mem d)
    apply sum_eq_zero
    intro e _
    apply Finset.prod_eq_zero (mem_univ i)
    change (1 : ℂ) + -t (i, e i) = 0
    have h : t (i, e i) = 1 := congrFun g (e i)
    rw [h]
    ring
  obtain ⟨f, j, b⟩ := Submodule.exists_dual_map_eq_bot_of_notMem a inferInstance
  refine ⟨(f 1)⁻¹ • f, inv_mul_cancel₀ j, ?_⟩
  intro t d
  have c : f (row i t) ∈ (L.map (row i)).map f := ⟨_, ⟨t, d, rfl⟩, rfl⟩
  rw [b] at c
  change f (row i t) = 0 at c
  change (f 1)⁻¹ * f (row i t) = 0
  simp [c]

abbrev bK (i : Fin 6) : aH := Pi.single i 1

lemma vG (f : Module.Dual ℂ aH) (b : f 1 = 1) : ∃ a, f (bK a) ≠ 0 := by
  classical
  by_contra! h
  have e : ∑ a : Fin 6, bK a = (1 : aH) := by
    ext j
    simp [bK, Finset.sum_apply, Pi.single_apply]
  rw [← e, map_sum] at b
  simp [h] at b

lemma aBr (f g : Module.Dual ℂ aH) (r : f 1 = 1) (s : g 1 = 1) :
    ∃ x y : aH, f x = 1 ∧ g y = 1 ∧ ∀ c d : Fin 6, c ≠ d → x c * y d + x d * y c = 0 := by
  classical
  by_cases e : ∃ a, f (bK a) ≠ 0 ∧ g (bK a) ≠ 0
  · obtain ⟨a, k, j⟩ := e
    refine ⟨(f (bK a))⁻¹ • bK a, (g (bK a))⁻¹ • bK a, by simp [k], by simp [j], ?_⟩
    intro c d i
    by_cases h : a = c
    · subst c
      simp [bK, Ne.symm i]
    · simp [bK, Pi.single_apply, Ne.symm h]
  · obtain ⟨a, k⟩ := vG f r
    obtain ⟨b, j⟩ := vG g s
    have l : g (bK a) = 0 := by
      by_contra h
      exact e ⟨a, k, h⟩
    have n : f (bK b) = 0 := by
      by_contra h
      exact e ⟨b, h, j⟩
    have hab : a ≠ b := by
      rintro rfl
      exact j l
    refine ⟨(f (bK a))⁻¹ • (bK a + bK b), (g (bK b))⁻¹ • (bK b - bK a), by simp [k, n],
      by simp [j, l], ?_⟩
    intro c d i
    by_cases m : c = a
    · subst c
      by_cases q : d = b
      · subst d
        simp [bK, hab, hab.symm]
      · simp [bK, hab, Ne.symm i, q]
    · by_cases o : c = b
      · subst c
        by_cases p : d = a
        · subst d
          simp [bK, hab, hab.symm]
        · simp [bK, m, Ne.symm i, p]
      · simp [bK, Pi.single_apply, m, o]

lemma cD (M : aC) (i j : Fin 4) (a : i ≠ j)
    (h : ∀ c d : Fin 6, c ≠ d → M (i, c) * M (j, d) + M (i, d) * M (j, c) = 0) : aO M = 0 := by
  classical
  let τ := Equiv.swap i j
  let E := Equiv.embeddingCongr τ (Equiv.refl (Fin 6))
  let w (e : Fin 4 ↪ Fin 6) := ∏ r, M (r, e r)
  have f (e : Fin 4 ↪ Fin 6) (r : Fin 4) : E e r = e (Equiv.swap i j r) := by
    change e ((Equiv.swap i j).symm r) = _
    rw [Equiv.symm_swap]
  let S : Finset (Fin 4) := (univ.erase i).erase j
  have aAg (e : Fin 4 ↪ Fin 6) : w e = M (i, e i) * M (j, e j) * ∏ r ∈ S, M (r, e r) := by
    change (∏ r, M (r, e r)) = _
    rw [← mul_prod_erase univ (fun r => M (r, e r)) (mem_univ i),
      ← mul_prod_erase (univ.erase i) (fun r => M (r, e r)) (mem_erase.mpr ⟨a.symm, mem_univ j⟩)]
    exact (mul_assoc _ _ _).symm
  have b (e : Fin 4 ↪ Fin 6) : w e + w (E e) = 0 := by
    have l : (∏ r ∈ S, M (r, E e r)) = ∏ r ∈ S, M (r, e r) := by
      apply prod_congr rfl
      intro r n
      obtain ⟨k, g, _⟩ := (show r ≠ j ∧ r ≠ i ∧ r ∈ univ by simpa [S] using n)
      rw [f, Equiv.swap_apply_of_ne_of_ne g k]
    rw [aAg, aAg, l, f, f]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [← add_mul, h _ _ (fun m => a (e.injective m)), zero_mul]
  have zero : (∑ e, w e) + (∑ e, w e) = 0 := by
    calc
      _ = (∑ e, w e) + (∑ e, w (E e)) := by rw [E.sum_comp w]
      _ = ∑ e, (w e + w (E e)) := Finset.sum_add_distrib.symm
      _ = 0 := sum_eq_zero (fun e _ => b e)
  change (∑ e, w e) = 0
  linear_combination zero / 2

lemma lB (L : Submodule ℂ aC) (hL : ∀ t ∈ L, aO (1 + t) ≠ 0) (i j : Fin 4) (w : i ≠ j) :
    Module.finrank ℂ (L.map ((row i).prod (row j))) ≤ 9 := by
  classical
  obtain ⟨f, k, s⟩ := lO L hL i
  obtain ⟨g, l, v⟩ := lO L hL j
  let P := L.map ((row i).prod (row j))
  let H := (LinearMap.ker f).prod (LinearMap.ker g)
  have n : P ≤ H := by
    rintro _ ⟨t, b, rfl⟩
    exact ⟨s t b, v t b⟩
  have a (u : Module.Dual ℂ aH) (C : u 1 = 1) : Module.finrank ℂ (LinearMap.ker u) = 5 := by
    have B : u ≠ 0 := by
      rintro rfl
      simp at C
    have h := Module.Dual.finrank_ker_add_one_of_ne_zero B
    have d : Module.finrank ℂ aH = 6 := by simp [aH]
    omega
  have dimH : Module.finrank ℂ H = 10 := by
    rw [((LinearMap.ker f).prodEquiv (LinearMap.ker g)).finrank_eq, Module.finrank_prod, a f k, a g l]
  change Module.finrank ℂ P ≤ 9
  by_contra! A
  have q : P = H := Submodule.eq_of_le_of_finrank_le n (by omega)
  obtain ⟨x, y, E, F, m⟩ := aBr f g k l
  have z : (x - 1, y - 1) ∈ P := by
    rw [q]
    exact ⟨by simp [LinearMap.mem_ker, E, k], by simp [LinearMap.mem_ker, F, l]⟩
  obtain ⟨t, b, r⟩ := z
  have o (c) : (1 + t) (i, c) = x c := by
    have e : t (i, c) = x c - 1 := congrFun (congrArg Prod.fst r) c
    change 1 + t (i, c) = x c
    rw [e]
    ring
  have p (c) : (1 + t) (j, c) = y c := by
    have e : t (j, c) = y c - 1 := congrFun (congrArg Prod.snd r) c
    change 1 + t (j, c) = y c
    rw [e]
    ring
  apply hL t b (cD _ i j w ?_)
  simpa only [o, p] using m

end Aa

namespace Ac
open Aa

abbrev aD (L : Submodule ℂ aC) := ∀ t ∈ L, aO (1 + t) = 360
abbrev aX (L : Submodule ℂ aC) := Module.finrank ℂ L

lemma cT {L : Submodule ℂ aC} (hL : aD L) {x : aC} (a : x ∈ L) :
    cW x = 0 ∧ pQ x = 0 ∧ pR x = 0 ∧ yW x = 0 := by
  have h (s : ℂ) :
      360 + 60 * (s * cW x) + 12 * (s ^ 2 * pQ x) + 3 * (s ^ 3 * pR x) + s ^ 4 * yW x = 360 := by
    have e (v w : ℂ) : s * v * (s * w) = s ^ 2 * (v * w) := by ring
    have f (n : ℕ) (v w : ℂ) : (s ^ n * v) * (s * w) = s ^ (n + 1) * (v * w) := by ring
    simpa only [cW, pQ, pR, yW, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero, e, f]
      using (oD (s • x)).symm.trans (hL _ (L.smul_mem s a))
  have := h 1
  have := h (-1)
  have := h 2
  have := h (-2)
  exact ⟨by grobner, by grobner, by grobner, by grobner⟩

lemma aAm (L : Submodule ℂ aC)
    (h : ∀ t ∈ L, cW t = 0 ∧ pQ t = 0 ∧ pR t = 0 ∧ yW t = 0) : aD L := by
  intro x j
  obtain ⟨a, b, c, d⟩ := h x j
  rw [oD, a, b, c, d]
  ring

end Ac

namespace Ac
namespace Av
open Aa Finset

def G3 (j : Fin 6) (x y z : aH) : ℂ :=
  ∑ l, ∑ m, ∑ n, if j = l ∨ j = m ∨ j = n ∨ l = m ∨ l = n ∨ m = n then 0 else x l * y m * z n

def e1 (v : aH) : ℂ := ∑ i, v i

def e2 (v : aH) : ℂ := ∑ i, ∑ j, if i < j then v i * v j else 0

def e3 (v : aH) : ℂ := ∑ i, ∑ j, ∑ k, if i < j ∧ j < k then v i * v j * v k else 0

lemma cJ (j : Fin 6) (x y z : aH) :
    G3 j x y z =
      ((∑ l, x l) - x j) * ((∑ l, y l) - y j) * ((∑ l, z l) - z j)
        - ((∑ l, x l) - x j) * ((∑ l, y l * z l) - y j * z j)
        - ((∑ l, y l) - y j) * ((∑ l, x l * z l) - x j * z j)
        - ((∑ l, z l) - z j) * ((∑ l, x l * y l) - x j * y j)
        + 2 * ((∑ l, x l * y l * z l) - x j * y j * z j) := by
  rcases (by revert j; decide : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [G3, Fin.sum_univ_six, ite_true, ite_false,
      zero_add, add_zero]
    ring

lemma g3_cubic (j : Fin 6) (v : aH) :
    G3 j v v v = 6 * (-(v j) ^ 3 + e1 v * (v j) ^ 2 - e2 v * v j + e3 v) := by
  rcases (by revert j; decide : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5) with
    rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp (config := { decide := true }) only [cJ, e1, e2, e3, Fin.sum_univ_six, ite_true, ite_false,
      zero_add, add_zero]
    ring

lemma g3_one (j : Fin 6) : G3 j (fun _ => 1) (fun _ => 1) (fun _ => 1) = 60 := by
  simp [cJ]
  norm_num

def block (φ : Fin 6 → Fin 3) : Submodule ℂ aH :=
  LinearMap.range (LinearMap.funLeft ℂ ℂ φ)

lemma mem_block {φ : Fin 6 → Fin 3} {v : aH} :
    v ∈ block φ ↔ ∀ i j, φ i = φ j → v i = v j := by
  classical
  constructor
  · rintro ⟨f, rfl⟩ i j h
    change f (φ i) = f (φ j)
    rw [h]
  · intro h
    refine ⟨fun c => if hex : ∃ i, φ i = c then v hex.choose else 0, ?_⟩
    funext i
    change (if hex : ∃ k, φ k = φ i then v hex.choose else 0) = v i
    have hex : ∃ k, φ k = φ i := ⟨i, rfl⟩
    simp only [hex, dite_true]
    exact h _ _ hex.choose_spec

lemma finrank_block (φ : Fin 6 → Fin 3) : Module.finrank ℂ (block φ) ≤ 3 := by
  show Module.finrank ℂ (LinearMap.range (LinearMap.funLeft ℂ ℂ φ)) ≤ 3
  have h := LinearMap.finrank_range_le (LinearMap.funLeft ℂ ℂ φ)
  rwa [Module.finrank_fin_fun] at h

lemma one_mem_block (φ : Fin 6 → Fin 3) : (1 : aH) ∈ block φ := by
  rw [mem_block]
  intro i j _
  rfl

section
variable {P : Type*} [AddCommGroup P] [Module ℂ P]

lemma vM (f : Fin 6 → P →ₗ[ℂ] ℂ) (o : ∀ x, (∀ i, f i x = 0) → x = 0)
    (t : ∀ x j, G3 j (f · x) (f · x) (f · x) = 0) : Module.finrank ℂ P ≤ 2 := by
  classical
  let F : P →ₗ[ℂ] aH := LinearMap.pi f
  have hinj : Function.Injective F := (injective_iff_map_eq_zero F).mpr fun x hx =>
    o x fun i => by simpa [F] using congrFun hx i
  let S := LinearMap.range F
  have hvar : ∀ v ∈ S, ∀ j, G3 j v v v = 0 := by
    intro v hv j
    obtain ⟨x, rfl⟩ := hv
    simp only [F, LinearMap.pi_apply]
    exact t x j
  have hone : (1 : aH) ∉ S := by
    intro h1
    have h0 := hvar (1 : aH) h1 0
    have hfun : G3 0 (1 : aH) (1 : aH) (1 : aH) =
        G3 0 (fun _ => 1) (fun _ => 1) (fun _ => 1) := rfl
    rw [hfun, g3_one] at h0
    norm_num at h0
  have hsub : ∀ v ∈ S, ∃ φ : Fin 6 → Fin 3, v ∈ block φ := by
    intro v hv
    let poly : Polynomial ℂ :=
      Polynomial.C 1 * Polynomial.X ^ 3 + Polynomial.C (-e1 v) * Polynomial.X ^ 2 +
        Polynomial.C (e2 v) * Polynomial.X + Polynomial.C (-e3 v)
    have hpoly : ∀ i, poly.eval (v i) = 0 := by
      intro i
      have hg := hvar v hv i
      rw [g3_cubic] at hg
      have hzero : -(v i) ^ 3 + e1 v * (v i) ^ 2 - e2 v * v i + e3 v = 0 := by
        apply mul_left_cancel₀ (show (6 : ℂ) ≠ 0 by norm_num)
        simpa using hg
      simp only [poly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      linear_combination -hzero
    have hdeg : poly.natDegree = 3 := Polynomial.natDegree_cubic (by norm_num : (1 : ℂ) ≠ 0)
    have hne : poly ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < poly.natDegree)
    have hroots : (Finset.univ.image v).card ≤ 3 := by
      have hmem : Finset.univ.image v ⊆ poly.roots.toFinset := by
        intro a ha
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha
        obtain ⟨i, rfl⟩ := ha
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne]
        exact hpoly i
      have h1 := Finset.card_le_card hmem
      have h2 : poly.roots.toFinset.card ≤ poly.roots.card := Multiset.toFinset_card_le _
      have h3 := Polynomial.card_roots' poly
      omega
    let s := Finset.univ.image v
    let α := {a : ℂ // a ∈ s}
    have hc : Fintype.card α ≤ 3 := by
      rw [Fintype.card_coe]
      simpa [s, α] using hroots
    let e := Fintype.equivFin α
    let φ : Fin 6 → Fin 3 := fun i => Fin.castLE hc (e ⟨v i, by simp [s]⟩)
    refine ⟨φ, ?_⟩
    rw [mem_block]
    intro i j hij
    have hinj := Fin.castLE_injective hc hij
    have := e.injective hinj
    simpa using congrArg Subtype.val this
  let p (φ : Fin 6 → Fin 3) : Submodule ℂ S := (block φ).comap S.subtype
  have hcover : (Set.iUnion fun φ : Fin 6 → Fin 3 => (p φ : Set S)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨φ, hφv⟩ := hsub x.1 x.2
    exact ⟨φ, by simpa [p] using hφv⟩
  obtain ⟨φ, hφ⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hcover
  have hleS : S ≤ block φ := by
    intro v hv
    have : (⟨v, hv⟩ : S) ∈ p φ := by
      rw [hφ]
      exact Submodule.mem_top
    simpa [p] using this
  have hrank : Module.finrank ℂ S ≤ 2 := by
    have hb := finrank_block φ
    by_cases h2 : Module.finrank ℂ (block φ) ≤ 2
    · exact (Submodule.finrank_mono hleS).trans h2
    · have heq : Module.finrank ℂ (block φ) = 3 := by omega
      have hlt : S < block φ := by
        apply lt_of_le_of_ne hleS
        intro e
        exact hone (e ▸ one_mem_block φ)
      have hlt' := Submodule.finrank_lt_finrank_of_lt hlt
      omega
  rw [← LinearMap.finrank_range_of_inj hinj]
  simpa [S] using hrank

end

end Av
end Ac

end

end PEqualNP.Outside.L_gct_195

