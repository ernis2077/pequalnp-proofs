import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1332

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_nil (w : List Bool) : wiresFrom [] w = w := rfl

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs₁ gs₂ : List Gate) (w : List Bool) :
    wiresFrom (gs₁ ++ gs₂) w = wiresFrom gs₂ (wiresFrom gs₁ w) := by
  induction gs₁ generalizing w with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, wiresFrom_cons, ih]

lemma wiresFrom_length (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    rw [wiresFrom_cons, ih]
    simp
    omega

lemma getD_snoc_lt {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  simp [List.getD, List.getElem?_append_left hi]

lemma getD_snoc_eq {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i = l.length) :
    (l ++ [x]).getD i d = x := by
  subst hi
  simp [List.getD]

lemma getD_snoc_ne {α : Type*} (l : List α) (x d : α) (i : ℕ) (hi : i ≠ l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  by_cases hlt : i < l.length
  · exact getD_snoc_lt l x d i hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma wiresFrom_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [wiresFrom_cons, ih _ (by simp; omega)]
    exact getD_snoc_lt _ _ _ _ hi

lemma wiresFrom_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (wiresFrom gs w).getD (w.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (wiresFrom (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simpa only [List.append_assoc, List.singleton_append] using h1.symm
  conv_lhs => rw [hsplit, wiresFrom_append, wiresFrom_append, wiresFrom_cons, wiresFrom_nil]
  have hlen : (wiresFrom (gs.take j) w).length = w.length + j := by
    rw [wiresFrom_length, List.length_take, Nat.min_eq_left (by omega)]
  rw [wiresFrom_getD_lt _ _ _ (by simp [hlen])]
  exact getD_snoc_eq _ _ _ _ hlen.symm

def OkGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

def NOkGate (g : Gate) : Prop :=
  OkGate g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : OkGate g) : NOkGate (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this
    exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this
    exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩
    · simp [normGate]
    · simp [normGate]

lemma wiresFrom_norm (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, wiresFrom_cons, wiresFrom_cons, normGate_eval, ih]

def statVal (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Bool ⊕ ℕ → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List (Bool ⊕ ℕ) → Option Gate × (Bool ⊕ ℕ)
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplifyGate (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    Option Gate × (Bool ⊕ ℕ) :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplifyGate_ok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, OkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp [OkGate]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp [OkGate]
  · simp at hg
  · simp at hg

lemma simplifyGate_nok (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) :
    ∀ g ∈ (simplifyGate op m ins).1, NOkGate g := by
  intro g hg
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨⟨Or.inl rfl, by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inl rfl), by simp⟩, by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; exact ⟨⟨Or.inr (Or.inr rfl), by simp⟩, by simp⟩
  · simp at hg
  · simp at hg

lemma simplifyGate_none_of_const (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplifyGate op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplifyGate, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplifyGate, simpNot]

lemma simplifyGate_and_false (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (hf : Sum.inl false ∈ ins) :
    simplifyGate GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at hf
  · cases a <;> simp_all [simplifyGate, simpAnd]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => cases c <;> simp_all [simplifyGate, simpAnd]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpAnd]
      | inr j => simp at hf
  · simp at hlen

lemma simplifyGate_or_true (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (hlen : ins.length ≤ 2) (ht : Sum.inl true ∈ ins) :
    simplifyGate GateOp.or m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · simp at ht
  · cases a <;> simp_all [simplifyGate, simpOr]
  · cases a with
    | inl c =>
      cases b with
      | inl d => cases c <;> cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => cases c <;> simp_all [simplifyGate, simpOr]
    | inr i =>
      cases b with
      | inl d => cases d <;> simp_all [simplifyGate, simpOr]
      | inr j => simp at ht
  · simp at hlen

lemma simplifyGate_not_const (m : ℕ) (c : Bool) :
    simplifyGate GateOp.not m [Sum.inl c] = (none, Sum.inl (!c)) := rfl

lemma simplifyGate_both_const (op : GateOp) (m : ℕ) (c d : Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∃ e : Bool, simplifyGate op m [Sum.inl c, Sum.inl d] = (none, Sum.inl e) := by
  rcases hop with rfl | rfl
  · exact ⟨c && d, rfl⟩
  · exact ⟨c || d, rfl⟩

lemma simplifyGate_sound (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List (Bool ⊕ ℕ)) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplifyGate op w.length ins).1.toList.length)
      (simplifyGate op w.length ins).2 ∧
    statVal (wiresFrom (simplifyGate op w.length ins).1.toList w)
      (simplifyGate op w.length ins).2 = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a with
      | inl c =>
        cases b with
        | inl d => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval]
        | inr j => cases c <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
      | inr i =>
        cases b with
        | inl d => cases d <;> simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
        | inr j => simp_all [simplifyGate, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplifyGate, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplifyGate, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

lemma simplifyGate_mem_inputs_of_some (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) (w : ℕ) (hw : w ∈ g.inputs) :
    Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; simp at hw; rcases hw with rfl | rfl <;> simp
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg
    subst hg; simp at hw; subst hw; simp
  · simp at hg
  · simp at hg

lemma simplifyGate_out_wire_mem (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (w : ℕ) (hw : (simplifyGate op m ins).2 = Sum.inr w) :
    w = m ∨ Sum.inr w ∈ ins := by
  cases op <;> simp only [simplifyGate] at hw
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hw
    · right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · split_ifs at hw <;> simp at hw; right; simp [hw]
    · left; exact hw.symm
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hw
    left; exact hw.symm
  · simp at hw
  · simp at hw

lemma simplifyGate_some_snd (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ))
    (g : Gate) (hg : (simplifyGate op m ins).1 = some g) :
    (simplifyGate op m ins).2 = Sum.inr m := by
  cases op <;> simp only [simplifyGate] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg ⊢
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg ⊢
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg ⊢
  · simp at hg
  · simp at hg

def elimStep (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  let r := simplifyGate g.op (m + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  (acc.1 ++ [r.2], acc.2 ++ r.1.toList)

def elimPass (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  gs.foldl (elimStep m) acc

lemma elimPass_nil (m : ℕ) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m [] acc = acc := rfl

lemma elimPass_cons (m : ℕ) (g : Gate) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (g :: gs) acc = elimPass m gs (elimStep m acc g) := rfl

lemma elimPass_append (m : ℕ) (gs₁ gs₂ : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimPass m (gs₁ ++ gs₂) acc = elimPass m gs₂ (elimPass m gs₁ acc) := by
  induction gs₁ generalizing acc with
  | nil => rfl
  | cons g gs ih => simp only [List.cons_append, elimPass_cons, ih]

lemma elimPass_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, ih]
    simp [elimStep]
    omega

lemma elimPass_getD_lt (m k : ℕ) (d : Bool ⊕ ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (hk : k < acc.1.length) :
    (elimPass m gs acc).1.getD k d = acc.1.getD k d := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    rw [elimPass_cons, ih _ (by simp [elimStep]; omega)]
    exact getD_snoc_lt _ _ _ _ hk

lemma toList_opt_len_le {α : Type*} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elimPass_ok (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (h : ∀ g ∈ acc.2, OkGate g) : ∀ g ∈ (elimPass m gs acc).2, OkGate g := by
  induction gs generalizing acc with
  | nil => exact h
  | cons g gs ih =>
    rw [elimPass_cons]
    apply ih
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplifyGate_ok _ _ _ g' (by simpa using h1)

lemma elimPass_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elimPass]
  | cons g gs ih =>
    rw [elimPass_cons, List.length_cons]
    have h1 := ih (elimStep m acc g)
    have h2 : (elimStep m acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    omega

def elimState (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) :
    List (Bool ⊕ ℕ) × List Gate :=
  elimPass m (gs.take j) acc

lemma elimState_zero (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc 0 = acc := rfl

lemma elimState_end (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    elimState m gs acc gs.length = elimPass m gs acc := by
  simp [elimState]

lemma elimState_succ (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    elimState m gs acc (j + 1) = elimStep m (elimState m gs acc j) gs[j] := by
  unfold elimState
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, elimPass_append,
    elimPass_cons, elimPass_nil]

lemma elimState_fst_len (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j ≤ gs.length) :
    (elimState m gs acc j).1.length = acc.1.length + j := by
  rw [elimState, elimPass_fst_len, List.length_take, Nat.min_eq_left hj]

lemma elimState_getD_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k i : ℕ) (d : Bool ⊕ ℕ) (hjk : j ≤ k) (hk : k ≤ gs.length) (hi : i < acc.1.length + j) :
    (elimState m gs acc k).1.getD i d = (elimState m gs acc j).1.getD i d := by
  have htake : gs.take k = gs.take j ++ (gs.drop j).take (k - j) := by
    have h1 := List.take_add (l := gs) (i := j) (j := k - j)
    rw [show j + (k - j) = k by omega] at h1
    exact h1
  rw [elimState, htake, elimPass_append]
  exact elimPass_getD_lt m i d _ _ (by rw [elimPass_fst_len, List.length_take, Nat.min_eq_left (by omega)]; exact hi)

lemma elimState_snd_mono (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j k : ℕ) (hjk : j ≤ k) :
    (elimState m gs acc j).2.length ≤ (elimState m gs acc k).2.length := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0; exact le_rfl
  | succ k ih =>
    by_cases h : j = k + 1
    · subst h; exact le_rfl
    · have h1 := ih (by omega)
      by_cases hk : k < gs.length
      · rw [elimState_succ m gs acc k hk]
        simp only [elimStep, List.length_append]
        omega
      · have htk : gs.take (k + 1) = gs.take k := by
          rw [List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
        change (elimState m gs acc j).2.length ≤ (elimPass m (gs.take (k + 1)) acc).2.length
        rw [htk]
        exact h1

lemma elimState_getD_at (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    (elimState m gs acc (j + 1)).1.getD (acc.1.length + j) (Sum.inl false) =
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).2 := by
  rw [elimState_succ m gs acc j hj]
  simp only [elimStep]
  exact getD_snoc_eq _ _ _ _ (elimState_fst_len m gs acc j (by omega)).symm

def elimDropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : Finset ℕ :=
  (Finset.range gs.length).filter (fun j =>
    if hj : j < gs.length then
      (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
        (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
    else false)

lemma elimPass_card_dropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (elimPass m gs acc).2.length + (elimDropped m gs acc).card = acc.2.length + gs.length := by
  suffices ∀ k ≤ gs.length,
      (elimState m gs acc k).2.length +
        ((Finset.range k).filter (fun j =>
          if hj : j < gs.length then
            (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
              (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
          else false)).card = acc.2.length + k by
    simpa [elimState_end, elimDropped] using this gs.length le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    simp [elimState_zero]
  | succ k ih =>
    intro hk
    have hklt : k < gs.length := by omega
    have hih := ih (by omega)
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnot : k ∉ (Finset.range k).filter (fun j =>
        if hj : j < gs.length then
          (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
            (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1.isNone
        else false) := by
      simp
    rw [elimState_succ m gs acc k hklt]
    simp only [elimStep, List.length_append, hklt, ↓reduceDIte]
    cases hopt : (simplifyGate gs[k].op (m + (elimState m gs acc k).2.length)
        (gs[k].inputs.map fun i => (elimState m gs acc k).1.getD i (Sum.inl false))).1 with
    | none =>
      simp only [Option.toList_none, List.length_nil, Option.isNone_none, ↓reduceIte,
        Finset.card_insert_of_notMem hnot]
      omega
    | some g =>
      simp only [Option.toList_some, List.length_singleton, Option.isNone_some, Bool.false_eq_true,
        ↓reduceIte]
      omega

lemma mem_elimDropped_of_const (m : ℕ) (gs : List Gate)
    (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) (hj : j < gs.length)
    (hnok : NOkGate gs[j]) (i : ℕ) (hi : i ∈ gs[j].inputs)
    (hc : ∃ c, (elimState m gs acc j).1.getD i (Sum.inl false) = Sum.inl c) :
    j ∈ elimDropped m gs acc := by
  rw [elimDropped, Finset.mem_filter, Finset.mem_range]
  refine ⟨hj, ?_⟩
  simp only [hj, ↓reduceDIte]
  obtain ⟨c, hc⟩ := hc
  have hnone : (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
      (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1 = none := by
    apply simplifyGate_none_of_const
    · exact hnok.1.1
    · simpa using hnok.1.2
    · intro h; simpa using hnok.2 h
    · exact ⟨c, List.mem_map.2 ⟨i, hi, hc⟩⟩
  rw [hnone]
  rfl

lemma elimPass_len_lt (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (hex : ∃ g ∈ gs, k ∈ g.inputs) :
    (elimPass m gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  obtain ⟨g, hg, hkg⟩ := hex
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  have hmem : j ∈ elimDropped m gs acc := by
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkg
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcard : 1 ≤ (elimDropped m gs acc).card := Finset.one_le_card.2 ⟨j, hmem⟩
  have htot := elimPass_card_dropped m gs acc
  omega

lemma elimPass_len_two (m k : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (hk : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c)
    (htwo : 2 ≤ (gs.filter (fun g => decide (k ∈ g.inputs))).length) :
    (elimPass m gs acc).2.length + 2 ≤ acc.2.length + gs.length := by
  have hsub : (Finset.range gs.length).filter (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)
      ⊆ elimDropped m gs acc := by
    intro j hj'
    rw [Finset.mem_filter, Finset.mem_range] at hj'
    obtain ⟨hj, hkin⟩ := hj'
    simp only [hj, ↓reduceDIte] at hkin
    apply mem_elimDropped_of_const m gs acc j hj (hok _ (List.getElem_mem hj)) k hkin
    obtain ⟨c, hc⟩ := hc
    exact ⟨c, by rw [elimState_getD_mono m gs acc 0 j k _ (Nat.zero_le _) (by omega) (by omega), elimState_zero]; exact hc⟩
  have hcnt : ((Finset.range gs.length).filter
      (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card =
      (gs.filter (fun g => decide (k ∈ g.inputs))).length := by
    clear hsub htwo hc hk hok acc m
    induction gs with
    | nil => simp
    | cons g gs ih =>
      rw [List.filter_cons]
      have hbij : ((Finset.range (g :: gs).length).filter
          (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false)).card =
          (if k ∈ g.inputs then 1 else 0) +
          ((Finset.range gs.length).filter
            (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).card := by
        have hsplit : (Finset.range (g :: gs).length).filter
            (fun j => if hj : j < (g :: gs).length then k ∈ (g :: gs)[j].inputs else false) =
            (if k ∈ g.inputs then {0} else ∅) ∪
            ((Finset.range gs.length).filter
              (fun j => if hj : j < gs.length then k ∈ gs[j].inputs else false)).image (· + 1) := by
          ext j
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image,
            List.length_cons]
          cases j with
          | zero =>
            by_cases hk0 : k ∈ g.inputs <;> simp [hk0]
          | succ j =>
            by_cases hk0 : k ∈ g.inputs <;> by_cases hlt : j < gs.length <;> simp [hk0, hlt]
        rw [hsplit, Finset.card_union_of_disjoint]
        · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega)]
          split_ifs <;> simp
        · rw [Finset.disjoint_left]
          intro x hx1 hx2
          simp only [Finset.mem_image] at hx2
          obtain ⟨y, _, rfl⟩ := hx2
          split_ifs at hx1 <;> simp at hx1
      rw [hbij, ih]
      by_cases hkg : k ∈ g.inputs <;> simp [hkg] <;> omega
  have hle := Finset.card_le_card hsub
  have htot := elimPass_card_dropped m gs acc
  omega

def ElimInv (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) : Prop :=
  w_in.length = m ∧
  acc.1.length = w_old.length ∧
  ∀ i : ℕ,
    statValid (m + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 w_in) (acc.1.getD i (Sum.inl false)) = w_old.getD i false

lemma elimInv_step (m : ℕ) (w_in w_old : List Bool)
    (acc : List (Bool ⊕ ℕ) × List Gate) (g : Gate) (hok : OkGate g)
    (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (w_old ++ [g.op.eval (g.inputs.map fun i => w_old.getD i false)])
      (elimStep m acc g) := by
  obtain ⟨hwin, hlen, hi⟩ := hinv
  set w_new := wiresFrom acc.2 w_in with hw_new
  have hw_len : w_new.length = m + acc.2.length := by
    rw [hw_new, wiresFrom_length, hwin]
  set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
  have hins_len : ins.length ≤ 2 := by simp [hins]; exact hok.2
  have hins_val : ∀ s ∈ ins, statValid w_new.length s := by
    intro s hs
    obtain ⟨idx, _, rfl⟩ := List.mem_map.1 hs
    rw [hw_len]
    exact (hi idx).1
  have hsound := simplifyGate_sound g.op hok.1 w_new ins hins_len hins_val
  rw [hw_len] at hsound
  refine ⟨hwin, by simp [elimStep, hlen], ?_⟩
  intro i
  simp only [elimStep]
  by_cases hieq : i = acc.1.length
  · rw [getD_snoc_eq _ _ _ _ hieq, getD_snoc_eq _ _ _ _ (by omega)]
    refine ⟨?_, ?_⟩
    · rw [List.length_append, ← Nat.add_assoc]
      exact hsound.1
    · rw [wiresFrom_append, ← hw_new, hsound.2]
      congr 1
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro idx _
      exact (hi idx).2
  · rw [getD_snoc_ne _ _ _ _ hieq, getD_snoc_ne _ _ _ _ (by omega)]
    have ⟨hv, hval⟩ := hi i
    refine ⟨?_, ?_⟩
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c => trivial
      | inr j =>
        rw [hst] at hv
        simp only [statValid, List.length_append] at hv ⊢
        omega
    · cases hst : acc.1.getD i (Sum.inl false) with
      | inl c =>
        rw [hst] at hval
        exact hval
      | inr j =>
        rw [hst] at hv hval
        simp only [statValid] at hv
        simp only [statVal] at hval ⊢
        rw [wiresFrom_append, ← hw_new, wiresFrom_getD_lt _ _ _ (by omega)]
        exact hval

lemma elimInv_pass (m : ℕ) (w_in : List Bool) (gs : List Gate)
    (w_old : List Bool) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, OkGate g) (hinv : ElimInv m w_in w_old acc) :
    ElimInv m w_in (wiresFrom gs w_old) (elimPass m gs acc) := by
  induction gs generalizing w_old acc with
  | nil => exact hinv
  | cons g gs ih =>
    rw [wiresFrom_cons, elimPass_cons]
    exact ih _ _ (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (elimInv_step m w_in w_old acc g (hok g List.mem_cons_self) hinv)

lemma ofFn_getD_lt {α : Type*} {m : ℕ} (f : Fin m → α) (d : α) (i : ℕ) (hi : i < m) :
    (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp; exact hi), List.getElem_ofFn]

def isTwoGate (g : Gate) : Bool :=
  match g.op with
  | GateOp.and | GateOp.or => decide (g.inputs.length = 2)
  | _ => false

def constTrueGate : Gate := { op := GateOp.and, inputs := [] }

lemma isTwoGate_iff (g : Gate) :
    isTwoGate g = true ↔ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  simp only [isTwoGate]
  cases h : g.op <;> simp [h, decide_eq_true_eq]

lemma ok_of_stmt (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    OkGate g := ⟨by rcases h.1 with h | h | h <;> simp [h], h.2⟩

lemma stmt_of_ok (g : Gate) (h : OkGate g) :
    (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2 :=
  ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h.1, h.2⟩

def fixStats (n : ℕ) (p : Fin n) : List (Bool ⊕ ℕ) :=
  List.ofFn fun i : Fin n => if i = p then Sum.inl false else Sum.inr i.val

lemma fixStats_length (n : ℕ) (p : Fin n) : (fixStats n p).length = n := by simp [fixStats]

lemma fixStats_at (n : ℕ) (p : Fin n) :
    (fixStats n p).getD p.val (Sum.inl false) = Sum.inl false := by
  unfold fixStats
  rw [ofFn_getD_lt (f := fun i : Fin n => if i = p then Sum.inl false else Sum.inr i.val)
    (Sum.inl false) p.val p.isLt]
  simp

lemma fixStats_other (n : ℕ) (p : Fin n) (i : ℕ) (hi : i < n)
    (hne : (⟨i, hi⟩ : Fin n) ≠ p) :
    (fixStats n p).getD i (Sum.inl false) = Sum.inr i := by
  unfold fixStats
  rw [ofFn_getD_lt (f := fun j : Fin n => if j = p then Sum.inl false else Sum.inr j.val)
    (Sum.inl false) i hi]
  simp [hne]

lemma elimInv_fix (n : ℕ) (p : Fin n) (x : Fin n → Bool) :
    ElimInv n (List.ofFn x) (List.ofFn (Function.update x p false)) (fixStats n p, []) := by
  refine ⟨by simp, by simp [fixStats], ?_⟩
  intro i
  by_cases hin : i < n
  · by_cases hep : (⟨i, hin⟩ : Fin n) = p
    · have heq : i = p.val := congrArg Fin.val hep
      subst heq
      rw [fixStats_at]
      refine ⟨trivial, ?_⟩
      simp only [statVal, wiresFrom]
      rw [ofFn_getD_lt (f := Function.update x p false) false p.val p.isLt]
      simp [Function.update_self]
    · rw [fixStats_other n p i hin hep]
      refine ⟨by simp [statValid, hin], ?_⟩
      change (List.ofFn x).getD i false =
        (List.ofFn (Function.update x p false)).getD i false
      rw [ofFn_getD_lt (f := x) false i hin,
        ofFn_getD_lt (f := Function.update x p false) false i hin]
      simp [Function.update_of_ne hep]
  · rw [List.getD_eq_default _ _ (by rw [fixStats_length]; omega),
        List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma simplifyGate_emit_two (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (g : Gate)
    (hg : (simplifyGate op m ins).1 = some g) (ht : isTwoGate g = true) :
    (op = GateOp.and ∨ op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    all_goals (subst hg; try simp [isTwoGate] at ht; try exact ⟨Or.inl rfl, rfl⟩)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    all_goals (subst hg; try simp [isTwoGate] at ht; try exact ⟨Or.inr rfl, rfl⟩)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    all_goals (subst hg; simp [isTwoGate] at ht)
  · simp at hg
  · simp at hg

lemma simplifyGate_emit_not (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (g : Gate)
    (hg : (simplifyGate op m ins).1 = some g) (hn : g.op = GateOp.not) :
    op = GateOp.not := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (try subst hg) <;> try simp at hn
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (try subst hg) <;> try simp at hn
  · rfl
  · simp at hg
  · simp at hg

lemma update_false_eq (n : ℕ) (p : Fin n) (x : Fin n → Bool) (v : Fin n) :
    Function.update x p false v = true ↔ v ≠ p ∧ x v = true := by
  by_cases h : v = p
  · subst h; simp
  · simp [Function.update_of_ne h, h]

lemma eval_update_eq_sum (n m : ℕ) (S : Fin m → Finset (Fin n)) (p : Fin n)
    (gates : List Gate) (out : Fin m → ℕ)
    (hev : ∀ (o : Fin m) (x : Fin n → Bool),
      Circuit.eval ⟨gates, out o⟩ (List.ofFn x) = decide (∃ v ∈ S o, x v = true))
    (o : Fin m) (x2 : Fin n → Bool) :
    Circuit.eval ⟨gates, out o⟩ (List.ofFn (Function.update x2 p false)) =
      decide (∃ v2 ∈ S o, v2 ≠ p ∧ x2 v2 = true) := by
  rw [hev]
  congr 1
  exact propext ⟨fun ⟨v, hvS, hv⟩ => ⟨v, hvS, (update_false_eq n p x2 v).1 hv⟩,
    fun ⟨v, hvS, hvne, hv⟩ => ⟨v, hvS, (update_false_eq n p x2 v).2 ⟨hvne, hv⟩⟩⟩

def outOfStat (n gl0Len : ℕ) : (Bool ⊕ ℕ) → ℕ
  | Sum.inl false => n + gl0Len + 1
  | Sum.inl true => n + gl0Len
  | Sum.inr j => j

lemma outOfStat_val (n : ℕ) (gl0 : List Gate) (y : List Bool) (hy : y.length = n)
    (s : Bool ⊕ ℕ) (hv : statValid (n + gl0.length) s) :
    statVal (wiresFrom (gl0 ++ [constTrueGate]) y) s =
      (wiresFrom (gl0 ++ [constTrueGate]) y).getD (outOfStat n gl0.length s) false := by
  cases s with
  | inl c =>
    cases c
    · simp only [outOfStat, statVal]
      have hlen : (wiresFrom (gl0 ++ [constTrueGate]) y).length = n + gl0.length + 1 := by
        rw [wiresFrom_length, hy, List.length_append, List.length_singleton]; omega
      rw [List.getD_eq_default _ _ (by omega)]
    · simp only [outOfStat, statVal]
      rw [wiresFrom_append]
      have hw : (wiresFrom gl0 y).length = n + gl0.length := by rw [wiresFrom_length, hy]
      change true = (wiresFrom gl0 y ++ [true]).getD (n + gl0.length) false
      rw [← hw]; simp
  | inr j =>
    change (wiresFrom (gl0 ++ [constTrueGate]) y).getD j false =
      (wiresFrom (gl0 ++ [constTrueGate]) y).getD j false
    rfl

lemma elimPass_prefix_le (m : ℕ) (gs : List Gate) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      acc.2.length ≤ (elimPass m gs acc).2.length := by
  induction gs with
  | nil => intro acc; simp [elimPass]
  | cons g gs ih =>
    intro acc
    rw [elimPass_cons]
    have h : acc.2.length ≤ (elimStep m acc g).2.length := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    exact h.trans (ih _)

lemma elimPass_getElem?_prefix (m : ℕ) (gs : List Gate) :
    ∀ (acc : List (Bool ⊕ ℕ) × List Gate) (i : ℕ) (hi : i < acc.2.length),
      (elimPass m gs acc).2[i]? = acc.2[i]? := by
  induction gs with
  | nil =>
    intro acc i hi
    rfl
  | cons g gs ih =>
    intro acc i hi
    rw [elimPass_cons]
    have hacc : i < (elimStep m acc g).2.length := by
      simp only [elimStep, List.length_append]
      have := toList_opt_len_le (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have hget : (elimStep m acc g).2[i]? = acc.2[i]? := by
      simp only [elimStep]
      exact List.getElem?_append_left hi
    rw [ih (elimStep m acc g) i hacc, hget]

def emitOpt (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) (j : ℕ) :
    Option Gate :=
  if hj : j < gs.length then
    (simplifyGate gs[j].op (m + (elimState m gs acc j).2.length)
      (gs[j].inputs.map fun i => (elimState m gs acc j).1.getD i (Sum.inl false))).1
  else
    none

lemma emitOpt_zero (m : ℕ) (g : Gate) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    emitOpt m (g :: gs) acc 0 =
      (simplifyGate g.op (m + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 := by
  simp [emitOpt, elimState_zero]

lemma emitOpt_succ (m : ℕ) (g : Gate) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (k : ℕ) (hk : k < gs.length) :
    emitOpt m (g :: gs) acc (k + 1) = emitOpt m gs (elimStep m acc g) k := by
  have hk' : k + 1 < (g :: gs).length := by simp; omega
  have hstate : elimState m (g :: gs) acc (k + 1) = elimState m gs (elimStep m acc g) k := by
    change elimPass m ((g :: gs).take (k + 1)) acc =
      elimPass m (gs.take k) (elimStep m acc g)
    have htake : (g :: gs).take (k + 1) = g :: gs.take k := by
      simp [List.take_cons]
    rw [htake, elimPass_cons]
  simp only [emitOpt, hk, hk', ↓reduceDIte, hstate, List.getElem_cons_succ]

lemma emit_filterMap (m : ℕ) (gs : List Gate) :
    ∀ acc : List (Bool ⊕ ℕ) × List Gate,
      (elimPass m gs acc).2 = acc.2 ++ (List.range gs.length).filterMap (emitOpt m gs acc) := by
  induction gs with
  | nil =>
    intro acc
    simp [elimPass]
  | cons g gs ih =>
    intro acc
    set r := simplifyGate g.op (m + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
    set acc' := elimStep m acc g with hacc'
    have hacc'_def : acc' = (acc.1 ++ [r.2], acc.2 ++ r.1.toList) := by
      simp [acc', elimStep, hr]
    have hzero : emitOpt m (g :: gs) acc 0 = r.1 := by
      simpa [hr] using emitOpt_zero m g gs acc
    have htail :
        ((List.range gs.length).map (· + 1)).filterMap (emitOpt m (g :: gs) acc) =
          (List.range gs.length).filterMap (emitOpt m gs acc') := by
      rw [List.filterMap_map]
      apply List.filterMap_congr
      intro k hk
      simpa [acc'] using emitOpt_succ m g gs acc k (List.mem_range.1 hk)
    rw [elimPass_cons, ← hacc']
    simp only [List.length_cons]
    have hrange : List.range (gs.length + 1) = 0 :: (List.range gs.length).map (· + 1) :=
      List.range_succ_eq_map
    rw [hrange, List.filterMap_cons, hzero, htail, ih acc']
    cases hopt : r.1 with
    | none =>
      simp [hacc'_def, hopt, Option.toList_none]
    | some g0 =>
      simp [hacc'_def, hopt, Option.toList_some, List.append_assoc]


lemma emitOpt_none_iff (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (j : ℕ) (hj : j < gs.length) :
    emitOpt m gs acc j = none ↔ j ∈ elimDropped m gs acc := by
  simp only [emitOpt, elimDropped, hj, ↓reduceDIte, Finset.mem_filter, Finset.mem_range,
    true_and]
  constructor <;> intro h <;> simpa using h

def survivingIdxs (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) : List ℕ :=
  (List.range gs.length).filter (fun j => (emitOpt m gs acc j).isSome)

lemma survivingIdxs_length (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate) :
    (survivingIdxs m gs acc).length =
      ((List.range gs.length).filterMap (emitOpt m gs acc)).length := by
  simp only [survivingIdxs]
  rw [List.length_filterMap_eq_countP (f := emitOpt m gs acc), List.countP_eq_length_filter]

lemma survivingIdxs_get_lt (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (t : ℕ) (ht : t < (survivingIdxs m gs acc).length) :
    (survivingIdxs m gs acc)[t] < gs.length := by
  have hmem : (survivingIdxs m gs acc)[t] ∈ List.range gs.length :=
    List.mem_of_mem_filter (List.getElem_mem ht)
  exact List.mem_range.1 hmem

lemma filter_filterMap_length {α β : Type*} (f : α → Option β) (l : List α) :
    (l.filterMap f).length = (l.filter (fun a => (f a).isSome)).length := by
  rw [List.length_filterMap_eq_countP, List.countP_eq_length_filter]

lemma filter_filterMap_getElem? {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (t : ℕ),
      (l.filterMap f)[t]? =
        Option.bind ((l.filter (fun a => (f a).isSome))[t]?) f := by
  intro l
  induction l with
  | nil =>
    intro t
    simp
  | cons x xs ih =>
    intro t
    simp only [List.filter_cons, List.filterMap_cons]
    by_cases hx : (f x).isSome
    · simp only [hx, ↓reduceIte]
      cases t with
      | zero =>
        cases hopt : f x with
        | none => simp [hopt] at hx
        | some b => simp [hopt]
      | succ t =>
        cases hopt : f x with
        | none => simp [hopt] at hx
        | some b => simpa [hopt] using ih t
    · simp only [hx, Bool.false_eq_true, ↓reduceIte]
      cases hopt : f x with
      | none => simpa [hopt] using ih t
      | some b => simp [hopt] at hx

lemma survivingIdxs_emit (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (t : ℕ) (ht : t < (survivingIdxs m gs acc).length) :
    emitOpt m gs acc ((survivingIdxs m gs acc)[t]) =
      some (((List.range gs.length).filterMap (emitOpt m gs acc))[t]'(by
        rw [← survivingIdxs_length]; exact ht)) := by
  have ht' : t < ((List.range gs.length).filterMap (emitOpt m gs acc)).length := by
    rw [← survivingIdxs_length]; exact ht
  have h := filter_filterMap_getElem? (emitOpt m gs acc) (List.range gs.length) t
  have hs : ((List.range gs.length).filter (fun j => (emitOpt m gs acc j).isSome))[t]? =
      some (survivingIdxs m gs acc)[t] := by
    simpa [survivingIdxs] using List.getElem?_eq_getElem (by simpa [survivingIdxs] using ht)
  rw [hs, Option.bind_some] at h
  have hfm := List.getElem?_eq_getElem ht'
  rw [hfm] at h
  exact h.symm

lemma survivingIdxs_strict (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (i j : ℕ) (hij : i < j) (hj : j < (survivingIdxs m gs acc).length) :
    (survivingIdxs m gs acc)[i] < (survivingIdxs m gs acc)[j] := by
  have hi : i < (survivingIdxs m gs acc).length := by omega
  have hpw : List.Pairwise (· < ·) (survivingIdxs m gs acc) := by
    simp only [survivingIdxs]
    exact List.Pairwise.filter _ (@List.pairwise_lt_range gs.length)
  have := List.Pairwise.rel_get_of_lt hpw (a := ⟨i, hi⟩) (b := ⟨j, hj⟩) hij
  simpa [List.get_eq_getElem] using this

lemma simplifyGate_emit_two' (op : GateOp) (m : ℕ) (ins : List (Bool ⊕ ℕ)) (g : Gate)
    (hg : (simplifyGate op m ins).1 = some g) (ht : isTwoGate g = true) :
    (op = GateOp.and ∨ op = GateOp.or) ∧ ins.length = 2 ∧ g.inputs.length = 2 := by
  cases op <;> simp only [simplifyGate] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    all_goals (try subst hg; try simp [isTwoGate] at ht; try exact ⟨Or.inl rfl, rfl, rfl⟩)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    all_goals (try subst hg; try simp [isTwoGate] at ht; try exact ⟨Or.inr rfl, rfl, rfl⟩)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    all_goals (try subst hg; try simp [isTwoGate] at ht)
  · simp at hg
  · simp at hg

lemma reader_in_dropped (m : ℕ) (gs : List Gate) (acc : List (Bool ⊕ ℕ) × List Gate)
    (hok : ∀ g ∈ gs, NOkGate g) (q : ℕ) (hq : q < gs.length)
    (k : ℕ) (hk : k ∈ (gs[q]).inputs) (hklt : k < acc.1.length)
    (hc : ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) :
    q ∈ elimDropped m gs acc :=
  mem_elimDropped_of_const m gs acc q hq (hok _ (List.getElem_mem hq)) k hk
    (by
      obtain ⟨c, hc⟩ := hc
      refine ⟨c, ?_⟩
      rw [elimState_getD_mono m gs acc 0 q k _ (Nat.zero_le _) (Nat.le_of_lt hq)
        (by omega), elimState_zero]
      exact hc)


lemma two_wire_card_bound (m : ℕ) (gs : List Gate) (st : List (Bool ⊕ ℕ))
    (hok : ∀ g ∈ gs, NOkGate g) (I : Finset (Fin gs.length))
    (hI : ∀ q : Fin gs.length,
      ((gs.get q).op = GateOp.and ∨ (gs.get q).op = GateOp.or) ∧
        (gs.get q).inputs.length = 2 → q ∈ I)
    (a b : Fin gs.length) (hab : a ≠ b)
    (haD : a.val ∈ elimDropped m gs (st, []))
    (hbD : b.val ∈ elimDropped m gs (st, []))
    (haTwo : isTwoGate (gs.get a) = true)
    (hbTwo : isTwoGate (gs.get b) = true) :
    let gl0 := (elimPass m gs (st, [])).2
    (Finset.univ.filter (fun j : Fin gl0.length => isTwoGate (gl0.get j) = true)).card + 2 ≤
      I.card := by
  intro gl0
  have hfm := emit_filterMap m gs (st, [])
  simp only [List.nil_append] at hfm
  have hlen : gl0.length = (survivingIdxs m gs (st, [])).length := by
    simp only [gl0, hfm]
    exact (survivingIdxs_length m gs (st, [])).symm
  set J0 := Finset.univ.filter (fun j : Fin gl0.length => isTwoGate (gl0.get j) = true)
  have haI : a ∈ I := hI a ((isTwoGate_iff _).1 haTwo)
  have hbI : b ∈ I := hI b ((isTwoGate_iff _).1 hbTwo)
  set Surv := I.filter (fun q : Fin gs.length => q.val ∉ elimDropped m gs (st, []))
  have hcardI : Surv.card + 2 ≤ I.card := by
    have hne : a ∉ Surv := by simp [Surv, haD]
    have hne' : b ∉ Surv := by simp [Surv, hbD]
    have hdisj : Disjoint Surv ({a, b} : Finset (Fin gs.length)) := by
      rw [Finset.disjoint_right]
      intro x hx hxS
      have hx' : x = a ∨ x = b :=
        (Finset.mem_insert.1 hx).elim Or.inl fun h => Or.inr (Finset.mem_singleton.1 h)
      rcases hx' with rfl | rfl
      · exact hne hxS
      · exact hne' hxS
    have hsub : ({a, b} : Finset (Fin gs.length)) ⊆ I := by
      intro x hx
      have hx' : x = a ∨ x = b :=
        (Finset.mem_insert.1 hx).elim Or.inl fun h => Or.inr (Finset.mem_singleton.1 h)
      rcases hx' with rfl | rfl
      · exact haI
      · exact hbI
    have hunion : Surv ∪ {a, b} ⊆ I := by
      intro x hx
      cases Finset.mem_union.1 hx with
      | inl hx => exact (Finset.mem_filter.1 hx).1
      | inr hx => exact hsub hx
    have hcard_u : (Surv ∪ {a, b}).card = Surv.card + ({a, b} : Finset _).card :=
      Finset.card_union_of_disjoint hdisj
    have habc : ({a, b} : Finset _).card = 2 := Finset.card_pair hab
    have := Finset.card_le_card hunion
    omega
  have hinj : ∀ j ∈ J0, ∃ q ∈ Surv,
      q.val = (survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact j.isLt) := by
    intro j hj
    have htwo : isTwoGate (gl0.get j) = true := (Finset.mem_filter.1 hj).2
    have hjlt : j.val < gl0.length := j.isLt
    have hsrc_lt := survivingIdxs_get_lt m gs (st, []) j.val (by rw [← hlen]; exact hjlt)
    have hemit := survivingIdxs_emit m gs (st, []) j.val (by rw [← hlen]; exact hjlt)
    have hgl : gl0[j.val] =
        ((List.range gs.length).filterMap (emitOpt m gs (st, [])))[j.val]'(by
          rw [← survivingIdxs_length, ← hlen]; exact hjlt) := by
      simp [gl0, hfm]
    have hsome : emitOpt m gs (st, [])
        ((survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact hjlt)) =
        some (gl0[j.val]) := by
      simpa [hgl] using hemit
    have hnd : (survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact hjlt) ∉
        elimDropped m gs (st, []) := by
      intro h
      have := (emitOpt_none_iff m gs (st, []) _ hsrc_lt).2 h
      simp [this] at hsome
    set src := (survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact hjlt)
    have hopg := simplifyGate_emit_two' (gs[src]).op
      (m + (elimState m gs (st, []) src).2.length)
      ((gs[src]).inputs.map fun i =>
        (elimState m gs (st, []) src).1.getD i (Sum.inl false))
      (gl0[j.val]) (by simpa [emitOpt, hsrc_lt, src] using hsome)
      (by simpa [List.get_eq_getElem] using htwo)
    have htwo_g : isTwoGate (gs[src]) = true := by
      obtain ⟨hop, hlen_ins, _⟩ := hopg
      have hlen' : (gs[src]).inputs.length = 2 := by simpa using hlen_ins
      rcases hop with hop | hop <;> simp [isTwoGate, hop, hlen']
    refine ⟨⟨src, hsrc_lt⟩, ?_, rfl⟩
    simp only [Surv, Finset.mem_filter]
    refine ⟨hI _ ((isTwoGate_iff _).1 (by simpa [List.get_eq_getElem] using htwo_g)), hnd⟩
  have hcardJ : J0.card ≤ Surv.card := by
    refine Finset.card_le_card_of_injOn
      (fun j => ⟨(survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact j.isLt),
        survivingIdxs_get_lt m gs (st, []) j.val (by rw [← hlen]; exact j.isLt)⟩)
      ?_ ?_
    · intro j hj
      obtain ⟨q, hqS, heq⟩ := hinj j hj
      have : (⟨(survivingIdxs m gs (st, []))[j.val]'(by rw [← hlen]; exact j.isLt),
          survivingIdxs_get_lt m gs (st, []) j.val (by rw [← hlen]; exact j.isLt)⟩ :
          Fin gs.length) = q := Fin.ext heq.symm
      simpa [this] using hqS
    · intro j1 _hj1 j2 _hj2 heq
      apply Fin.ext
      have hi1 : j1.val < (survivingIdxs m gs (st, [])).length := by rw [← hlen]; exact j1.isLt
      have hi2 : j2.val < (survivingIdxs m gs (st, [])).length := by rw [← hlen]; exact j2.isLt
      have hs : (survivingIdxs m gs (st, []))[j1.val] = (survivingIdxs m gs (st, []))[j2.val] :=
        Fin.val_eq_of_eq heq
      rcases lt_trichotomy j1.val j2.val with hlt | he | hgt
      · have := survivingIdxs_strict m gs (st, []) j1.val j2.val hlt hi2
        omega
      · exact he
      · have := survivingIdxs_strict m gs (st, []) j2.val j1.val hgt hi1
        omega
  omega

lemma normGate_op_not (g : Gate) (h : (normGate g).op = GateOp.not) : g.op = GateOp.not := by
  cases hop : g.op <;> simp [normGate, hop] at h ⊢

lemma normGate_two (g : Gate)
    (h : ((normGate g).op = GateOp.and ∨ (normGate g).op = GateOp.or) ∧
      (normGate g).inputs.length = 2) :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 := by
  cases hop : g.op <;> simp [normGate, hop] at h ⊢
  · exact h
  · exact h

lemma wiresFrom_norm_eq (gs : List Gate) (w : List Bool) :
    wiresFrom (gs.map normGate) w = wiresFrom gs w := wiresFrom_norm gs w


lemma gl_two_wire_lt (gl0 : List Gate) (j : Fin (gl0 ++ [constTrueGate]).length)
    (htwo : isTwoGate ((gl0 ++ [constTrueGate]).get j) = true) :
    j.val < gl0.length := by
  by_contra hge
  have hlen : (gl0 ++ [constTrueGate]).length = gl0.length + 1 := by simp
  have heq : j.val = gl0.length := by omega
  have hget : (gl0 ++ [constTrueGate]).get j = constTrueGate := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right (by omega)]
    simp [heq]
  rw [hget] at htwo
  simp [constTrueGate, isTwoGate] at htwo

lemma J_card_eq_J0 (gl0 : List Gate) :
    let gl := gl0 ++ [constTrueGate]
    (Finset.univ.filter (fun j : Fin gl.length => isTwoGate (gl.get j) = true)).card =
      (Finset.univ.filter (fun j : Fin gl0.length => isTwoGate (gl0.get j) = true)).card := by
  intro gl
  set J := Finset.univ.filter (fun j : Fin gl.length => isTwoGate (gl.get j) = true)
  set J0 := Finset.univ.filter (fun j : Fin gl0.length => isTwoGate (gl0.get j) = true)
  have hle : gl0.length ≤ gl.length := by
    simp only [gl, List.length_append, List.length_singleton]; omega
  let f : Fin gl0.length ↪ Fin gl.length := Fin.castLEEmb hle
  have himg : J = J0.map f := by
    ext j
    constructor
    · intro hj
      have htwo : isTwoGate (gl.get j) = true := (Finset.mem_filter.1 hj).2
      have hjlt := gl_two_wire_lt gl0 j htwo
      refine Finset.mem_map.2 ⟨⟨j.val, hjlt⟩, ?_, Fin.ext rfl⟩
      simp only [J0, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [List.get_eq_getElem, gl, List.getElem_append_left hjlt] using htwo
    · intro hj
      obtain ⟨j0, hj0, rfl⟩ := Finset.mem_map.1 hj
      have htwo : isTwoGate (gl0.get j0) = true := (Finset.mem_filter.1 hj0).2
      simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [List.get_eq_getElem, gl, List.getElem_append_left j0.isLt, f] using htwo
  rw [himg, Finset.card_map]

end PEqualNP.Outside.L_meta_1332

open PEqualNP.Outside.L_meta_1332
open PEqualNP.CircuitLowerBounds

set_option maxHeartbeats 800000 in
theorem PEqualNP.Outside.L_meta_1332 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)),
    (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) →
    ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ),
    (∀ g ∈ gates,
      (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
          g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
        g.inputs.length ≤ 2) →
    (∀ (o : Fin m) (x : Fin n → Bool),
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out o⟩ (List.ofFn x) =
        decide (∃ v ∈ S o, x v = true)) →
    ∀ p : Fin n, (∃ i0 : Fin m, p ∈ S i0 ∧ ∃ v0 ∈ S i0, v0 ≠ p) →
    ∀ a b : Fin gates.length, a ≠ b →
    ((gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (gates.get a).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (gates.get a).inputs.length = 2 → p.val ∈ (gates.get a).inputs →
    ((gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
        (gates.get b).op = PEqualNP.CircuitLowerBounds.GateOp.or) →
    (gates.get b).inputs.length = 2 → p.val ∈ (gates.get b).inputs →
    ∀ (t : ℕ) (ι : Fin t → Fin gates.length),
    (∀ q : Fin gates.length,
      (gates.get q).op = PEqualNP.CircuitLowerBounds.GateOp.not →
        ∃ r : Fin t, ι r = q) →
    ∀ I : Finset (Fin gates.length),
    (∀ q2 : Fin gates.length,
      ((gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            (gates.get q2).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          (gates.get q2).inputs.length = 2 →
        q2 ∈ I) →
    ∃ (gl : List PEqualNP.CircuitLowerBounds.Gate) (ol : Fin m → ℕ)
      (κ : Fin t → Fin gl.length) (J : Finset (Fin gl.length)),
      (∀ h ∈ gl,
          (h.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
              h.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
              h.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
            h.inputs.length ≤ 2) ∧
        (∀ q3 : Fin gl.length,
          (gl.get q3).op = PEqualNP.CircuitLowerBounds.GateOp.not →
            ∃ r2 : Fin t, κ r2 = q3) ∧
        (∀ q4 : Fin gl.length,
          ((gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
                (gl.get q4).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
              (gl.get q4).inputs.length = 2 →
            q4 ∈ J) ∧
        J.card + 2 ≤ I.card ∧
        ∀ (o2 : Fin m) (x2 : Fin n → Bool),
          PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gl, ol o2⟩ (List.ofFn x2) =
            decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) := by
  intro n m S _hdisj gates out hok hev p _hp a b hab haOp haLen haIn hbOp hbLen hbIn t ι hι I hI
  classical
  set gs : List Gate := gates.map normGate with hgs
  have hlen_gs : gs.length = gates.length := by simp [gs]
  have hokN : ∀ g ∈ gs, NOkGate g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok_of_stmt g0 (hok g0 hg0))
  have hokG : ∀ g ∈ gs, OkGate g := fun g hg => (hokN g hg).1
  set st := fixStats n p
  set pass := elimPass n gs (st, [])
  set gl0 := pass.2
  set gl : List Gate := gl0 ++ [constTrueGate]
  set ol : Fin m → ℕ := fun o2 =>
    outOfStat n gl0.length (pass.1.getD (out o2) (Sum.inl false))
  set aG : Fin gs.length := ⟨a.val, by omega⟩
  set bG : Fin gs.length := ⟨b.val, by omega⟩
  have habG : aG ≠ bG := by
    intro h
    exact hab (Fin.ext (by simpa [aG, bG] using congrArg Fin.val h))
  have hnorm_andor (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
      normGate g = g := by
    cases hop with
    | inl h => simp [normGate, h]
    | inr h => simp [normGate, h]
  have hget_a : gs.get aG = gates.get a := by
    simp only [gs, aG, List.get_eq_getElem, List.getElem_map]
    exact hnorm_andor _ haOp
  have hget_b : gs.get bG = gates.get b := by
    simp only [gs, bG, List.get_eq_getElem, List.getElem_map]
    exact hnorm_andor _ hbOp
  have haTwo : isTwoGate (gs.get aG) = true := by
    rw [hget_a, isTwoGate_iff]; exact ⟨haOp, haLen⟩
  have hbTwo : isTwoGate (gs.get bG) = true := by
    rw [hget_b, isTwoGate_iff]; exact ⟨hbOp, hbLen⟩
  have haInG : p.val ∈ (gs.get aG).inputs := by rw [hget_a]; exact haIn
  have hbInG : p.val ∈ (gs.get bG).inputs := by rw [hget_b]; exact hbIn
  have hp_lt : p.val < st.length := by
    rw [show st.length = n from fixStats_length n p]
    exact p.isLt
  have haD : aG.val ∈ elimDropped n gs (st, []) :=
    reader_in_dropped n gs (st, []) hokN aG.val aG.isLt p.val haInG hp_lt
      ⟨false, fixStats_at n p⟩
  have hbD : bG.val ∈ elimDropped n gs (st, []) :=
    reader_in_dropped n gs (st, []) hokN bG.val bG.isLt p.val hbInG hp_lt
      ⟨false, fixStats_at n p⟩
  let emb : Fin gates.length ↪ Fin gs.length :=
    Fin.castLEEmb (by omega)
  set IG : Finset (Fin gs.length) := I.map emb
  have hIG : ∀ q : Fin gs.length,
      ((gs.get q).op = GateOp.and ∨ (gs.get q).op = GateOp.or) ∧
        (gs.get q).inputs.length = 2 → q ∈ IG := by
    intro q hq
    set qG : Fin gates.length := ⟨q.val, by omega⟩
    have hmap : gs.get q = normGate (gates.get qG) := by
      simp [gs, qG, List.get_eq_getElem, List.getElem_map]
    have hq' :
        ((normGate (gates.get qG)).op = GateOp.and ∨
          (normGate (gates.get qG)).op = GateOp.or) ∧
          (normGate (gates.get qG)).inputs.length = 2 := by
      rw [← hmap]; simpa [List.get_eq_getElem] using hq
    refine Finset.mem_map.2 ⟨qG, hI qG (normGate_two _ hq'), ?_⟩
    apply Fin.ext
    simp [emb, Fin.castLEEmb, Fin.castLE, qG]
  have hcard0 := two_wire_card_bound n gs st hokN IG hIG aG bG habG haD hbD haTwo hbTwo
  set J0 := Finset.univ.filter (fun j : Fin gl0.length => isTwoGate (gl0.get j) = true)
  have hJ0 : J0.card + 2 ≤ IG.card := by simpa [J0, gl0, pass, st] using hcard0
  have hIGc : IG.card = I.card := by simp [IG, Finset.card_map]
  set J : Finset (Fin gl.length) :=
    Finset.univ.filter (fun j : Fin gl.length => isTwoGate (gl.get j) = true)
  have hJeq : J.card = J0.card := by
    simpa [J, J0, gl] using J_card_eq_J0 gl0
  have hJle : J.card + 2 ≤ I.card := by omega
  set surv := survivingIdxs n gs (st, [])
  have hsurv_len : gl0.length = surv.length := by
    have hfm := emit_filterMap n gs (st, [])
    simp only [List.nil_append] at hfm
    simp [gl0, pass, st, hfm, surv, survivingIdxs_length]
  have hgl_len : gl.length = gl0.length + 1 := by simp [gl]
  set κ : Fin t → Fin gl.length := fun r =>
    if h : ∃ j : Fin surv.length, surv[j.val] = (ι r).val then
      ⟨(Classical.choose h).val, by have := (Classical.choose h).isLt; omega⟩
    else
      ⟨gl0.length, by omega⟩
  refine ⟨gl, ol, κ, J, ?_, ?_, ?_, hJle, ?_⟩
  · intro h hh
    have hh' : h ∈ gl0 ++ [constTrueGate] := by simpa [gl] using hh
    cases List.mem_append.1 hh' with
    | inl hh0 =>
      exact stmt_of_ok h (elimPass_ok n gs (st, []) (by intro g hg; cases hg) h hh0)
    | inr hh0 =>
      have : h = constTrueGate := List.mem_singleton.1 hh0
      subst this
      exact ⟨Or.inl rfl, by simp [constTrueGate]⟩
  · intro q3 hq3
    have hq3lt : q3.val < gl0.length := by
      by_contra hge
      have heq : q3.val = gl0.length := by
        have := q3.isLt; omega
      have hget : gl.get q3 = constTrueGate := by
        simp only [List.get_eq_getElem, gl]
        rw [List.getElem_append_right (by omega)]
        simp [heq]
      rw [hget] at hq3
      simp [constTrueGate] at hq3
    have hget0 : gl.get q3 = gl0[q3.val]'(hq3lt) := by
      simp only [List.get_eq_getElem, gl, List.getElem_append_left hq3lt]
    rw [hget0] at hq3
    have hsrc_lt := survivingIdxs_get_lt n gs (st, []) q3.val (by rw [← hsurv_len]; exact hq3lt)
    have hemit := survivingIdxs_emit n gs (st, []) q3.val (by rw [← hsurv_len]; exact hq3lt)
    have hfm := emit_filterMap n gs (st, [])
    simp only [List.nil_append] at hfm
    have hgl0eq : gl0 = (List.range gs.length).filterMap (emitOpt n gs (st, [])) := by
      simpa [gl0, pass, st] using hfm
    set src := surv[q3.val]'(by rw [← hsurv_len]; exact hq3lt)
    have hsome : emitOpt n gs (st, []) src = some (gl0[q3.val]'(hq3lt)) := by
      simpa [surv, src, hgl0eq] using hemit
    have hop_src : (gs[src]).op = GateOp.not :=
      simplifyGate_emit_not (gs[src]).op
        (n + (elimState n gs (st, []) src).2.length)
        ((gs[src]).inputs.map fun i =>
          (elimState n gs (st, []) src).1.getD i (Sum.inl false))
        (gl0[q3.val]'(hq3lt)) (by simpa [emitOpt, hsrc_lt, src] using hsome)
        (by simpa [List.get_eq_getElem] using hq3)
    have hop_gates : (gates.get ⟨src, by simpa [hlen_gs] using hsrc_lt⟩).op = GateOp.not := by
      have hmap : gs[src] = normGate (gates.get ⟨src, by simpa [hlen_gs] using hsrc_lt⟩) := by
        simp [gs, List.getElem_map]
      exact normGate_op_not _ (by simpa [hmap] using hop_src)
    obtain ⟨r, hr⟩ := hι ⟨src, by simpa [hlen_gs] using hsrc_lt⟩ hop_gates
    refine ⟨r, ?_⟩
    change κ r = q3
    simp only [κ]
    have hex : ∃ j : Fin surv.length, surv[j.val] = (ι r).val :=
      ⟨⟨q3.val, by rw [← hsurv_len]; exact hq3lt⟩, by simp [hr, src]⟩
    simp only [hex, ↓reduceDIte]
    apply Fin.ext
    have hch := Classical.choose_spec hex
    have hjlt : (Classical.choose hex).val < surv.length := (Classical.choose hex).isLt
    have hs : surv[(Classical.choose hex).val] =
        surv[q3.val]'(by rw [← hsurv_len]; exact hq3lt) := by
      rw [hch]; simp [hr, src]
    rcases lt_trichotomy (Classical.choose hex).val q3.val with hlt | he | hgt
    · have := survivingIdxs_strict n gs (st, []) (Classical.choose hex).val q3.val hlt
        (by rw [← hsurv_len]; exact hq3lt)
      simp only [surv] at this hs; omega
    · exact he
    · have := survivingIdxs_strict n gs (st, []) q3.val (Classical.choose hex).val hgt hjlt
      simp only [surv] at this hs; omega
  · intro q4 hq4
    simp only [J, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (isTwoGate_iff _).2 hq4
  · intro o2 x2
    have htarget :
        Circuit.eval ⟨gates, out o2⟩ (List.ofFn (Function.update x2 p false)) =
          decide (∃ v2 ∈ S o2, v2 ≠ p ∧ x2 v2 = true) :=
      eval_update_eq_sum n m S p gates out hev o2 x2
    rw [← htarget]
    change (wiresFrom gl (List.ofFn x2)).getD (ol o2) false =
      (wiresFrom gates (List.ofFn (Function.update x2 p false))).getD (out o2) false
    have hnorm :
        wiresFrom gs (List.ofFn (Function.update x2 p false)) =
          wiresFrom gates (List.ofFn (Function.update x2 p false)) :=
      wiresFrom_norm_eq gates _
    rw [← hnorm]
    have hinv0 := elimInv_fix n p x2
    have hinv := elimInv_pass n (List.ofFn x2) gs
      (List.ofFn (Function.update x2 p false)) (st, []) hokG (by simpa [st] using hinv0)
    obtain ⟨_, _, hi⟩ := hinv
    have hstat := hi (out o2)
    have hv := hstat.1
    have hval := hstat.2
    have happend := outOfStat_val n gl0 (List.ofFn x2) (by simp)
      (pass.1.getD (out o2) (Sum.inl false)) (by simpa [pass, st, gl0] using hv)
    have hstat_same :
        statVal (wiresFrom (gl0 ++ [constTrueGate]) (List.ofFn x2))
            (pass.1.getD (out o2) (Sum.inl false)) =
          statVal (wiresFrom gl0 (List.ofFn x2))
            (pass.1.getD (out o2) (Sum.inl false)) := by
      cases hst : pass.1.getD (out o2) (Sum.inl false) with
      | inl c => simp [statVal, hst]
      | inr j =>
        simp only [statVal, hst]
        have hj : j < n + gl0.length := by
          have hv0 := hv
          simp only [pass, st, gl0] at hv0
          rw [hst] at hv0
          simpa [statValid, gl0, pass, st] using hv0
        have hlen0 : (wiresFrom gl0 (List.ofFn x2)).length = n + gl0.length := by
          rw [wiresFrom_length]; simp
        rw [wiresFrom_append, wiresFrom_getD_lt _ _ _ (by omega)]
    simp only [gl, ol]
    calc
      (wiresFrom (gl0 ++ [constTrueGate]) (List.ofFn x2)).getD
            (outOfStat n gl0.length (pass.1.getD (out o2) (Sum.inl false))) false =
          statVal (wiresFrom (gl0 ++ [constTrueGate]) (List.ofFn x2))
            (pass.1.getD (out o2) (Sum.inl false)) := happend.symm
      _ = statVal (wiresFrom gl0 (List.ofFn x2))
            (pass.1.getD (out o2) (Sum.inl false)) := hstat_same
      _ = (wiresFrom gs (List.ofFn (Function.update x2 p false))).getD (out o2) false := by
          simpa [pass, st, gl0] using hval
