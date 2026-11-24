import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1417_aux

-- The live-wire compression argument follows the project proof of L-meta-703.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 256 pairs of assignments.
abbrev W := BitVec 512
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 256 := ((x >>> 256) ^^^ x).setWidth 256
def cuts (ws : List W) : BitVec 256 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 256) ++ (0 : BitVec 256)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 256) (w : W) : Prop :=
  w.getLsbD (256+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 256) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 256+i.val < 512 := by omega
  have hi' : i.val < 512 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 256) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 256)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

theorem optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

theorem search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 512 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 512)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 512) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 512) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 512) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#512)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search n ins = false)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 512) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  have found := search_complete ht n ins nd (lift low run)
  exact Bool.noConfusion (rejection.symm.trans found)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 512, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : search (m-2) ins = false)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩
def ins_e8808080 : List W := [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]
theorem nd_e8808080 : ins_e8808080.Nodup := by decide +kernel
theorem spec_e8808080 : ∀ j : Fin 512, Nat.testBit 0xe8808080 (∑ i : Fin 5, if (ins_e8808080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p0 : dispatch 2 (optimized 5) (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2) (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004) ([0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p1 : dispatch 2 (optimized 5) (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2) (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d) ([0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p2 : dispatch 2 (optimized 5) (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2) (0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51) ([0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p3 : dispatch 2 (optimized 5) (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2) (0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5) ([0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p4 : dispatch 2 (optimized 5) (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004) (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p5 : dispatch 2 (optimized 5) (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004) (0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p6 : dispatch 2 (optimized 5) (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004) (0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p7 : dispatch 2 (optimized 5) (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d) (0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p8 : dispatch 2 (optimized 5) (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d) (0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808080_p9 : dispatch 2 (optimized 5) (0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51) (0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5) ([0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d]) = false := by decide +kernel

theorem pairs_e8808080 : pairs ins_e8808080 = [(0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, [0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, [0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, [0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5, [0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]), (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]), (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5]), (0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51]), (0xd2cdb61ae3cdafb5ffff4d1a3f7f6fddffbeefdfeef97dbffe9dafff2fd24b9d50f6f144737404690381f60097fe2e24573225931b80fc6555b272062c00ea51, 0x933df6b9ffcdadbdbfd76f9335dd4fedf9afedb0af5ffaffdbdbef3f6f7b69bf2627060c4f97860ed038298a02cb7129c045767d25985a330b3509e86d62d7a5, [0xfffafbff7c7ffb7f5fefffffdaefff76f77fb37ffffedfeabdfffffffcbdfeff66485e032db613421400d2d1035548dd25d091c570150432c28e829c9a0d4ac2, 0x7fffdfe7ffbfd6ffeefbfffffff3beffefff5fefdfa7e77f7f7efce3dfffffeec8559aaad0634ab24b00060e98029b2fdc61c4222e1520488cb42535c7919004, 0xedf77dff9ffe7fcffb7efefffffef5fb7ff3fffff3ffbfffe7f757dcfbeffff71a03e41590883cc4b198f1a2a809d1d038a619281f428c082f0af32b30c2213d])] := by decide +kernel

theorem opt_e8808080 : optimized 6 2 ins_e8808080 = false := by
  unfold optimized
  have hs : (ins_e8808080 == [goal] || ins_e8808080 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_e8808080]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_e8808080_p0, dispatch_e8808080_p1, dispatch_e8808080_p2, dispatch_e8808080_p3, dispatch_e8808080_p4, dispatch_e8808080_p5, dispatch_e8808080_p6, dispatch_e8808080_p7, dispatch_e8808080_p8, dispatch_e8808080_p9]

set_option maxRecDepth 32000 in
theorem reject_e8808080 : search 6 ins_e8808080 = false := by
  have hopt := opt_e8808080
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 6+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_e8808080 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (6 + 1 - ins_e8808080.length) = 2 := by decide
      simpa [hx] using hopt

def gates_e8808080 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [5, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [0, 2]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 9]⟩]
theorem upper_e8808080 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8808080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8808080, 12, ?_, rfl, ?_⟩
  · simp [gates_e8808080]
  · decide +kernel

def ins_a8888880 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]
theorem nd_a8888880 : ins_a8888880.Nodup := by decide +kernel
theorem spec_a8888880 : ∀ j : Fin 512, Nat.testBit 0xa8888880 (∑ i : Fin 5, if (ins_a8888880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p0 : dispatch 1 (optimized 4) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119) ([0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p1 : dispatch 1 (optimized 4) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46) (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p2 : dispatch 1 (optimized 4) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46) (0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p3 : dispatch 1 (optimized 4) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p4 : dispatch 1 (optimized 4) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119) (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p5 : dispatch 1 (optimized 4) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119) (0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p6 : dispatch 1 (optimized 4) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p7 : dispatch 1 (optimized 4) (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c) (0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p8 : dispatch 1 (optimized 4) (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a8888880_p9 : dispatch 1 (optimized 4) (0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c]) = false := by decide +kernel

theorem pairs_a8888880 : pairs ins_a8888880 = [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, [0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]), (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]), (0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a]), (0x7f73376dad6e837beed396eebdfc55c6debba794157d4f8eff37f9eb2f81b332d421825c6548e08d3f1e60c8db2a1f3434fb82197499ac6f1150135b5a71bc2a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb40572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffdb0b63194525b581588aca20c90ab03280b25683ac542c0c8a1004c4365763119, 0x82dcf27f61f765bdf8dcd9779a7c57bd98745fc757e3fea4d1f96cbddbafafa68e142b4282e0a9462d9169a5e5ce71f54c2fd16e47bb9d69788b34016501232c])] := by decide +kernel

theorem opt_a8888880 : optimized 5 1 ins_a8888880 = false := by
  unfold optimized
  have hs : (ins_a8888880 == [goal] || ins_a8888880 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_a8888880]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_a8888880_p0, dispatch_a8888880_p1, dispatch_a8888880_p2, dispatch_a8888880_p3, dispatch_a8888880_p4, dispatch_a8888880_p5, dispatch_a8888880_p6, dispatch_a8888880_p7, dispatch_a8888880_p8, dispatch_a8888880_p9]

set_option maxRecDepth 32000 in
theorem reject_a8888880 : search 5 ins_a8888880 = false := by
  have hopt := opt_a8888880
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 5+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_a8888880 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (5 + 1 - ins_a8888880.length) = 1 := by decide
      simpa [hx] using hopt

def gates_a8888880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [3, 4]⟩, ⟨.and, [1, 5]⟩, ⟨.or, [2, 6]⟩, ⟨.and, [3, 4]⟩, ⟨.and, [0, 7]⟩, ⟨.or, [8, 1]⟩, ⟨.and, [10, 9]⟩]
theorem upper_a8888880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 7 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8888880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8888880, 11, ?_, rfl, ?_⟩
  · simp [gates_a8888880]
  · decide +kernel

def ins_a888a080 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e098028bc1015e04700c4d30945d09af10084450a002022cc3821a008848a46, 0xffefd533edbde7ee3e0fcfffa7f857ff5efffed7579effaafedff57ffeaf9fb4b4b63194525b58158dace28c91ab13380b25e83ac542c0e8a1004c4365763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a142b4282e0a94628912925e4ce61e54c2f516e47bb9d49788b34016501232c, 0x32713eed3366997beff2b466f9fffd86ff31a7acbd754eddf1376be90fd1f36bf021825c7558f08d3a1ea048da2b0f2c35fb02197499ac4f9150135b5a75bc2a, 0xff679d81ff2cbf66172bafeb67eba847678fbcbbb99e277bee87974ff65c52f940572637c145607a5a691b75c8fee2843ac17b794faa8a9618f412a382231970]
theorem nd_a888a080 : ins_a888a080.Nodup := by decide +kernel
theorem spec_a888a080 : ∀ j : Fin 512, Nat.testBit 0xa888a080 (∑ i : Fin 5, if (ins_a888a080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a888a080 : search 3 ins_a888a080 = false := by decide +kernel
def gates_a888a080 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [4, 2]⟩, ⟨.and, [0, 5]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [7, 1]⟩, ⟨.and, [8, 6]⟩]
theorem upper_a888a080 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 5 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa888a080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a888a080, 9, ?_, rfl, ?_⟩
  · simp [gates_a888a080]
  · decide +kernel

def ins_e8808880 : List W := [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]
theorem nd_e8808880 : ins_e8808880.Nodup := by decide +kernel
theorem spec_e8808880 : ∀ j : Fin 512, Nat.testBit 0xe8808880 (∑ i : Fin 5, if (ins_e8808880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p0 : dispatch 2 (optimized 5) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119) ([0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p1 : dispatch 2 (optimized 5) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c) ([0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p2 : dispatch 2 (optimized 5) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a) ([0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p3 : dispatch 2 (optimized 5) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336) ([0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p4 : dispatch 2 (optimized 5) (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119) (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p5 : dispatch 2 (optimized 5) (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119) (0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p6 : dispatch 2 (optimized 5) (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p7 : dispatch 2 (optimized 5) (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c) (0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p8 : dispatch 2 (optimized 5) (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8808880_p9 : dispatch 2 (optimized 5) (0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a) (0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c]) = false := by decide +kernel

theorem pairs_e8808880 : pairs ins_e8808880 = [(0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, [0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, [0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, [0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336, [0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]), (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]), (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336]), (0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a]), (0x7f733fedbf6e9b7beff3b6eefdfffdc6ffbba7bcbd7d4fdfff37fbeb2fd1f37bd020827ce508e0ed701e20195264cfa404fa02503a992c4d196013fa5a71b46a, 0xb275becd7366bd77d7fabd637befa807e705bdabb9f7267de1a70fcdd75c72eb6a5ea61f7d15759a10699f2640b1220ecbc07f3401aa2a94d4cc33028aa79336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff77fedffe7fffedfdfffbffc57ffdeffffd757ffffaefffffdffffafbfb6b4b63194521b581585ace28c11a113380b24e832814240e8a1004c4265763119, 0x82dcfaff73f77dbdf9fcf977da7fffbdb9745fefffe3fef5d1f96ebddbffefef8a152b4282a0a946229129656cc461e57c2e516703bb1d4b789b340065012b2c])] := by decide +kernel

theorem opt_e8808880 : optimized 6 2 ins_e8808880 = false := by
  unfold optimized
  have hs : (ins_e8808880 == [goal] || ins_e8808880 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_e8808880]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_e8808880_p0, dispatch_e8808880_p1, dispatch_e8808880_p2, dispatch_e8808880_p3, dispatch_e8808880_p4, dispatch_e8808880_p5, dispatch_e8808880_p6, dispatch_e8808880_p7, dispatch_e8808880_p8, dispatch_e8808880_p9]

set_option maxRecDepth 32000 in
theorem reject_e8808880 : search 6 ins_e8808880 = false := by
  have hopt := opt_e8808880
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 6+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_e8808880 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (6 + 1 - ins_e8808880.length) = 2 := by decide
      simpa [hx] using hopt

def gates_e8808880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [1, 0]⟩, ⟨.and, [5, 3]⟩, ⟨.and, [4, 3]⟩, ⟨.or, [1, 0]⟩, ⟨.or, [7, 5]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [11, 9]⟩]
theorem upper_e8808880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8808880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8808880, 12, ?_, rfl, ?_⟩
  · simp [gates_e8808880]
  · decide +kernel

def ins_e888a000 : List W := [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]
theorem nd_e888a000 : ins_e888a000.Nodup := by decide +kernel
theorem spec_e888a000 : ∀ j : Fin 512, Nat.testBit 0xe888a000 (∑ i : Fin 5, if (ins_e888a000.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p0 : dispatch 0 (optimized 3) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119) ([0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p1 : dispatch 0 (optimized 3) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c) ([0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p2 : dispatch 0 (optimized 3) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a) ([0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p3 : dispatch 0 (optimized 3) (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46) (0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336) ([0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p4 : dispatch 0 (optimized 3) (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119) (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p5 : dispatch 0 (optimized 3) (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119) (0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p6 : dispatch 0 (optimized 3) (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119) (0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p7 : dispatch 0 (optimized 3) (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c) (0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p8 : dispatch 0 (optimized 3) (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c) (0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e888a000_p9 : dispatch 0 (optimized 3) (0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a) (0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336) ([0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c]) = false := by decide +kernel

theorem pairs_e888a000 : pairs ins_e888a000 = [(0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, [0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, [0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, [0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336, [0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]), (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]), (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336]), (0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a]), (0x4fda7bffbfff5bb9e9f5f2fedc7ffffcb9fa47fcff69dfd7df79fabb2bf3ef7fd420827c6508e0ad751e609853209f3404fa821038992c6d116013fa5a71b46a, 0xfffff75fedffe7f7d6dfdffb3fec027fc6cffdd353ffb72eefef9ddff72e3eb64a5ea61f6d05659a10691f2640b02206cac07f3401aa2a9454cc33028aa39336, [0xffefddb3ffbdffee3f2fefffe7fbffff7ffffeffff9efffbfedff77ffeffdffd2e098028bc5015e04f00c4d3894fd09af101844d4e00a022cc3821a108848a46, 0xb2fdf67f61f7e5fffededd77bbfc57bfde75ffc757f7feacf1ff6dfddfafbfa6b4b63194d21b585585ace28d11e553b80b24e872834240e8a9004c4265763119, 0xcf56bbedff6e3f3df9f9bbefde7ffdc5b9be1fbfbdeb6ff7dfb1feaffbdde3fbaa152b4212b0b9062291a9646c81216d7d2e512701bb1d4bf09b340065052b2c])] := by decide +kernel

theorem opt_e888a000 : optimized 4 0 ins_e888a000 = false := by
  unfold optimized
  have hs : (ins_e888a000 == [goal] || ins_e888a000 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_e888a000]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_e888a000_p0, dispatch_e888a000_p1, dispatch_e888a000_p2, dispatch_e888a000_p3, dispatch_e888a000_p4, dispatch_e888a000_p5, dispatch_e888a000_p6, dispatch_e888a000_p7, dispatch_e888a000_p8, dispatch_e888a000_p9]

set_option maxRecDepth 32000 in
theorem reject_e888a000 : search 4 ins_e888a000 = false := by
  have hopt := opt_e888a000
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 4+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_e888a000 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (4 + 1 - ins_e888a000.length) = 0 := by decide
      simpa [hx] using hopt

def gates_e888a000 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [1, 4]⟩, ⟨.and, [2, 3]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [6, 0]⟩, ⟨.and, [5, 8]⟩, ⟨.or, [9, 7]⟩]
theorem upper_e888a000 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe888a000 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e888a000, 10, ?_, rfl, ?_⟩
  · simp [gates_e888a000]
  · decide +kernel

def ins_a8888888 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef108608c751a5e812b0010808521013450cf839a250f9411111825a08175e10b1, 0xd08ea7733c2a7fa3a98d3f16bccca9affce3038afdf8477d591c1148e7af725efe84e50e87d058420f1635216520eb444dbbbf236a5b58063b5f883085f27b16, 0x97c06f8335ff565bbdceaf5f1d87cdcf46568ac9a49187811a2f379af363e9ba70c78d74e002e719ddd0963e5e17e5556926b95a61b728f20cc1ead15948e600, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1c6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]
theorem nd_a8888888 : ins_a8888888.Nodup := by decide +kernel
theorem spec_a8888888 : ∀ j : Fin 512, Nat.testBit 0xa8888888 (∑ i : Fin 5, if (ins_a8888888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a8888888 : search 2 ins_a8888888 = false := by decide +kernel
def gates_a8888888 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [4, 2]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩]
theorem upper_a8888888 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8888888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8888888, 8, ?_, rfl, ?_⟩
  · simp [gates_a8888888]
  · decide +kernel

def ins_a888a880 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]
theorem nd_a888a880 : ins_a888a880.Nodup := by decide +kernel
theorem spec_a888a880 : ∀ j : Fin 512, Nat.testBit 0xa888a880 (∑ i : Fin 5, if (ins_a888a880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p0 : dispatch 0 (optimized 3) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42) (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1) ([0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p1 : dispatch 0 (optimized 3) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916) ([0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p2 : dispatch 0 (optimized 3) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400) ([0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p3 : dispatch 0 (optimized 3) (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42) (0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb) ([0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p4 : dispatch 0 (optimized 3) (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p5 : dispatch 0 (optimized 3) (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p6 : dispatch 0 (optimized 3) (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1) (0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p7 : dispatch 0 (optimized 3) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p8 : dispatch 0 (optimized 3) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916) (0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_a888a880_p9 : dispatch 0 (optimized 3) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400) (0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb) ([0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916]) = false := by decide +kernel

theorem pairs_a888a880 : pairs ins_a888a880 = [(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, [0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, [0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, [0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb, [0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]), (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]), (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb]), (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400]), (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xbb7114dccb32a1145a334af4ceb5f370d199f43d1a27bd7fecdaccbf5df48f0d6c6e1c26f3b580e893382b9a0a43292634057674478dfa318389287ce7635deb, [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xf7deecf039f77ff91edbdbdfaffff5f2ffbfbdff796df7ff5bbb3ffb75ffdfee108689c751a5e812b8010c085210d3450cf8b9a250fb411311825a08175e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe84640e87d058420716312165202b444dbb3f236a5958043b5f883085f25916])] := by decide +kernel

theorem opt_a888a880 : optimized 4 0 ins_a888a880 = false := by
  unfold optimized
  have hs : (ins_a888a880 == [goal] || ins_a888a880 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_a888a880]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_a888a880_p0, dispatch_a888a880_p1, dispatch_a888a880_p2, dispatch_a888a880_p3, dispatch_a888a880_p4, dispatch_a888a880_p5, dispatch_a888a880_p6, dispatch_a888a880_p7, dispatch_a888a880_p8, dispatch_a888a880_p9]

set_option maxRecDepth 32000 in
theorem reject_a888a880 : search 4 ins_a888a880 = false := by
  have hopt := opt_a888a880
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 4+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_a888a880 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (4 + 1 - ins_a888a880.length) = 0 := by decide
      simpa [hx] using hopt

def gates_a888a880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [3, 2]⟩, ⟨.or, [2, 3]⟩, ⟨.or, [4, 6]⟩, ⟨.and, [7, 0]⟩, ⟨.or, [1, 5]⟩, ⟨.and, [8, 9]⟩]
theorem upper_a888a880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa888a880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a888a880, 10, ?_, rfl, ?_⟩
  · simp [gates_a888a880]
  · decide +kernel

def ins_a8a8a800 : List W := [0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8238b3102e4a004108ac26168022c0202205c4118d0204ca240804e368a12b42, 0xd7ceecf039f77ff91ccb9b5fadcfe5e2feb789cb7969c7fd5b3b37da75efdbee108689c753a5e852b8012c085210d3450cf9bda250fb4113118a5a28177e3bb3, 0xb8b1375ffe2af707ebbd6fb6deb4bbbfd5cb76bcbeb63f7ffcdcd92defb7661ffe84e50e85d058020f1615216520eb444dbabb236a5b58063b57881085d27214, 0xfbffb4acf332deb55aba5bf66efdd3d26d3af5bf634fff03bdcaddff797bdd4b70c70c74e002e719d5d0923e5e1725556926395a61b528f00cc1ead15948c400, 0xf41ecf730cef29eaaf55fe9dbffebd3dfbed3f7eddfc75ff4bbd2a69c7bc36fc6c6e1c26f1b580a893380b9a0a43292634047274478dfa318381285ce74354e9]
theorem nd_a8a8a800 : ins_a8a8a800.Nodup := by decide +kernel
theorem spec_a8a8a800 : ∀ j : Fin 512, Nat.testBit 0xa8a8a800 (∑ i : Fin 5, if (ins_a8a8a800.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 80000000 in
theorem reject_a8a8a800 : search 2 ins_a8a8a800 = false := by decide +kernel
def gates_a8a8a800 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [5, 6]⟩, ⟨.and, [0, 7]⟩]
theorem upper_a8a8a800 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xa8a8a800 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_a8a8a800, 8, ?_, rfl, ?_⟩
  · simp [gates_a8a8a800]
  · decide +kernel

def ins_e880a880 : List W := [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]
theorem nd_e880a880 : ins_e880a880.Nodup := by decide +kernel
theorem spec_e880a880 : ∀ j : Fin 512, Nat.testBit 0xe880a880 (∑ i : Fin 5, if (ins_e880a880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p0 : dispatch 2 (optimized 5) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3) ([0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p1 : dispatch 2 (optimized 5) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014) ([0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p2 : dispatch 2 (optimized 5) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440) ([0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p3 : dispatch 2 (optimized 5) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9) ([0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p4 : dispatch 2 (optimized 5) (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3) (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p5 : dispatch 2 (optimized 5) (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3) (0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p6 : dispatch 2 (optimized 5) (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3) (0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p7 : dispatch 2 (optimized 5) (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014) (0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p8 : dispatch 2 (optimized 5) (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014) (0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e880a880_p9 : dispatch 2 (optimized 5) (0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440) (0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014]) = false := by decide +kernel

theorem pairs_e880a880 : pairs ins_e880a880 = [(0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, [0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, [0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, [0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9, [0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]), (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]), (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9]), (0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440]), (0xbff17f8ff7ffd65ffffeefff5fb7dfdf475efefda697bf83beefffbffb73edbb70eb1c70c002e719d5f8902c5e1524714922494a24b428f00cc1e2913809c440, 0xb35007d30d3a2112bb176ed49eb5f97dd1d9b63d9cb5b57f489e0cbbd7f4af1cee52af32ddff80a99b940d8c8a61e802160082658a8efefba781249f8e8276a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd7ceeff33dff7ffbbdcfbf5fbdcfedeffef78bcbfdf9c7fd5b3f37daf7effbfe108289c353a5e852b8012c085210d2410cf98da210fa4113118a5228163e3bb3, 0xf8bfb77ffe2affa7ebbd7fb6fefcbbbffdeb77befffe7f7ffddcd96defbf765ffe80640aa5d058020716133365222a406dbe0b332b5858043b578050c4925014])] := by decide +kernel

theorem opt_e880a880 : optimized 6 2 ins_e880a880 = false := by
  unfold optimized
  have hs : (ins_e880a880 == [goal] || ins_e880a880 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_e880a880]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_e880a880_p0, dispatch_e880a880_p1, dispatch_e880a880_p2, dispatch_e880a880_p3, dispatch_e880a880_p4, dispatch_e880a880_p5, dispatch_e880a880_p6, dispatch_e880a880_p7, dispatch_e880a880_p8, dispatch_e880a880_p9]

set_option maxRecDepth 32000 in
theorem reject_e880a880 : search 6 ins_e880a880 = false := by
  have hopt := opt_e880a880
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 6+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_e880a880 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (6 + 1 - ins_e880a880.length) = 2 := by decide
      simpa [hx] using hopt

def gates_e880a880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [2, 0]⟩, ⟨.or, [5, 3]⟩, ⟨.and, [1, 6]⟩, ⟨.and, [4, 2]⟩, ⟨.and, [5, 3]⟩, ⟨.or, [8, 0]⟩, ⟨.or, [9, 7]⟩, ⟨.and, [10, 11]⟩]
theorem upper_e880a880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe880a880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e880a880, 12, ?_, rfl, ?_⟩
  · simp [gates_e880a880]
  · decide +kernel

def ins_e8888880 : List W := [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]
theorem nd_e8888880 : ins_e8888880.Nodup := by decide +kernel
theorem spec_e8888880 : ∀ j : Fin 512, Nat.testBit 0xe8888880 (∑ i : Fin 5, if (ins_e8888880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p0 : dispatch 3 (optimized 6) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1) ([0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p1 : dispatch 3 (optimized 6) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916) ([0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p2 : dispatch 3 (optimized 6) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42) ([0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p3 : dispatch 3 (optimized 6) (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42) (0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9) ([0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p4 : dispatch 3 (optimized 6) (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p5 : dispatch 3 (optimized 6) (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p6 : dispatch 3 (optimized 6) (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1) (0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p7 : dispatch 3 (optimized 6) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p8 : dispatch 3 (optimized 6) (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916) (0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]) = false := by decide +kernel
set_option maxRecDepth 32000 in
set_option maxHeartbeats 40000000 in
theorem dispatch_e8888880_p9 : dispatch 3 (optimized 6) (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42) (0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9) ([0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916]) = false := by decide +kernel

theorem pairs_e8888880 : pairs ins_e8888880 = [(0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, [0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, [0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, [0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9, [0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]), (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]), (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9]), (0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42]), (0x9fe17f8ff7ffd65ffdeeaf7f5d87cfcf4656cac9a6938f81be6ff79efb63e9bb70eb1c70c202e759d5f8b02c5e15247149234d4a24b428f00cc9e2b13829cd42, 0xbb7117dfcf3aa116fb376ef4deb5fb7dd1d9f63d9eb7bd7fecdeccbfdff4af1dee522e32ddff80a99394098c8a612802160002658a8cfef9a781249f8e8254a9, [0xfffffcfcfbf7fffd5efbdbffeffff7f2ffbffdff7b6ffffffffbffff7dffdfef823cb3142e4a004108ac26168022c1242205f411cd0304ca24080ce369e12b42, 0xf7deeff33dff7ffbbfdfffdfbffffdffffffbffffdfdf7ff5bbf3ffbf7fffffe108289c351a5e812b8010c085210d2410cf889a210fa411311825208161e32b1, 0xd8afb77ffe2affa7e9ad3f36fcccabaffce3438afffa4f7dfd5cd14cefaf725ffe80640aa7d058420716333365222a406dbf0f332b5858043b5f8070c4b25916])] := by decide +kernel

theorem opt_e8888880 : optimized 7 3 ins_e8888880 = false := by
  unfold optimized
  have hs : (ins_e8888880 == [goal] || ins_e8888880 == [~~~goal]) = false := by decide +kernel
  rw [hs, Bool.false_or, pairs_e8888880]
  simp only [List.any_cons, List.any_nil, Bool.or_false, dispatch_e8888880_p0, dispatch_e8888880_p1, dispatch_e8888880_p2, dispatch_e8888880_p3, dispatch_e8888880_p4, dispatch_e8888880_p5, dispatch_e8888880_p6, dispatch_e8888880_p7, dispatch_e8888880_p8, dispatch_e8888880_p9]

set_option maxRecDepth 32000 in
theorem reject_e8888880 : search 7 ins_e8888880 = false := by
  have hopt := opt_e8888880
  apply List.any_eq_false.mpr
  intro ws hws
  cases hguard : decide (ws.length ≤ 7+1) && (cuts ws == -1) with
  | false => simp [hguard]
  | true =>
      have heq : ws = ins_e8888880 := by
        revert ws hws hguard
        decide +kernel
      subst heq
      have hx : (7 + 1 - ins_e8888880.length) = 3 := by decide
      simpa [hx] using hopt

def gates_e8888880 : List PEqualNP.CircuitLowerBounds.Gate := [⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.or, [4, 3]⟩, ⟨.and, [7, 5]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [5, 9]⟩, ⟨.and, [10, 2]⟩, ⟨.or, [8, 11]⟩, ⟨.and, [6, 12]⟩]
theorem upper_e8888880 : ∃ (gs : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8888880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  refine ⟨gates_e8888880, 13, ?_, rfl, ?_⟩
  · simp [gates_e8888880]
  · decide +kernel

end PEqualNP.Outside.L_meta_1417_aux

open PEqualNP.Outside.L_meta_1417_aux

set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1417 : ∀ T ∈ ({0xe8808080, 0xa8888880, 0xa888a080, 0xe8808880, 0xe888a000, 0xa8888888, 0xa888a880, 0xa8a8a800, 0xe880a880, 0xe8888880} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xe8808080 8 ins_e8808080 nd_e8808080 spec_e8808080 (by decide) reject_e8808080 upper_e8808080 gs o hg he
  · exact replace 0xa8888880 7 ins_a8888880 nd_a8888880 spec_a8888880 (by decide) reject_a8888880 upper_a8888880 gs o hg he
  · exact replace 0xa888a080 5 ins_a888a080 nd_a888a080 spec_a888a080 (by decide) reject_a888a080 upper_a888a080 gs o hg he
  · exact replace 0xe8808880 8 ins_e8808880 nd_e8808880 spec_e8808880 (by decide) reject_e8808880 upper_e8808880 gs o hg he
  · exact replace 0xe888a000 6 ins_e888a000 nd_e888a000 spec_e888a000 (by decide) reject_e888a000 upper_e888a000 gs o hg he
  · exact replace 0xa8888888 4 ins_a8888888 nd_a8888888 spec_a8888888 (by decide) reject_a8888888 upper_a8888888 gs o hg he
  · exact replace 0xa888a880 6 ins_a888a880 nd_a888a880 spec_a888a880 (by decide) reject_a888a880 upper_a888a880 gs o hg he
  · exact replace 0xa8a8a800 4 ins_a8a8a800 nd_a8a8a800 spec_a8a8a800 (by decide) reject_a8a8a800 upper_a8a8a800 gs o hg he
  · exact replace 0xe880a880 8 ins_e880a880 nd_e880a880 spec_e880a880 (by decide) reject_e880a880 upper_e880a880 gs o hg he
  · exact replace 0xe8888880 9 ins_e8888880 nd_e8888880 spec_e8888880 (by decide) reject_e8888880 upper_e8888880 gs o hg he
