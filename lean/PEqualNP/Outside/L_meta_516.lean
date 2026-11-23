import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

-- Live-wire compilation and completeness adapted from Lewis Watson, L-meta-515.
namespace Live516

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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

-- Any pair of rows which the output separates must stay separated at each cut.
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

end Live516

namespace Live516
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live516

namespace Check516

abbrev W := BitVec 320
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 0 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 160)).setWidth 160
def cuts (ws : List W) : BitVec 160 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 160) ++ (0 : BitVec 160)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

-- Each of the 160 pairs differs by turning on a single vertex.
-- The lower half is independent and the upper half contains an edge.
def rawInputs : List W :=
  [0xf00f80847c0f81088444488917c0f82245f05fc7f00780003c0780000000000003c0780000f00fc7,
   0x111091088490a2110bc3c178f0490a5e3c17cff8000000000000000003c3c078f000001e3c03cff8,
   0x22f9027c097904f813fc027f0097909fc02bf04100f8007c007800f803fc007f0007801fc003f000,
   0xff200f903fa01f207c88879223fa01e488fca088ff000f803f801f007c00078003f801e000fc0000,
   0x44422fffd00208427ffff800012425ffff40010200000fffc00000007ffff800000001ffff000000,
   0xfffff42100001fffa111102043ffff0912010210fffff00000001fff8000000003fffe0000000000,
   0x8884484222445ffffffffffffe004000008004040000000000001ffffffffffffc00000000000000,
   0xfffffffffffff084422224448800001020020820ffffffffffffe000000000000000000000000000]

def inputs := rawInputs.map canon

end Check516
namespace Check516
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check516

namespace Check516
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 160) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (160+i.val)

theorem neg_differs (i : Fin 160) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 160) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 160) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (160+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (160+i.val) := by simpa [differs] using h.2
  have lo : i.val < 320 := by omega
  have hi : 160+i.val < 320 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 160) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬160 + i.val < 160 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 160) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live516.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live516.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 160)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check516

namespace Check516

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

end Check516

namespace Check516
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 320) (z : W) := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 320) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 0 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide
  · subst z; left; decide
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160))) :
    Live516.build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide : ((-1 : BitVec 160) ++ (0 : BitVec 160)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide)
  | cons g gs ih =>
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)

def assignment (k : Fin 320) (i : Fin 8) := bit k (rawInputs.getD i.val 0)

theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live516.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 160) := [12, 18, 0, 3, 1, 4, 2, 5]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (160+i.val)) || b == a))) = true := by decide
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live516.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 320) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 320) : graph (assignment k) =
    bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 1) ||| (x 0 &&& x 4) ||| (x 4 &&& x 5) ||| (x 5 &&& x 1) ||| (x 0 &&& x 6) ||| (x 6 &&& x 7) ||| (x 7 &&& x 1) =
      ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by decide
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 320) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 160) ++ (0 : BitVec 160)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) = graph x) :
    Live516.build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live516.build basicOps goal k inputs.toFinset) :
    Live516.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live516.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live516.live basicOps goal m inputs.toFinset) :
    Live516.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Check516
namespace Check516

def rawOps (a b : W) := [both a b, both a (neg b), both (neg a) b, both (neg a) (neg b)]

theorem sep_canon (x : W) : sep (canon x) = sep x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h (v : W) : (sep v)[i] = true ↔ differs ⟨i,hi⟩ v := by
    change (sep v).getLsbD i = true ↔ _
    simp [sep, hi, differs]
  have eq := (h (canon x)).trans ((canon_differs ⟨i,hi⟩ x).trans (h x).symm)
  exact Bool.eq_iff_iff.mpr eq

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (rawOps a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (canon w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra-1) (canon w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra-1) (canon w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra-2) (canon w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k+1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a,b,r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z::kept) = -1) (ht : next (k-kept.length) (z::kept) = true) :
    dispatch extra next a b r = true := by
  have hmap : ops a b = (rawOps a b).map canon := rfl
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp (hmap ▸ List.mem_toFinset.mp hz)
  apply List.any_eq_true.mpr
  refine ⟨w,hw,?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [cuts, List.foldr_cons, sep_canon] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2 <;> omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1 <;> ac_rfl, by convert ht using 2 <;> omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1 <;> ac_rfl⟩, by convert ht using 2 <;> omega⟩

end Check516

namespace Check516

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live516.live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live516.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hc := Live516.live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check516

namespace Live516
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def kept (p : α → Option β) (s : Finset α) : Finset β := s.biUnion (fun a => (p a).toFinset)
def zeros (p : α → Option β) (s : Finset α) : ℕ :=
  (s.filter (fun a => p a = none)).card

theorem kept_insert (p : α → Option β) (a : α) (s : Finset α) :
    kept p (insert a s) = (p a).toFinset ∪ kept p s := by
  simp [kept]

theorem zeros_some {p : α → Option β} {a : α} {v : β} (h : p a = some v) (s : Finset α) :
    zeros p (insert a s) = zeros p s := by simp [zeros, Finset.filter_insert, h]

theorem zeros_none {p : α → Option β} {a : α} (h : p a = none) {s : Finset α} (ha : a ∉ s) :
    zeros p (insert a s) = zeros p s + 1 := by simp [zeros, Finset.filter_insert, h, ha]

theorem zeros_le (p : α → Option β) (a : α) (s : Finset α) :
    zeros p (insert a s) ≤ zeros p s + 1 := by
  cases h : p a with
  | some v => rw [zeros_some h]; omega
  | none =>
    by_cases hm : a ∈ s
    · rw [Finset.insert_eq_of_mem hm]; omega
    · exact (zeros_none h hm).le

theorem zeros_mono (p : α → Option β) {s t : Finset α} (h : s ⊆ t) :
    zeros p s ≤ zeros p t := Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem build_mono {ops : β → β → Finset β} {goal : β} {k : ℕ} {s t : Finset β}
    (hs : s ⊆ t) (h : build ops goal k s) : build ops goal k t := by
  induction k generalizing s t with
  | zero => exact hs h
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
    · exact .inl (ih hs skip)
    · exact .inr ⟨a,hs ha,b,hs hb,hab,z,hz,ih (Finset.insert_subset_insert _ hs) tail⟩

def projects (p : α → Option β) (ops : α → α → Finset α) (ops' : β → β → Finset β) : Prop :=
  ∀ a b z, z ∈ ops a b → ∀ v, p z = some v →
    p a = some v ∨ p b = some v ∨
    ∃ u w, p a = some u ∧ p b = some w ∧ u ≠ w ∧ v ∈ ops' u w

theorem zeros_step {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    (P : projects p ops ops') {a b z : α} (hz : z ∈ ops a b) (r : Finset α)
    (fresh : z ∉ insert a (insert b r)) :
    zeros p (insert a (insert b r)) ≤ zeros p (insert z r)+1 := by
  have mono := zeros_mono p (Finset.subset_insert z r)
  cases ha : p a with
  | some u =>
    rw [zeros_some ha]
    have h := zeros_le p b r
    omega
  | none =>
    cases hb : p b with
    | some v =>
      have h := zeros_le p a (insert b r)
      rw [zeros_some hb] at h
      omega
    | none =>
      have hzn : p z = none := by
        cases he : p z with
        | none => rfl
        | some v => simpa [ha, hb] using P a b z hz v he
      have hzout : z ∉ r := by intro h; exact fresh (by simp [h])
      rw [zeros_none hzn hzout]
      have u := zeros_le p a (insert b r)
      have v := zeros_le p b r
      omega

theorem zeros_budget {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) : zeros p s ≤ k := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, zeros, hg]
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact (ih skip).trans (by omega)
    · exact (zeros_step P hz r hn).trans (Nat.succ_le_succ (ih tail))

theorem project_live {p : α → Option β} {ops : α → α → Finset α} {ops' : β → β → Finset β}
    {g : α} {g' : β} (hg : p g = some g') (P : projects p ops ops') {k : ℕ} {s : Finset α}
    (h : live ops g k s) (n : ℕ) (budget : k ≤ n + zeros p s) :
    build ops' g' n (kept p s) := by
  induction k generalizing s n with
  | zero =>
    change s = {g} at h
    have mem : g' ∈ kept p s := by simp [h, kept, hg]
    induction n with
    | zero => exact mem
    | succ n ih => exact Or.inl (ih (by omega))
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,hab,z,hz,hn,r,rfl,tail⟩
    · exact ih skip n (by omega)
    · have dz := zeros_step P hz r hn
      have free (hs : kept p (insert z r) ⊆ kept p (insert a (insert b r))) :
          build ops' g' n (kept p (insert a (insert b r))) :=
        build_mono hs (ih tail n (by omega))
      cases hZ : p z with
      | none =>
        apply free
        simp [kept_insert, hZ]
        exact fun _ hx => Finset.mem_union_right _ (Finset.mem_union_right _ hx)
      | some v =>
        rcases P a b z hz v hZ with ha|hb|⟨u,w,hA,hB,hw,hop⟩
        · apply free
          simp [kept_insert, hZ, ha]
        · apply free
          simp [kept_insert, hZ, hb]
        · rw [zeros_some hA, zeros_some hB] at budget
          have dz' := zeros_some hZ r
          have bound := zeros_budget hg P tail
          cases n with
          | zero => omega
          | succ n =>
            have next := ih tail n (by omega)
            have covers : kept p (insert z r) ⊆ insert v (kept p (insert a (insert b r))) := by
              simp [kept_insert,hZ,hA,hB]
              intro x hx
              simp only [Finset.mem_insert] at hx ⊢
              tauto
            exact Or.inr ⟨u, by simp [kept_insert,hA], w, by simp [kept_insert,hB],
                hw, v, hop, build_mono covers next⟩

end Live516

namespace Check516

abbrev Half := BitVec 160
def fill (m : Half) (r : Fin 160) (x : Half) : Half :=
  (x &&& m) ||| (if x[r.val] then ~~~m else 0)

def crop (m : Half) (r : Fin 160) (x : W) : W :=
  (fill m r ((x >>> 160).setWidth 160)) ++ (fill m r (x.setWidth 160))

theorem fill_bit (m x : Half) (r : Fin 160) {i : ℕ} (hi : i < 160) :
    (fill m r x)[i] = if m[i] then x[i] else x[r.val] := by
  unfold fill
  cases hr : x[r.val] <;> cases hm : m[i] <;> simp [hr, hm]

def pos (m : Half) (r : Fin 160) (i : Nat) :=
  if i < 160 then (if m.getLsbD i then i else r.val)
  else (if m.getLsbD (i-160) then i else 160+r.val)

theorem pos_lt (m : Half) (r : Fin 160) {i : Nat} (hi : i < 320) : pos m r i < 320 := by
  unfold pos; split <;> split <;> omega

theorem fill_lsb (m x : Half) (r : Fin 160) {i : Nat} (hi : i < 160) :
    (fill m r x).getLsbD i = if m.getLsbD i then x.getLsbD i else x.getLsbD r.val := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem r.isLt] using fill_bit m x r hi

theorem crop_bit (m : Half) (r : Fin 160) (x : W) (i : ℕ) (hi : i < 320) :
    (crop m r x).getLsbD i = x.getLsbD (pos m r i) := by
  unfold crop pos
  rw [BitVec.getLsbD_append]
  by_cases h : i < 160
  · rw [if_pos h, if_pos h, fill_lsb _ _ _ h]
    cases e : m.getLsbD i <;> simp only [BitVec.getLsbD_setWidth, h, r.isLt, decide_true,
      Bool.true_and, Bool.false_eq_true, if_false, if_true]
  · have hr : i-160 < 160 := by omega
    rw [if_neg h, if_neg h, fill_lsb _ _ _ hr]
    cases e : m.getLsbD (i-160) <;> simp only [BitVec.getLsbD_setWidth, hr, r.isLt,
      decide_true, Bool.true_and, Bool.false_eq_true, if_false, if_true, BitVec.getLsbD_ushiftRight,
      show 160+(i-160)=i by omega]

theorem crop_and (m : Half) (r : Fin 160) (x y : W) :
    crop m r (x &&& y) = crop m r x &&& crop m r y := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (x &&& y)).getLsbD j = (crop m r x &&& crop m r y).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_and]

theorem crop_neg (m : Half) (r : Fin 160) (x : W) :
    crop m r (~~~x) = ~~~crop m r x := by
  apply BitVec.eq_of_getElem_eq
  intro j h
  change (crop m r (~~~x)).getLsbD j = (~~~crop m r x).getLsbD j
  simp only [crop_bit _ _ _ _ h, BitVec.getLsbD_not, h, pos_lt _ _ h]

def wrap (x : W) : Option W := if canon x = 0 then none else some (canon x)
theorem wrap_neg (x : W) : wrap (~~~x) = wrap x := by simp only [wrap, canon_neg]

def cropOpt (m : Half) (r : Fin 160) (x : W) := wrap (crop m r x)

theorem crop_canon (m : Half) (r : Fin 160) (x : W) :
    cropOpt m r (canon x) = cropOpt m r x := by
  unfold canon
  split
  · simp only [cropOpt, neg, crop_neg, wrap_neg]
  · rfl

set_option maxRecDepth 2500 in
theorem crop_goal (m : Half) (r : Fin 160) : cropOpt m r goal = some goal := by
  have g : goal = (BitVec.allOnes 160 ++ (0 : Half)) := by decide
  have eq : crop m r goal = goal := by
    change (fill m r (BitVec.allOnes 160) ++ fill m r 0) = (BitVec.allOnes 160 ++ (0 : Half))
    congr 1
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp only [BitVec.getElem_allOnes, ite_self]
    · apply BitVec.eq_of_getElem_eq
      intro i hi; rw [fill_bit _ _ _ hi]; simp

  rw [cropOpt, eq]
  decide

set_option maxRecDepth 2500 in
theorem binary_project {x y v : W} (h : wrap (x &&& y) = some v) :
    wrap x = some v ∨ wrap y = some v ∨
    ∃ u w, wrap x = some u ∧ wrap y = some w ∧ u ≠ w ∧ v ∈ basicOps u w := by
  have trivial (t : W) (ht : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 320 := by
    rcases sign t with h'|h' <;> rw [ht] at h'
    · exact .inl h'
    · exact .inr h'
  by_cases hx : canon x = 0
  · rcases trivial _ hx with rfl|rfl
    · rw [show (0 : W) &&& y = 0 from BitVec.zero_and] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.allOnes_and] at h; exact .inr (.inl h)
  by_cases hy : canon y = 0
  · rcases trivial _ hy with rfl|rfl
    · rw [show x &&& (0 : W) = 0 from BitVec.and_zero] at h
      have h0 : wrap 0 = none := by decide
      have bad := h0.symm.trans h; cases bad
    · rw [BitVec.and_allOnes] at h; exact .inl h
  have hn : canon (x &&& y) ≠ 0 := by intro hn; simp [wrap, hn] at h
  have hval : canon (x &&& y) = v := by simpa only [wrap, if_neg hn, Option.some.injEq] using h
  by_cases eq : canon x = canon y
  · rcases same_both eq with same|bad
    · exact .inl (by simp only [wrap, if_neg hx, ← hval, same])
    · exact False.elim (hn bad)
  · exact .inr (.inr ⟨canon x,canon y,by simp only [wrap,if_neg hx],by simp only [wrap,if_neg hy],eq,
        hval ▸ signed_both (sign x) (sign y)⟩)

theorem mask_projects (m : Half) (r : Fin 160) : Live516.projects (cropOpt m r) basicOps basicOps := by
  intro a b z hz v hv
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [crop_canon] at hv <;> simp only [cropOpt, both, neg, crop_and, crop_neg] at hv ⊢ <;>
    simpa only [wrap_neg] using binary_project hv

end Check516

namespace Check516

def maybeBuild (n : Nat) (av : List W) : Bool :=
  av.sublists.any (fun ws => ws.length ≤ n+1 && cuts ws == -1 &&
    optimized n (n+1-ws.length) ws)

theorem maybeBuild_complete {n : ℕ} {av : List W} (hn : av.Nodup)
    (h : Live516.build basicOps goal n av.toFinset) : maybeBuild n av = true := by
  obtain ⟨s,hs,hr⟩ := Live516.compress h
  let xs := av.filter (fun a => decide (a ∈ s))
  have hsub : xs.Sublist av := List.filter_sublist
  have hnd : xs.Nodup := hn.sublist hsub
  have heq : xs.toFinset = s := by
    ext a
    simp only [List.mem_toFinset, xs, List.mem_filter, decide_eq_true_eq]
    exact ⟨And.right, fun ha => ⟨List.mem_toFinset.mp (hs ha),ha⟩⟩
  rw [←heq] at hr
  have bound := Live516.live_card hr
  rw [List.toFinset_card_of_nodup hnd] at bound
  apply List.any_eq_true.mpr
  refine ⟨xs,List.mem_sublists.mpr hsub,?_⟩
  have ok := optimized_complete n xs (n+1-xs.length) hnd (by omega) hr
  simp [bound, cuts_full hr, ok]

def projectedBudget (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Nat :=
  n - (ws.filter (fun w => (cropOpt m r w).isNone)).length

def available (m : Half) (r : Fin 160) (ws : List W) : List W :=
  (ws.filterMap (cropOpt m r)).dedup

theorem available_spec (m : Half) (r : Fin 160) (ws : List W) :
    (available m r ws).toFinset = Live516.kept (cropOpt m r) ws.toFinset := by
  ext y; simp [available, Live516.kept, List.mem_filterMap]

theorem projected_bound (m : Half) (r : Fin 160) (n : Nat) {ws : List W} (hn : ws.Nodup) :
    n ≤ projectedBudget m r n ws + Live516.zeros (cropOpt m r) ws.toFinset := by
  let xs := ws.filter (fun w => (cropOpt m r w).isNone)
  have eq : (xs.toFinset) = ws.toFinset.filter (fun w => cropOpt m r w = none) := by
    ext w; simp [xs]
  have card := List.toFinset_card_of_nodup (hn.sublist (List.filter_sublist :
    xs.Sublist ws))
  rw [eq] at card
  change (ws.toFinset.filter (fun w => cropOpt m r w = none)).card = xs.length at card
  change n ≤ n-xs.length + (ws.toFinset.filter (fun w => cropOpt m r w = none)).card
  omega

theorem projection_survives (m : Half) (r : Fin 160) {k : ℕ} {ws : List W}
    (hn : ws.Nodup) (h : Live516.live basicOps goal k ws.toFinset) :
    maybeBuild (projectedBudget m r k ws) (available m r ws) = true := by
  have hbuild := Live516.project_live (crop_goal m r) (mask_projects m r) h _ (projected_bound m r k hn)
  rw [← available_spec] at hbuild
  exact maybeBuild_complete (List.nodup_dedup _) hbuild

end Check516

namespace Check516

abbrev Claim := Nat × List W
abbrev Hint := Half × Fin 160 × Nat

def goodClaim (c : Claim) : Bool := decide c.2.Nodup && !(maybeBuild c.1 c.2)

def usable (c : Claim) (m : Half) (r : Fin 160) (n : Nat) (ws : List W) : Bool :=
  projectedBudget m r n ws ≤ c.1 &&
  ws.all (fun w => match cropOpt m r w with | none => true | some y => c.2.contains y)

theorem unusable (c : Claim) (m : Half) (r : Fin 160) {n : Nat} {ws : List W}
    (hn : ws.Nodup) (live : Live516.live basicOps goal n ws.toFinset) (hc : goodClaim c) :
    usable c m r n ws = false := by
  apply Bool.eq_false_iff.mpr
  intro u
  simp only [goodClaim, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc
  simp only [usable, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at u
  have budget := projected_bound m r n hn
  have bound : n ≤ c.1 + Live516.zeros (cropOpt m r) ws.toFinset := by omega
  have build := Live516.project_live (crop_goal m r) (mask_projects m r) live _ bound
  have sub : Live516.kept (cropOpt m r) ws.toFinset ⊆ c.2.toFinset := by
    intro y hy
    obtain ⟨w,hw,hv⟩ := Finset.mem_biUnion.mp hy
    have hy' : cropOpt m r w = some y := by simpa using hv
    have hu := u.2 w (List.mem_toFinset.mp hw)
    simpa [hy'] using hu
  have ok := maybeBuild_complete hc.1 (Live516.build_mono sub build)
  exact Bool.noConfusion (hc.2.symm.trans ok)

def key (n : Nat) (ws : List W) : Nat := ws.foldl (fun h w => (65599*h+w.toNat)%1000000007) n

def matched (table : List Claim) (hint : Nat → Option Hint) (n : Nat) (ws : List W) : Bool :=
  match hint (key n ws) with
  | none => false
  | some (m,r,j) => (table[j]?).any (fun c => usable c m r n ws)

theorem matched_false {table : List Claim} (ht : table.all goodClaim = true)
    (hint : Nat → Option Hint) {n : Nat} {ws : List W} (hn : ws.Nodup)
    (h : Live516.live basicOps goal n ws.toFinset) : matched table hint n ws = false := by
  unfold matched
  cases hh : hint (key n ws) with
  | none => rfl
  | some data =>
    obtain ⟨m,r,j⟩ := data
    change (table[j]?).any (fun c => usable c m r n ws) = false
    cases he : table[j]? with
    | none => rfl
    | some c =>
      exact unusable c m r hn h (List.all_eq_true.mp ht c (List.mem_of_getElem? he))

def front (table : List Claim) (hint : Nat → Option Hint) : Nat → Nat → Nat → List W → Bool
  | 0, n, extra, ws => !(matched table hint n ws) && optimized n extra ws
  | depth+1, n, extra, ws =>
    !(matched table hint n ws) && (ws == [goal] ||
      (pairs ws).any (fun (a,b,r) => dispatch extra (front table hint depth (n-1)) a b r))

theorem front_complete {table : List Claim} (ht : table.all goodClaim = true) (hint : Nat → Option Hint)
    (depth n : Nat) (ws : List W) (extra : Nat) (hn : ws.Nodup)
    (room : extra + ws.length = n+1) (h : Live516.live basicOps goal n ws.toFinset) :
    front table hint depth n extra ws = true := by
  induction depth generalizing n ws extra with
  | zero => simp [front, matched_false ht hint hn h, optimized_complete n ws extra hn room h]
  | succ depth ih =>
    simp only [front, matched_false ht hint hn h, Bool.not_false, Bool.true_and]
    cases n with
    | zero => simp [singleton_list hn h]
    | succ k =>
      simp only [Nat.add_one_sub_one]
      rcases Live516.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
      · simp [singleton_list hn done]
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W} (perm : ws.Perm (a::b::r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatch extra (front table hint depth k) a b r = true := by
          obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
          have hl : Live516.live basicOps goal k (z::kept).toFinset := by
            simpa [hfin] using tail
          have hc := Live516.live_card hl
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
          have len := perm.length_eq
          simp only [List.length_cons] at len
          apply dispatch_complete (k := k) (extra := extra) (front table hint depth k) hop hk (by omega) (by omega) (cuts_full hl)
          apply ih _ _ _ hnd _ hl
          simp; omega
        simp only [Bool.or_eq_true, List.any_eq_true]
        right
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, go hp hs hz⟩
        · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

theorem lower_of_front (table : List Claim) (hint : Nat → Option Hint) (depth : Nat)
    (ht : table.all goodClaim = true) (check : front table hint depth 11 4 inputs = false)
    (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize 8 graph s) : 12 ≤ s := by
  by_contra! hs
  obtain ⟨C,hg,hsize,he⟩ := h
  have hl : C.gates.length ≤ 11 := by change C.gates.length ≤ s at hsize; omega
  have searched := front_complete ht hint depth 11 inputs 4 (by decide) (by decide)
    (extend_live hl (input_live _ (get_build C hg he)))
  exact Bool.noConfusion (check.symm.trans searched)

end Check516

namespace Check516

def claim0 : Claim := (7, [0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim1 : Claim := (3, [0x2000040000000200008000000000000000000000240004000000028000c00000001000000, 0x200044000000028000c000000000000040000000000000000000028000c00000000000000, 0x2400640000000200008000000000000000000000240064000000000000000000000000000, 0xfffffffffffbbffffffffffff3fffffffffffffb0000000240000000000028000000000001000000])
def claim2 : Claim := (6, [0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim3 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim4 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000])
def claim5 : Claim := (6, [0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim6 : Claim := (6, [0x6003000040060000300008000400020000000000600340004006800038000c00040003000000, 0x800000008000000000000000080000000f000000000000000000000000000000000000000f00, 0x4400200044006800038000c004000000004040000000000000006800038000c00000000000000, 0x6e001000000068000100000006c00020002000006e000000000068000000000006c0000000000, 0x6e0034006c0040000200008000000000008000006e0034006c000000000000000000000000000, 0xfffb3ffffffb3ffb7ffffffff3ffb7fffffff1fb0000000340000000000038000000000003000000])
def claim7 : Claim := (6, [0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim8 : Claim := (6, [0x422067400200420034380000042401430000020000006740000000003438000000000143000000, 0x844042004440ce803438050c0040000000000400000000000000ce803438050c00000000000000, 0xc06063004040c600303004080404010200000000c86067404840ce803438050c04840143001000, 0xcf6021000000ce801010000004f4010200000000cf6000000000ce800000000004f40000000000, 0xcf6067404f408400202004080000000000000000cf6067404f4000000000000000000000000000, 0xfff99ffcbff9bff97fffc7fff3ff9bfffcfffff900c80064004800c8003400050004800140001000])
def claim9 : Claim := (7, [0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim10 : Claim := (6, [0x36040000000060608000000000820000000000003684000000006870c00000000083000, 0x4008000000000000000000000100cc00000000000000000000000000000000000000cc0, 0x22444000000006870c000000008004040000000000000000000006870c00000000000000, 0x2f200000000006820000000000b82080000000002f000000000006800000000000b80000, 0x2f6dc000000004040800000000000800000000002f6dc000000000000000000000000000, 0xffffffffd9fb3ffffffffb7ff3ffffffff6ff37b0000000000680000000000070000000000003000])
def claim11 : Claim := (6, [0x84222444000542c2e870c000000008000040000000000000000542c2e870c00000000000000, 0xa520360400050282606080000808008200000000ad643684000542c2e870c0000a0c1083000, 0xa903b20000054080682000000a080e8200000000a803b00000054000680000000a000e80000, 0xad650020000542c2800000000a0c140000200000ad640000000542c2800000000a0c1000000, 0xad67b6f400040202404080000000000000000000ad67b6f4000000000000000000000000000, 0xfffff77d8df9bfffbbffd37ff3ffffdffe3ffff90000005400680000002c000700000000c0003000])
def claim12 : Claim := (7, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim13 : Claim := (6, [0x36058182082000000000000000000000000000003685a1c3083000, 0x400800001003c000000000000000000000000000000000000003c0, 0x12425a1c3400102000000000000000000000000000001a1c3000000, 0x1f201a08078208000000000000000000000000001f001a000780000, 0x1f6bd010200020000000000000000000000000001f6bc0000000000, 0xfffffffffffffffffffffffffe9fd2dffcaffc7d00000000000000000000000000068001c0003000])
def claim14 : Claim := (6, [0x842341c1800012425a1c34000020000000000000000341c1800000001a1c3000000, 0xc623018120200360581820820000000000000000d6ab41c1a83043685a1c3083000, 0xd203408028203b201a080e820000000000000000d003400028003b001a000e80000, 0xd6aa010100003b6f501020000000000000000000d6a8000000003b6f40000000000, 0xd6ab41c1a8306004000008000040000000000000d6ab41c1a830400000000000000, 0xfffffffffffff6fd5bffe77ff8df9adffc3ffff90000000000000068001c000300068001c0003000])
def claim15 : Claim := (3, [0x80000000000000000, 0xfffffffffffffffffffffff7ffffffffffffffff0000000000000000000000000000000000000000])
def claim16 : Claim := (6, [0x4002d03800008026803b000002005403a00000000000d03800000006803b000000001403a000000, 0x800480202005a076803b500e8000000000000000000000000001a076803b500e800000000000000, 0xc006c03020058066000340008200500020000000d007d0382807a07680035000828074002040000, 0xd00740100001a072001100040280700120000100d00700000001a07000000000028060000000000, 0xd007d03828070044002240088000000200000200d007d0382806000000000000000000000000000, 0xffff8ffc7fff9ff8fffccfff37fff9ffcdffffcf0d000d0002801a00680005000028014000040000])
def claim17 : Claim := (3, [0x800020000004000040000000000000000000000088002000000440004800000002000000000, 0x800220000004400048000000000008000000000000000000000440004800000000000000000, 0x880320000004000040000000000000000000000088032000000000000000000000000000000, 0xffffffffddfffffffffffb7fffffffffff7fffff0000088000000000440000000000002000000000])
def claim18 : Claim := (3, [0x20200000000000820000000000000000000000002830400000000083000, 0x2820000000000a820000000000000000000000002800000000000a80000, 0x28304000000008000040000000000000000000002830400000000000000, 0xffffffffffffffffffffff7ffbffffffff7ffffb0000000000000000000000030000000000003000])
def claim19 : Claim := (6, [0x2b00000017004b00000027600130000000ba00000b00000007000b000000076000300000003a000, 0x8804000024056b500000776e80000000000000000000000000016b500000776e800000000000000, 0xaa04000036054a40000060608120000000820000bb0500003f076b500000706081b0200000c2000, 0xbb05000000016b500000020401b0200000100100bb05000000016b500000000001b020000000000, 0xbb0500003f070840000044488000000000200200bb0500003f06000000000000000000000000000, 0xff6fafffffaf9f6affffff9b37fefdfffffcffcf0b000000038016000000070000180000000c0000])
def claim20 : Claim := (3, [0x4200000000000120000000000000000000000000528800000000012800000000000, 0x5200000000002920000000000000000000000000500000000000290000000000000, 0x5288000000002004000000000000000000000000528800000000000000000000000, 0xfffffffffffffeff7ffffffffdffbfffffffffff0000000000000028000000000002800000000000])
def claim21 : Claim := (3, [0x210012000000000000000000000000000000000029441280000000000000000000000000000, 0x290192000000000000000000000000000000000028019000000000000000000000000000000, 0x294500200000000000000000000000000000000029440000000000000000000000000000000, 0xffffff7faffdffffffffffffffffffffffffffff0000001400280000000000000000000000000000])
def claim22 : Claim := (6, [0x270023801300000000000000017009d800ba0000070003800300000000000000007001d8003a000, 0x44027398000000000000000002405ddba000000000007398000000000000000000001ddba000000, 0x6602631012000000000000000360581820820000770373981b0200000000000003f07c1820c2000, 0x77034210000000000000000003f070912010010077030000000000000000000003f060000000000, 0x770373981b020000000000000000010200200200770373981b02000000000000000000000000000, 0xffafcfd67fefdffffffffffffffaf9e6cdfcffcf070007000180000000000000003801c0000c0000])
def claim23 : Claim := (7, [0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x77fbbfffddfbaefb7ffffb7ff1ffbfffff7ffffb00e80ef7406800e8743c3807000681a1c3003000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim24 : Claim := (7, [0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xbbfddb7eaffdfffffffffffffedfdadffcbffffd00e8007400681deef43c3e870c068001c0003000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim25 : Claim := (7, [0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xccc66ef772465deef43c3e870f2465a1c3c0000600000ef740001deef43c3e870c0001a1c3000000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim26 : Claim := (6, [0x60030000400600003000080004000200000000007003c0006007800038000c00060003000000, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim27 : Claim := (6, [0x10800800108000000000000001081a34034b700000000000000000000000000000001a34034b70, 0x42002c00020000000000000004201b740001020000002c00000000000000000000001b74000000, 0x500028001000000000000000050019300300300058002c00180000000000000005801b74035030, 0x5b802000000000000000000005b80910010210005b800000000000000000000005b80000000000, 0x5b802c001b8000000000000000001020020820005b802c001b8000000000000000000000000000, 0xfffd7ffffffd7fffffffffffffffd7ffcbfff4cd0058002c00180000000000000005801b40035000])
def claim28 : Claim := (6, [0x10800800108000000000000001081a34034b700000000000000000000000000000001a34034b70, 0x400020000000000000000000040001000000000058002c00180000000000000005800140001000, 0x42002c00020000000000000004201b740001020000002c00000000000000000000001b74000000, 0x500028001000000000000000050019300300300058002c00180000000000000005801b74035030, 0x5b802000000000000000000005b80910010210005b800000000000000000000005b80000000000, 0x5b802c001b8000000000000000001020020820005b802c001b8000000000000000000000000000, 0xfffd7ffffffd7fffffffffffffffd7ffcbfff4cd0058002c00180000000000000005801b40035000])
def claim29 : Claim := (6, [0x2000801c100704808401c14079800000000000000000001c000700000001c000798, 0xa002801810060280140180400180000000000000b002c01c180702801601c040018, 0xb002001000043686900100002100000000000000b00000000000368680000000000, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb002c01c18072004000008004040000000000000b002c01c1807000000000000000, 0xfffffffffffffcfffffffe7f8db7b7ffff6bf96300000000000000002c01c000000001601c000000])
def claim30 : Claim := (6, [0x2000801c100704808401c14079800000000000000000001c000700000001c000798, 0x8002000000000200100000000000000000000000b002c0001800028016000040000, 0xa002801810060280140180400180000000000000b002c01c180702801601c040018, 0xb002001000043686900100002100000000000000b00000000000368680000000000, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb002c01c18072004000008004040000000000000b002c01c1807000000000000000, 0xfffffffffffffcfffffffe7f8db7b7ffff6bf96300000000000000002c01c000000001601c000000])
def claim31 : Claim := (6, [0x36040000000060608000000000820000000000003f86000000007870c000000000c3000, 0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim32 : Claim := (6, [0x100840080000802c000b00000402c100da800000000000000000002c000b00000002c000da8, 0x802200400004c02e800b00000000080040400000000000000004c02e800b000000000000000, 0x902800000004802a000a00000402800002800000982c00000004c02e800b00000602d000028, 0x980340000004c0080002000006008d0008800000980340000004c0000000000006000d00000, 0x982f406800040022000800000002000082000000982f4068000000000000000000000000000, 0xffffffffdbfb7fffffffffff4fffffffff6ff35300000982c00000004c02e800000000602d000000])
def claim33 : Claim := (6, [0x100840080000802c000b00000402c100da800000000000000000002c000b00000002c000da8, 0x8020000000040002000000000000000000000000982c00000004c0028000000006001000000, 0x802200400004c02e800b00000000080040400000000000000004c02e800b000000000000000, 0x902800000004802a000a00000402800002800000982c00000004c02e800b00000602d000028, 0x980340000004c0080002000006008d0008800000980340000004c0000000000006000d00000, 0x982f406800040022000800000002000082000000982f4068000000000000000000000000000, 0xffffffffdbfb7fffffffffff4fffffffff6ff35300000982c00000004c02e800000000602d000000])
def claim34 : Claim := (6, [0x2110000003870490a000011c6d8000000000000000000000038700000000001c6d8, 0x63100000030601b020000018018000000000000073980000038701b82000001c018, 0x7200000001022da000000b0808800000000000007000000000002d8000000b00000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x7398000003872004000008004040000000000000739800000387000000000000000, 0xfffffffffffffcfe7fffffff8db7b5ffff6ff963000000000000003800000038000380000001c000])
def claim35 : Claim := (6, [0x2110000003870490a000011c6d8000000000000000000000038700000000001c6d8, 0x420000000000012000000000000000000000000073980000000001b820000000000, 0x63100000030601b020000018018000000000000073980000038701b82000001c018, 0x7200000001022da000000b0808800000000000007000000000002d8000000b00000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x7398000003872004000008004040000000000000739800000387000000000000000, 0xfffffffffffffcfe7fffffff8db7b5ffff6ff963000000000000003800000038000380000001c000])
def claim36 : Claim := (6, [0x36058182082000000000000000000000000000003f87e1c30c3000, 0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim37 : Claim := (6, [0x21100000138704008000011c6d8000000000000000000000038700000000001c6d8, 0x6310000033260000000000180180000000000000739800003bb740000000001c018, 0x7200000039222c0000000b0808800000000000007000000038002c0000000b00000, 0x7398000002042c058000001021000000000000007398000000002c0580000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89bfb7ffff6ff96300000000000000380000003b000000000001c000])
def claim38 : Claim := (6, [0x21100000138704008000011c6d8000000000000000000000038700000000001c6d8, 0x4200000020200000000000000000000000000000739800003830400000000000000, 0x6310000033260000000000180180000000000000739800003bb740000000001c018, 0x7200000039222c0000000b0808800000000000007000000038002c0000000b00000, 0x7398000002042c058000001021000000000000007398000000002c0580000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89bfb7ffff6ff96300000000000000380000003b000000000001c000])
def claim39 : Claim := (6, [0x1090088010a000000000000000081a34034b700000000000000000000000000000001a34034b70, 0x42202dc0020000000000000000201a340001020000002dc0000000000000000000001a34000000, 0x503029801020000000000000000018300300300058302dc0182000000000000000001a34034030, 0x5bb02100000000000000000000380810010210005bb00000000000000000000000380000000000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd7ffcbfff4cd0058002c00180000000000000000001a00034000])
def claim40 : Claim := (6, [0x1090088010a000000000000000081a34034b700000000000000000000000000000001a34034b70, 0x402021000000000000000000000000000000000058302dc0182000000000000000000000000000, 0x42202dc0020000000000000000201a340001020000002dc0000000000000000000001a34000000, 0x503029801020000000000000000018300300300058302dc0182000000000000000001a34034030, 0x5bb02100000000000000000000380810010210005bb00000000000000000000000380000000000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd7ffcbfff4cd0058002c00180000000000000000001a00034000])
def claim41 : Claim := (3, [0x800000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000000080000000000000000])
def claim42 : Claim := (7, [0xc000c00020018006000040000200100000000000d000d8002801b006c0005800028016000040000, 0x1100810004808200080001000048084000140f800000000000000000000000000000000000000f80, 0x66fb7fffd97b6cfffffffa7ffdb7b7ffff6bf17b00000d80000000006c0000000000016000000000, 0x8804080022041b006c00058002004000008004040000000000001b006c0005800000000000000000, 0xdd000d8036801b006c0005800368016000d40080dd000d8036801b006c0005800368016000d40000, 0xdd06840000001b00200000000368690000000200dd06800000001b00000000000368680000000000, 0xdd068d8036869000400004000000000000000800dd068d8036868000000000000000000000000000])
def claim43 : Claim := (7, [0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0x8022000100000200500020000000000000000000b03ac0019800428076003040000, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb032c019180636807601ad400980000000000000b03ac01d980776807601fd40018, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim44 : Claim := (7, [0xaa04000000014a40000000000120000000000000bb85000000017bd80000000001b820000000000, 0x11109000040082110000000000490a0000100ec00000000000000000000000000000000000000ec0, 0x66fb2fffdbfb6cfa7ffffffffdb7b5ffff6ff17b00b80000000000b8000000000003800000000000, 0x88844000200417bd80000000020040000080040400000000000017bd800000000000000000000000, 0xbb2000002c0017200000000002da000000b00080bb0000002c0017000000000002d8000000b00000, 0xbbbdd000000017bd8000000002dbda0000000200bbbdd000000017bd8000000002dbda0000000000, 0xbbbdd0002c059084000000000000000000000800bbbdd0002c058000000000000000000000000000])
def claim45 : Claim := (7, [0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x80400000404084000000040800000000000000009850000058609d800000050c01820000001000, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd0000050609d80000064c801da0000030230009dd0000058609d8000006ddc01da0000035030, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim46 : Claim := (7, [0x660263101200000000000000000000000000000077837bdc1b82000000000000000000000000000, 0x111091088490a000000000000040080000100bc00000000000000000000000000000000000000bc0, 0x444227bdd0020000000000000100200000400102000007bdc0000000000000000000000000000000, 0x772007901da000000000000001c0000000700080770007801d8000000000000001c0000000700000, 0x777bb421000000000000000001c0380000000200777bb000000000000000000001c0380000000000, 0x777bb7bdddbba000000000000000000000000800777bb7bdddbba000000000000000000000000000, 0xaafd4a7e2b7d5ffffffffffffebfd7ffffaff47d0078003c00380000000000000000000000000000])
def claim47 : Claim := (7, [0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x210012000000000000000000080800820000000039cc1b8200000000000000000e0c10c3000, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0x39cddbba00000000000000000d4a80ea8280000039cddbba00000000000000000f6ed0ef028, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim48 : Claim := (7, [0x90000000a00100000000d0000a0000000e30000000000000000000000000d000000000000e70, 0x80400000404084000000040800000000000000009850000058609d800000050c01820000001000, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim49 : Claim := (7, [0x8000400080008004440091000800244005f400000000000000000000000000000000000000f40, 0x40006c00000040037740000004001b740001000000006c00000000037740000000001b74000000, 0x800040004000d80377406dd00000000000040000000000000000d80377406dd000000000000000, 0xc00060004000c000300004000400010000000000d8006c005800d8003400050005800140001000, 0xd8006c0058008002220044800000102002082000d8006c00580000000000000000000000000000, 0xd8006c005800d80374006d0005801b4003504000d8006c005800d80374006d0005801b40035000, 0xffffffb3ffa7fffffd99bfb26fffffed9bfda29f00d80000000000d8000000000005800000000000])
def claim50 : Claim := (7, [0x490a00000000000000000000016c8e8000000000000000000000000000000000002c9e8, 0x210012000000000000000000080800820000000039cc1b8200000000000000000e0c10c3000, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim51 : Claim := (7, [0x8440000000044448081000002245004dc00000000000000000000000000000000000000dc0, 0x25c0000000012ec005800000096c002c0400000005c0000000002ec005800000016c002c000, 0x842000000005eeee858b00000000000040000000000000000005eeee858b000000000000000, 0xa520000000050282000000000808000000000000bdec00000005c2c2800000000e0c1000000, 0xbdec000000042222040800000102002082000000bdec0000000000000000000000000000000, 0xbdec00000005eeee800000000f6ed00010000000bdec00000005eeee800000000f6ed000000, 0xffffffb13ffffffffd9997b76fffffed9afdb29f00000b80000000005c000000000000e000000000])
def claim52 : Claim := (7, [0x480a401c140398000000000000000000000000000000001c000798, 0x8022000100000200500020000000000000000000b03ac0019800428076003040000, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim53 : Claim := (7, [0x1088444488914000002040047c000000000000000000000000000000000000007c0, 0x47811dc023b0000000e0001c040000000000000007801dc003b0000000e0001c000, 0x8423dddd8000000000e1c00010000000000000000003dddd8000000000e1c000000, 0xc623018120200000000000000000000000000000f7bbc1c1b830400000000000000, 0xf7ba111102040000008100102100000000000000f7b800000000000000000000000, 0xf7bbddddbbb74000000000004000000000000000f7bbddddbbb7400000000000000, 0xffffffffffffffa47eaaa7d6abfffff5ebfeb8af0000000000000f003c0003800000000000000000])
def claim54 : Claim := (6, [0x5018000000000000000000001403a000000000007018000000000000000000001c03a000000, 0x10010880100000000000000001005c380380000000000000000000000000000000001c38038000, 0x4007398000000000000000000401ddba000000000007398000000000000000000001ddba000000, 0x700421000000000000000000070109120100000070000000000000000000000007000000000000, 0x700739803000000000000000000010200200000070073980300000000000000000000000000000, 0xffafffd67feffffffffffffffffaffe6cdfcffff000007000000000000000000000001c000000000])
def claim55 : Claim := (6, [0x1008480a0000802c100b00000402c140da800000000000000000002c000b00000002c000da8, 0x8020200400040002400080000000000000000000982c28060004c002d800c00006001040000, 0x802220440004c02ed80bc0000000080040400000000000000004c02ed80bc00000000000000, 0x902828060004802a500a80000402804002800000982c28060004c02ed80bc0000602d040028, 0x980368000004c0085802000006008d4008800000980368000004c0005800000006000d40000, 0x982f686e00040022400880000002000082000000982f686e000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000982c00000004c02e800000000602d000000])
def claim56 : Claim := (6, [0x120500000500e800000000000000000000000000160500000700e800000000000000, 0x1000000010021100000170e001000000038000000000000000000000000070e000000000038000, 0x800000004016b500000776e80000000000000000000000000016b500000776e800000000000000, 0xb00000000016b500000020400300000001000000b00000000016b5000000000003000000000000, 0xb000000070108400000444880000000002000000b0000000700000000000000000000000000000, 0xff6fffffffafff6affffff9b37fefffffffcffff0000000000001600000007000000000000000000])
def claim57 : Claim := (6, [0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0x8022000100000200500020000000000000000000b03ac0019800428076003040000, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim58 : Claim := (6, [0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x80400000404084000000040800000000000000009850000058609d800000050c01820000001000, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim59 : Claim := (6, [0x4a800000000004f40000000000000000000000006a800000000006f40000000000, 0x108840000800380f02000e000000000000000000000000000000380700000e00000, 0x84234000000012425a000400000000000000000000034000000000001a000000000, 0xd6aa000000003b6f500000000000000000000000d6a8000000003b6f40000000000, 0xd6ab400028002004000008000000000000000000d6ab40002800000000000000000, 0xfffffffffffff6fd5bffff7ffcdf9adfff3fffff0000000000000068000000000006800000000000])
def claim60 : Claim := (6, [0x1090088010a0000000000000010a1a34034b700000000000000000000000000000001a34034b70, 0x402021000000000000000000040401020000000058302dc0182000000000000005860143001000, 0x42202dc0020000000000000004241b770001020000002dc0000000000000000000001b77000000, 0x503029801020000000000000050619320300300058302dc0182000000000000005861b77035030, 0x5bb02100000000000000000005be0912010210005bb00000000000000000000005be0000000000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd1ffc8fff4cd0058002c00180000000000000005801b40035000])
def claim61 : Claim := (6, [0x46404f400000000000000000000000000000000056406f4000000000000000000000000000, 0x84780f0000040000800000002000e000000000000038070000000000000000000000e00000, 0x842224440005400068000000000008000000000000000000000540006800000000000000000, 0xad65002000054000000000000a00040000000000ad64000000054000000000000a000000000, 0xad67b6f400040000400000000000000000000000ad67b6f4000000000000000000000000000, 0xfffff77d8df9bfffbbfffb7fffffffdfff3fffff0000005400680000000000000000000000000000])
def claim62 : Claim := (6, [0x120500000500e8000000000000000000000000001a0700000500e800000000000000, 0x1008000020108038100e000004038000000000000000000000000038000e000000038000000, 0x80200001a076803b500e8000000000000000000000000001a076803b500e800000000000000, 0xd0000001a0068008500200001400800000000000d0000001a00680005000000014000000000, 0xd038000100440022400880000002000000000000d0380000000000000000000000000000000, 0xfffff6fd7fffffffb7fd5aff57ffffbfd7ffffff0000000000001a07000000000000000000000000])
def claim63 : Claim := (6, [0x2110000013870490a000015c6d8000000000000000000000038700000000001c6d8, 0x420000002020012000000082000000000000000073980000383041b8200000c3000, 0x63100000332601b0200000da0180000000000000739800003bb741b8200000df018, 0x7200000039222da000000bca08800000000000007000000038002d8000000bc0000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000380000003b000380000001f000])
def claim64 : Claim := (6, [0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x210012000000000000000000080800820000000039cc1b8200000000000000000e0c10c3000, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim65 : Claim := (6, [0x46404f400000000000000000000000000000000067404f4000000000000000000000000000, 0xf0004400f0008800000000000f000000000000007000000070000000000000000700000000000, 0x844042004440ce80000000000040000000000000000000000000ce800000000000000000000000, 0xc90064004900c800000000000490000000000000c80064004800c8000000000004800000000000, 0xcf6067404f408400000000000000000000000000cf6067404f4000000000000000000000000000, 0xff72bfffffb2bf737fffffffffff2fffffffffff0000006740000000000000000000000000000000])
def claim66 : Claim := (3, [0x4000000040040000000008000000000000000000500000006005000000000800020000000000, 0x40000000400500000000c800000000000000000000000000000500000000c800000000000000, 0x5000000060040000000088000000000000200000500000006000000000000000000000000000, 0xffffffffffff9fffffffffff77ffffffffffffdf0000500000000005000000000000020000000000])
def claim67 : Claim := (3, [0x200500020000000000000000000000000000000028074002040000, 0x2005401a000000000000000000000000000000000001401a000000, 0x280700120000100000000000000000000000000028060000000000, 0xfffffffffffffffffffffffffffff9ffedffffef0000000000000000000000000028014000040000])
def claim68 : Claim := (3, [0x802000000004000200000000000000000000000090280000000480020000000004000000000, 0x802000000004802a000000000000000000000000000000000004802a0000000000000000000, 0x902800000004002200000000000200000000000090280000000000000000000000000000000, 0xfffffffd7ffffffffffddfffffffffffdfffffff0000090000000000480000000000004000000000])
def claim69 : Claim := (6, [0x40001000000004000f000000000000000000000000000000000000000f00, 0x2003800000020003700000000400360001000000000380000000000370000000000036000000, 0x40020000400700037000d800000000000400000000000000000700037000d800000000000000, 0x6003000040060000300008000400020000000000700380006007000030000800060002000000, 0x7003800060040002200088000000200008200000700380006000000000000000000000000000, 0xfffffffd7fff9ffffffd9fff67ffffffdbfff2df0000700000000007000000000000060000000000])
def claim70 : Claim := (6, [0x81000000000004cc00000000000000000000000000000000000000cc0, 0x17000000000025e00000000000ae04000000000007000000000005e000000000002e000, 0x24040000000075eb80000000000040000000000000000000000075eb800000000000000, 0x36040000000060608000000000820000000000003f060000000070608000000000c2000, 0x3f060000000044488000000000208200000000003f06000000000000000000000000000, 0xffffffffffaf9fffffffffb367fffffffffdb39f00000000038000000000070000000000000c0000])
def claim71 : Claim := (6, [0x2040043c000000000000000000000000000000000000003c0, 0x17008f8009e0400000000000000000000000000007000f8001e000, 0x2405cf9e000100000000000000000000000000000001cf9e000000, 0x36058182082000000000000000000000000000003f07c1820c2000, 0x3f070912010210000000000000000000000000003f060000000000, 0xfffffffffffffffffffffffffffaf9f4e9febcaf000000000000000000000000003801c0000c0000])
def claim72 : Claim := (3, [0x800000004000800000000400000000000000000090000000500090000000040001000000000000, 0x800000004000900000006400000000000000000000000000000090000000640000000000000000, 0x900000005000800000004400000000000200000090000000500000000000000000000000000000, 0xffffffffffafffffffffffbbfffffffffffdffff0090000000000090000000000001000000000000])
def claim73 : Claim := (3, [0x8022000100000000000000000000000000000000a03280011000000000000000000, 0x8022801900000000000000000000000000000000000280190000000000000000000, 0xa032001100040000000000000000000000000000a03000000000000000000000000, 0xfffffffffffffffcfffeefffbfffffffffffffff0000000000000a00280001000000000000000000])
def claim74 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000, 0xffffffb57faf9ffffddddfbb77ffffefdffdffdf0ff07f0003801ef778000700003f07c0000c0000])
def claim75 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000, 0xffffffffffffffacfeeeefdfbffaf9f6edfeffef0ff07f7b83f07e0078000700003801c0000c0000])
def claim76 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff07f7b83f07ef763333464c83f0719320300300ff07f7b83f07ef700000000003f060000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000])
def claim77 : Claim := (6, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim78 : Claim := (6, [0x109000001080110000006800010a0000034e400000000000000000000000680000000000034e40, 0x8440000044009d8000006d0000400000000404000000000000009d8000006d0000000000000000, 0x90500000500095000000640001020000030000009850000058009d8000006d0001820000035000, 0x9dd0000000009d800000200001da0000010200009dd0000000009d800000000001da0000000000, 0x9dd000005d8084000000440000000000020800009dd000005d8000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffffffb5fffffff1fb00980000005800980000006d0001800000035000])
def claim79 : Claim := (6, [0x2010801c100704008000010078000000000000000000001c0007000000000000780, 0xa032801910060000000000000000000000000000b03ac01d9807400000000000000, 0xb002c0081802340000000d000800000000000000b002c0001800340000000d00000, 0xb03a001100043406800000002000000000000000b03800000000340680000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89bfb7ffff6ff97b00000000000000002c01d8000000000000000000])
def claim80 : Claim := (6, [0x1090088010a000000000000001081a00034b400000000000000000000000000000001a00034b40, 0x42202dc0020000000000000004201b400001020000002dc0000000000000000000001b40000000, 0x503029801020000000000000050019000300000058302dc0182000000000000005801b40035000, 0x5bb02100000000000000000005b80900010200005bb00000000000000000000005b80000000000, 0x5bb02dc01ba000000000000000001000020800005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd7fffffff4fd0058002c00180000000000000005801b40035000])
def claim81 : Claim := (6, [0x6003000040060000300008000400020000000000600340004006800038000c00040003000000, 0x422067400200420034380000042401430000020000006740000000003438000000000143000000, 0x844042004440ce803438050c0040000000000400000000000000ce803438050c00000000000000, 0xc06063004040c600303004080404010200000000c86067404840ce803438050c04840143001000, 0xcf6021000000ce801010000004f4010200000000cf6000000000ce800000000004f40000000000, 0xcf6067404f408400202004080000000000000000cf6067404f4000000000000000000000000000, 0xfff99ffcbff9bff97fffc7fff3ff9bfffcfffff900c80064004800c8003400050004800140001000])
def claim82 : Claim := (3, [0x4000000000040000000000000000000000000000500000000005000000000000020000000000, 0x40000000000500000000c000000000000000000000000000000500000000c000000000000000, 0x5000000000040000000080000000000000200000500000000000000000000000000000000000, 0xffffffffffffffffffffffff7fffffffffffffdf0000500000000005000000000000020000000000])
def claim83 : Claim := (3, [0x40001000000000000000000000000000000000004800140001000, 0x42001400000020000000000000000000000000000000140000000, 0x4b001000000000000000000000000000000000004b00000000000, 0xffffffffffffffffffffffffffffdffffffffffd0000000000000000000000000004800140001000])
def claim84 : Claim := (3, [0xa000000000000000000000000000000000000000f000, 0x10c0c0000000000000000000000000000000000000c0c0, 0x30a0800000000000000000000000000000000000300000, 0xffffffffffffffffffffffffffffffffffefff7f000000000000000000000000000000000000f000])
def claim85 : Claim := (7, [0xbb05000000016b500000000001b0200000000000bb85000000017bd80000000001b820000000000, 0x11109000040082110000000000490a0000100e800000000000000000000000000000000000000e80, 0x22b90000000004b800000000009390000000000000b80000000000b8000000000003800000000000, 0xbb200000240017200000000002da000000900080bb000000240017000000000002d8000000900000, 0xbbbdd000000017bd8000000002dbda0000000200bbbdd000000017bd8000000002dbda0000000000, 0xbbbdd00024049084000000000000000000000800bbbdd00024048000000000000000000000000000, 0xccc66ffffbff7fffffffffffff2465ffffeff57f00000000000017bd800000000000000000000000])
def claim86 : Claim := (7, [0x770373981b02000000000000000000000000000077837bdc1b82000000000000000000000000000, 0x111091088490a000000000000040080000100b800000000000000000000000000000000000000b80, 0x2279023c093900000000000000000000000000000078003c00380000000000000000000000000000, 0x772007901da00000000000000140000000500080770007801d800000000000000140000000500000, 0x777bb42100000000000000000140280000000200777bb00000000000000000000140280000000000, 0x777bb7bdddbba000000000000000000000000800777bb7bdddbba000000000000000000000000000, 0xccc66ffff2465fffffffffffffbff7ffffeff57f000007bdc0000000000000000000000000000000])
def claim87 : Claim := (7, [0x2e00270016004e010380206001600818008200000f00078007000f0003800060007000180002000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000])
def claim88 : Claim := (6, [0x1000000000000e000000000000000000000000000000000000000e40, 0x8000000080008000000091000800000005e400000000000000000000000000000000000000e40, 0x800000004000980000006dd00000000000040000000000000000980000006dd000000000000000, 0x880000004800880000000500008000000010000098000000580098000000050001800000001000, 0x980000005800800000004480000000000208200098000000580000000000000000000000000000, 0xffffffffffa7ffffffffffb26ffffffffffda39f0098000000000098000000000001800000000000])
def claim89 : Claim := (6, [0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb7ffffffb7fff7fffffffebffb7fffffff1fb009850000058609d8000006ddc01820000035030])
def claim90 : Claim := (6, [0x842341c1800012425a1c34000020000000000000000341c1800000001a1c3000000, 0xc623018120200360581820820000000000000000d6ab41c1a83043685a1c3083000, 0xd203408028203b201a080e820000000000000000d003400028003b001a000e80000, 0xd6aa010100003b6f501020000000000000000000d6a8000000003b6f40000000000, 0xd6ab41c1a8306004000008000040000000000000d6ab41c1a830400000000000000, 0xfffffffffffff6fd5bffe77ff8df9adffc3ffff90000000000000068001c000300068001c0003000, 0xfffffffffffffeff7bfff77ff8ff9fdffe3ffff90000000000000d6ab41c1a83043685a1c3083000])
def claim91 : Claim := (6, [0x10004808000080001000000004000140d800000000000000000000000000000000000000d80, 0x800220400004c000580000000000080040400000000000000004c0005800000000000000000, 0x9000280000048000500000000400004000000000980028000004c0005800000006000040000, 0x980368000004c0005800000006000d4008000000980368000004c0005800000006000d40000, 0x980368680004000040000000000000008000000098036868000000000000000000000000000, 0xffffffffd97b7ffffffffa7fffffffffff6bf37b00000980000000004c0000000000006000000000])
def claim92 : Claim := (6, [0x100848080000802c100000000402c140d8000000000000000000002c000000000002c000d80, 0x802220400004c02ed80000000000080040400000000000000004c02ed800000000000000000, 0x902828000004802a500000000402804000000000982c28000004c02ed80000000602d040000, 0x980368000004c0085800000006008d4008000000980368000004c0005800000006000d40000, 0x982f686800040022400000000002000080000000982f6868000000000000000000000000000, 0xffffffffd97b7ffffffffa7fffffffffff6bf37b00000982c00000004c02e800000000602d000000])
def claim93 : Claim := (6, [0xd000000000068008000000001400800000000000d0000000000680000000000014000000000, 0x2d03800000026803b000000005403a00000000000d03800000006803b000000001403a000000, 0x4802000040076803b000c80000000000000000000000000000076803b000c800000000000000, 0x6c030000400660003000080005000200000000007d0380006007680030000800074002000000, 0x7d038000600440022000880000002000002000007d0380006000000000000000000000000000, 0xfffff6fd7fff9fffb7fd5fff77ffffbfd7ffffdf0000700000000007000000000000060000000000])
def claim94 : Claim := (6, [0x109000000080110000000000010a0000000e400000000000000000000000000000000000000e40, 0x8440000004009d800000000000400000000404000000000000009d800000000000000000000000, 0x90500000000095000000000001020000000000009850000000009d800000000001820000000000, 0x9dd0000000009d800000000001da0000000200009dd0000000009d800000000001da0000000000, 0x9dd00000058084000000000000000000000800009dd00000058000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffffffb5fffffff1fb0098000000000098000000000001800000000000])
def claim95 : Claim := (3, [0x2001000000000000000000000400020000000000300180002000000000000000060002000000, 0x2001800000000000000000000400320000000000000180000000000000000000000032000000, 0x3001800020000000000000000000200000200000300180002000000000000000000000000000, 0xffffffff7fffdfffffffffffffffffffdfffffdf0000300000000000000000000000060000000000])
def claim96 : Claim := (6, [0x2010801c100704808400014078000000000000000000001c0007000000000000780, 0xa032801910060280140000400000000000000000b03ac01d9807428016000040000, 0xb002c0081802368016000d400800000000000000b002c0001800368016000d40000, 0xb03a001100043686900000002000000000000000b03800000000368680000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b7ffff6bf97b00000000000000002c01d8000000016000000000])
def claim97 : Claim := (6, [0x1a006800850020000000000000000000000000001a00680005000000000000000000, 0x2003800008026803b000000004003200000000000003800000006803b0000000000032000000, 0x400200005a076803b500e8000000000000000000000000001a076803b500e800000000000000, 0x6003000058066000340008000400020000000000700380007a07680035000800060002000000, 0x7003800070044002240088000000200000200000700380006000000000000000000000000000, 0xfffffffd7fff9fffb7fd5aff57ffffffdfffffdf0000700000001a07000000000000060000000000])
def claim98 : Claim := (6, [0x1090088010a000000000000000080000000b400000000000000000000000000000000000000b40, 0x42202dc00200000000000000002000000001020000002dc0000000000000000000000000000000, 0x503029801020000000000000000000000000000058302dc0182000000000000000000000000000, 0x5bb02100000000000000000000380000000200005bb00000000000000000000000380000000000, 0x5bb02dc01ba000000000000000000000000800005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd7fffffff4fd0058002c00180000000000000000000000000000])
def claim99 : Claim := (6, [0x2000800010000480840001407800000000000000000000000000000000000000780, 0xa002800010000280140000400000000000000000b002c0001800028016000040000, 0xb002000000003686900000002000000000000000b00000000000368680000000000, 0xb002c00018002004000008004040000000000000b002c0001800000000000000000, 0xb002c0001800368016000d400800000000000000b002c0001800368016000d40000, 0xfffffffffffffcfffffffe7ffdb7b7ffff6bf97b00000000000000002c0000000000016000000000])
def claim100 : Claim := (3, [0x800000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000080])
def claim101 : Claim := (3, [0x8002000000000200100000000000000000000000900240000800020012000000000, 0x9002000000003200100000000000000000000000900000000000320000000000000, 0x9002400008002000000008000000000000000000900240000800000000000000000, 0xfffffffffffffeffffffff7ffdffffffff7fffff0000000000000000240000000000012000000000])
def claim102 : Claim := (6, [0x8000000000000000000000000d000000000000000000000000000000000000000d80, 0x10004808000080001000000004000140d800000000000000000000000000000000000000d80, 0x800220400004c000580000000000080040400000000000000004c0005800000000000000000, 0x9000280000048000500000000400004000000000980028000004c0005800000006000040000, 0x980368680004000040000000000000008000000098036868000000000000000000000000000, 0xffffffffd97b7ffffffffa7fffffffffff6bf37b00000980000000004c0000000000006000000000])
def claim103 : Claim := (6, [0x28000000000022000000000002000000000000002c00000000002e800000000002d000000, 0x8074000000040048800000002005d000000000000034000000000000000000000000d00000, 0x802220000004c02ed80000000000080000000000000000000004c02ed800000000000000000, 0x982d00000004c02e800000000602d40000000000982c00000004c02e800000000602d000000, 0x982f680000040022400000000002000000000000982f6800000000000000000000000000000, 0xfffff77d8dffffffbbffd37fffffffdffe3fffff00000000000000000002c000000000002c000000])
def claim104 : Claim := (6, [0x300011000400000000000000000000000000000038001d8007400000000000000, 0x100840048801740002000d000000000000000000000000000000340000000d00000, 0x8022c01d800012001600040000000000000000000002c01d8000000016000000000, 0xb03a001100043680100000000000000000000000b03800000000368000000000000, 0xb03ac01d98076000000008000000000000000000b03ac01d9807400000000000000, 0xfffffffffffff6fd5bffe77ff8dffedfff3fffff00000000000000000001c0007000000000000000])
def claim105 : Claim := (6, [0x50600000000044880000000002002000000000007860000000005fbc0000000002f028, 0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim106 : Claim := (6, [0x50609120100100000000000000000000000000007860fdf01f018, 0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim107 : Claim := (3, [0x80, 0xffffffffffffffffffffffffffffffffffffff7f0000000000000000000000000000000000000000])
def claim108 : Claim := (6, [0x1088490a00000000000000000562c1009c0000000000000000000000000000000162c0009c0, 0x31881b0200000000000000000d4a80000000000039cc1b8200000000000000000f6ed000000, 0x3901da0000000000000000000e488700080000003801d80000000000000000000e000700000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200008000000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2aff67d0000001c003800000000000000000016c0000000])
def claim109 : Claim := (3, [0x40000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000004000000000000000000000])
def claim110 : Claim := (3, [0x21000000000000000000000008080000000000003188000000000000000000000c080000000, 0x218000000000000000000000094800000000000001800000000000000000000001480000000, 0x318800000000000000000000010200000000000031880000000000000000000000000000000, 0xfffffff77fffffffffffffffffffffefdfffffff000003000000000000000000000000c000000000])
def claim111 : Claim := (6, [0x2110000013870490a000015c6d8000000000000000000000038700000000001c6d8, 0x63100000332601b0200000da0180000000000000739800003bb741b8200000df018, 0x7200000039222da000000bca08800000000000007000000038002d8000000bc0000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000380000003b000380000001f000])
def claim112 : Claim := (3, [0x4200000020200000000000000000000000000000631000003020000000000000000, 0x4300000023200000000000000000000000000000030000000320000000000000000, 0x6310000002040000000000000000000000000000631000000000000000000000000, 0xffffffffffffffeeffffffdfbfffffffffffffff0000000000000600000003000000000000000000])
def claim113 : Claim := (6, [0x36040000000060608000000000820000000000003684000000006870c00000000083000, 0x84222444000542c2e870c000000008000040000000000000000542c2e870c00000000000000, 0xa520360400050282606080000808008200000000ad643684000542c2e870c0000a0c1083000, 0xa903b20000054080682000000a080e8200000000a803b00000054000680000000a000e80000, 0xad650020000542c2800000000a0c140000200000ad640000000542c2800000000a0c1000000, 0xad67b6f400040202404080000000000000000000ad67b6f4000000000000000000000000000, 0xfffff77d8df9bfffbbffd37ff3ffffdffe3ffff90000005400680000002c000700000000c0003000])
def claim114 : Claim := (3, [0x800000000004000000000000000000000000000088000000000440000000000002000000000, 0x800200000004400000000000000008000000000000000000000440000000000000000000000, 0x880300000004000000000000000000000000000088030000000000000000000000000000000, 0xffffffffdfffffffffffffffffffffffff7fffff0000088000000000440000000000002000000000])
def claim115 : Claim := (3, [0x8080000000000000000000000000000000000000a0c1000000, 0xa080600000000000000000000000000000000000a000600000, 0xa0c1400002000000000000000000000000000000a0c1000000, 0xffffffffffffffffffffffffffffffdffebffffd00000000000000000000000000000000c0000000])
def claim116 : Claim := (7, [0xd000d0002801a006800050000280140000400000d000d8002801b006c0005800028016000040000, 0x1100810004808200080001000048084000140e800000000000000000000000000000000000000e80, 0x44000d80100008006c000000012001600040000000000d80000000006c0000000000016000000000, 0xaaff7a7feb7f7ffffffffffffe97f69fffabf57f0000000000001b006c0005800000000000000000, 0xdd000d8036801b006c0005800368016000d40080dd000d8036801b006c0005800368016000d40000, 0xdd04840000001b00200000000368490000000200dd04800000001b00000000000368480000000000, 0xdd048d8036849000400004000000000000000800dd048d8036848000000000000000000000000000])
def claim117 : Claim := (7, [0x770373981b02000000000000000000000000000077837bdc1b82000000000000000000000000000, 0x111091088490a000000000000040080000100ac00000000000000000000000000000000000000ac0, 0x444227bdd0020000000000000000000000000000000007bdc0000000000000000000000000000000, 0x772007901da000000000000000c0000000300080770007801d8000000000000000c0000000300000, 0x777bb421000000000000000000c0180000000200777bb000000000000000000000c0180000000000, 0x777bb7bdddbba000000000000000000000000800777bb7bdddbba000000000000000000000000000, 0xaafd4a7e2b7d5fffffffffffffbff7ffffeff57f0078003c00380000000000000000000000000000])
def claim118 : Claim := (3, [0x4000000000000000000000, 0xffffffffffffffffffbfffffffffffffffffffff0000000000000000000000000000000000000000])
def claim119 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402e730000084270383000002405818200000000000f7b8000000078383000000001c182000000, 0x880484202405ef77bbbb776e8000000000000000000000000001ef77bbbb776e800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000])
def claim120 : Claim := (6, [0x48c000000000000000000000000000000000000009c0, 0x84400000000000000000000022450049c000000000000000000000000000000000000009c0, 0x21c000000000000000000000096c002c0400000001c000000000000000000000016c002c000, 0x2944000000000000000000000a0c10000000000039cc000000000000000000000e0c1000000, 0x39cc00000000000000000000010200208200000039cc0000000000000000000000000000000, 0xfffffff33fffffffffffffffffffffed9afdb69f000003800000000000000000000000e000000000])
def claim121 : Claim := (6, [0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd1b2200000000000000000f6ed4ea12a0000039cc1b8200000000000000000f6ed0ef028, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim122 : Claim := (6, [0x842341c1800012425a1c34000020000000000000000341c1800000001a1c3000000, 0xc623018120200360581820820000000000000000d6ab41c1a83043685a1c3083000, 0xc62341c1a02013625a1c34820020000000000000d6ab41c1a83043685a1c3083000, 0xd203408028203b201a080e820000000000000000d003400028003b001a000e80000, 0xd6aa010100003b6f501020000000000000000000d6a8000000003b6f40000000000, 0xd6ab41c1a8306004000008000040000000000000d6ab41c1a830400000000000000, 0xfffffffffffff6fd5bffe77ff8df9adffc3ffff90000000000000068001c000300068001c0003000])
def claim123 : Claim := (3, [0x200100000000000000000000000000000000000028014000040000, 0x200140180000000000000000000000000000000000014018000000, 0x280100100000100000000000000000000000000028000000000000, 0xffffffffffffffffffffffffffffffffefffffef0000000000000000000000000028014000040000])
def claim124 : Claim := (6, [0x800000024040b000000776a80000000000000000000000000000b000000776a800000000000000, 0xa00000036040a000000606080200000008200000b0000003f060b00000070608030000000c2000, 0xb00000000000b000000020000300000001000000b00000000000b0000000000003000000000000, 0xb00000017000b00000027600030000000ba00000b00000007000b000000076000300000003a000, 0xb0000003f0608000000444880000000002002000b0000003f06000000000000000000000000000, 0xff6fffffffaf9f6fffffff9b77fefffffffcffdf00000000038000000000070000000000000c0000])
def claim125 : Claim := (6, [0x2110000013870490a00001006c000000000000000000000003870000000000006c0, 0x63100000332601b0200000000000000000000000739800003bb741b820000000000, 0x7200000039222da000000b0008000000000000007000000038002d8000000b00000, 0x7398000002042dbda000000020000000000000007398000000002dbda0000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6ff97b00000000000000380000003b0003800000000000])
def claim126 : Claim := (6, [0x16b500000020400000000000000000000000000016b5000000000000000000000000, 0x17004b00000027600000000000aa00000000000007000b000000076000000000002a000, 0x24056b500000776e80000000000000000000000000016b500000776e800000000000000, 0x36054a40000060608000000000820000000000003f076b50000070608000000000c2000, 0x3f070840000044488000000000200200000000003f06000000000000000000000000000, 0xffffffffffaf9f6affffff9b37fffffffffdffdf00000000038016000000070000000000000c0000])
def claim127 : Claim := (6, [0x2110000000000490a00001006c000000000000000000000000000000000000006c0, 0x63100000000001b020000000000000000000000073980000000001b820000000000, 0x7200000000002da000000b0008000000000000007000000000002d8000000b00000, 0x7398000000002004000008004040000000000000739800000000000000000000000, 0x7398000000002dbda000000020000000000000007398000000002dbda0000000000, 0xfffffffffffffcfe7ffffffffdb7b5ffff6ff97b0000000000000038000000000003800000000000])
def claim128 : Claim := (3, [0x2000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000200])
def claim129 : Claim := (3, [0x80400000000084000000000000000000000000008840000000008c800000000000800000000000, 0x8440000000008c800000000000400000000000000000000000008c800000000000000000000000, 0x8d400000000084000000000000000000000000008d400000000000000000000000000000000000, 0xfffbbffffffffffb7fffffffffffbfffffffffff0088000000000088000000000000800000000000])
def claim130 : Claim := (6, [0x8000000000000000000000000c400000000000000000000000000000000000000e40, 0x109000000080110000000000010a0000000e400000000000000000000000000000000000000e40, 0x8440000004009d800000000000400000000404000000000000009d800000000000000000000000, 0x90500000000095000000000001020000000000009850000000009d800000000001820000000000, 0x9dd00000058084000000000000000000000800009dd00000058000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffffffb5fffffff1fb0098000000000098000000000001800000000000])
def claim131 : Claim := (6, [0x4d000000000058000000000004a00000000000005d000000000058000000000005a0000000000, 0x109000001000110000006800010a00000340000000000000000000000000680000000000034000, 0x8440000040009d8000006d0000400000000000000000000000009d8000006d0000000000000000, 0x9dd00000580084000000440000000000020000009dd00000580000000000000000000000000000, 0xff6fafffffafff6affffff9bfffefdfffffcffff0005800000000000000000000000580000000000, 0xffffffffffafffffffffffbbfffffffffffdffff009dd0000000009d800000000001da0000000000])
def claim132 : Claim := (6, [0x31220000000000000000000000000000000000003bb7400000000000000, 0x1088000008916c0d8000000000000000000000000000000000002c0580000000000, 0x4380000023b009390000000000000000000000000380000003b0003800000000000, 0x7200000039222da00000000000000000000000007000000038002d8000000000000, 0x739800003bb76004000000000000000000000000739800003bb7400000000000000, 0xfffffffffffffad77ffffd7cf96d2fffffffffff0000000000000000000000387000000000000000])
def claim133 : Claim := (6, [0x28000600000022000880000002000002000000003c000600000037800dc00000037000030, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim134 : Claim := (6, [0xc4880ca008000000000000000000000000000001efdf0df018, 0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim135 : Claim := (6, [0x1088490a0000000000000000000001009c000000000000000000000000000000000000009c0, 0x31881b020000000000000000000000000000000039cc1b82000000000000000000000000000, 0x3901da00000000000000000000000700080000003801d800000000000000000000000700000, 0x39cd00200000000000000000000004001020000039cc0000000000000000000000000000000, 0x39cddbba0000000000000000000000008000000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffffffffaff67d0000001c00380000000000000000000000000000])
def claim136 : Claim := (3, [0x200, 0xfffffffffffffffffffffffffffffffffffffdff0000000000000000000000000000000000000000])
def claim137 : Claim := (3, [0x400020000000000000000000040001000000000050002800100000000000000005000100000000, 0x400028000000000000000000040019000000000000002800000000000000000000001900000000, 0x500028001000000000000000000010000200000050002800100000000000000000000000000000, 0xfffffff7ffefffffffffffffffffffeffffdffff0050000000000000000000000005000000000000])
def claim138 : Claim := (6, [0x36058182082000000000000000000000000000003685a1c3083000, 0x842341c1800012425a1c34000020000000000000000341c1800000001a1c3000000, 0xc623018120200360581820820000000000000000d6ab41c1a83043685a1c3083000, 0xd203408028203b201a080e820000000000000000d003400028003b001a000e80000, 0xd6aa010100003b6f501020000000000000000000d6a8000000003b6f40000000000, 0xd6ab41c1a8306004000008000040000000000000d6ab41c1a830400000000000000, 0xfffffffffffff6fd5bffe77ff8df9adffc3ffff90000000000000068001c000300068001c0003000])
def claim139 : Claim := (3, [0x4200000000000000000000000000000000000000631000000000000000000000000, 0x4300000003000000000000000000000000000000030000000300000000000000000, 0x6310000002040000000000000000000000000000631000000000000000000000000, 0xffffffffffffffeeffffffdfbfffffffffffffff0000000000000600000000000000000000000000])
def claim140 : Claim := (3, [0x8002000000000000000000000000000000000000900240000800000000000000000, 0x9002000000003000000000000000000000000000900000000000300000000000000, 0x9002400008002000000008000000000000000000900240000800000000000000000, 0xfffffffffffffeffffffff7ffdffffffff7fffff0000000000000000240000000000000000000000])
def claim141 : Claim := (7, [0xd000d0002801a006800050000280140000400000d000d8002801b006c0005800028016000040000, 0x1100810004808200080001000048084000140b800000000000000000000000000000000000000b80, 0x66ff7fffd97f6cfffffffa7ffdb7f7ffff6bf57f00000d80000000006c0000000000016000000000, 0x8800080022001b006c00058002000000008000000000000000001b006c0005800000000000000000, 0xdd000d8036801b006c0005800368016000d40080dd000d8036801b006c0005800368016000d40000, 0xdd02840000001b00200000000368290000000200dd02800000001b00000000000368280000000000, 0xdd028d8036829000400004000000000000000800dd028d8036828000000000000000000000000000])
def claim142 : Claim := (7, [0xbb05000000016b500000000001b0200000000000bb85000000017bd80000000001b820000000000, 0x11109000040082110000000000490a0000100ac00000000000000000000000000000000000000ac0, 0x66fb2ffffbff6cfa7ffffffffdb7b5ffffeff57f00b80000000000b8000000000003800000000000, 0x88844000000017bd80000000020040000000000000000000000017bd800000000000000000000000, 0xbb2000000c0017200000000002da000000300080bb0000000c0017000000000002d8000000300000, 0xbbbdd000000017bd8000000002dbda0000000200bbbdd000000017bd8000000002dbda0000000000, 0xbbbdd0000c019084000000000000000000000800bbbdd0000c018000000000000000000000000000])
def claim143 : Claim := (7, [0x2f00278017004f013b802760017009d800ba00000f00078007000f003b800760007001d8003a000, 0x4402f7b800008427bbbb000002405ddba00000000000f7b800000007bbbb000000001ddba000000, 0x880484202405ce67038360608000000000000000000000000001ef7783837060800000000000000, 0xee06e7303605ce67038360608360581820820000ff07f7b83f07ef778383706083f07c1820c2000, 0xff0742100001ef721111020403f0709120100100ff0700000001ef700000000003f060000000000, 0xff07f7b83f070844222244488000010200200200ff07f7b83f06000000000000000000000000000, 0xff2f8f947faf9f28fccccf9b37faf9e6cdfcffcf0f000f0003801e0078000700003801c0000c0000])
def claim144 : Claim := (6, [0x40003800000000000000000000000000000000000000780, 0x1008400488014000000040007800000000000000000000000000000000000000780, 0x8022c01d800000000001c00010000000000000000002c01d800000000001c000000, 0x902a400188004000000000000000000000000000b03ac0019800400000000000000, 0xb03a001100040000000100002100000000000000b03800000000000000000000000, 0xfffffffffffffffc7ffea7ffabffffffebfff8ef0000000000000b002c0001800000000000000000])
def claim145 : Claim := (6, [0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d980762847401a84041c0000000000000b03ac01d980742807601f040018, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim146 : Claim := (6, [0x422067400200420034380000042401430000020000006740000000003438000000000143000000, 0x844042004440ce803438050c0040000000000400000000000000ce803438050c00000000000000, 0xc06063004040c600303004080404010200000000c86067404840ce803438050c04840143001000, 0xc46063004440ce803438050c0444010200000400c86067404840ce803438050c04840143001000, 0xcf6021000000ce801010000004f4010200000000cf6000000000ce800000000004f40000000000, 0xcf6067404f408400202004080000000000000000cf6067404f4000000000000000000000000000, 0xfff99ffcbff9bff97fffc7fff3ff9bfffcfffff900c80064004800c8003400050004800140001000])
def claim147 : Claim := (6, [0x4000380000000000000000002405dd9a000000000000380000000000000000000001dd9a000000, 0x60003000200000000000000036058182082000007000380030000000000000003f07c1820c2000, 0x7000200000000000000000003f070912010010007000000000000000000000003f060000000000, 0x700038003000000000000000000010000200000070003800300000000000000000000000000000, 0x70003800300000000000000017009d800ba0000070003800300000000000000007001d8003a000, 0xffafffd7ffeffffffffffffffffaf9e6edfcffef000000000000000000000000003801c0000c0000])
def claim148 : Claim := (6, [0x23800000000000000000017009d8009a0000000003800000000000000000007001d8001a000, 0x4210000000000000000003f070912010010000000000000000000000000003f060000000000, 0x63100000000000000000036058182082000000007398000000000000000003f07c1820c2000, 0x739800000000000000000000010200000000000073980000000000000000000000000000000, 0x7398000000000000000002405ddba000000000007398000000000000000000001ddba000000, 0xffffffd67ffffffffffffffffffaf9e6cdfeffef000007000000000000000000003801c0000c0000])
def claim149 : Claim := (3, [0x400000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000040000000000000000000000000000000])
def claim150 : Claim := (3, [0x402021000000000000000000000000000000000048202540080000000000000000000000000000, 0x422025400200000000000000000000000000000000002540000000000000000000000000000000, 0x4b202100000000000000000000000000000000004b200000000000000000000000000000000000, 0xfffddffebffdffffffffffffffffffffffffffff0048002400080000000000000000000000000000])
def claim151 : Claim := (6, [0x1001c000000000000000000000000000000000000009c0, 0x1088490a0000000000000000000001009c000000000000000000000000000000000000009c0, 0x31881b020000000000000000000000000000000039cc1b82000000000000000000000000000, 0x3901da00000000000000000000000700080000003801d800000000000000000000000700000, 0x39cd00200000000000000000000004001020000039cc0000000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffffffffaff67d0000001c00380000000000000000000000000000])
def claim152 : Claim := (6, [0x2b001c002a0000000000000000000000000000003b001c003a000000000000000000000000000, 0x1090088010a000000000000001001a000340000000000000000000000000000000001a00034000, 0x42202dc0020000000000000004001b400000000000002dc0000000000000000000001b40000000, 0x5bb02100000000000000000005800900010000005bb00000000000000000000005800000000000, 0xffafcfd67fefdffffffffffffffaffe6fffcffff0003800000038000000000000000000000000000, 0xfffffffffffffffffffffffffffafff6fffeffff005bb02dc01ba000000000000000000000000000])
def claim153 : Claim := (6, [0xdb9a000000000000000000000000000000000001dbba000000000000000000000000000, 0x1088490a00000000000000000562c000000000000000000000000000000000000162c000000, 0x21c093900000000000000000096c00000000000001c003800000000000000000016c0000000, 0x3901da0000000000000000000e488000000000003801d80000000000000000000e000000000, 0xfffffce77e4fdfffffffffffffffff2b57ffffff000000001c038000000000000000000000000000, 0xffffffffffffffffffffffffffffff3b77ffffff0000039cddbba000000000000000000000000000])
def claim154 : Claim := (6, [0x3000110004000060012000010000000000000000780037800dc00060037000030, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim155 : Claim := (6, [0x31220000000000ca0080000000000000000000007dfbc000000000ef028, 0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim156 : Claim := (3, [0x40000000000000000000000000000000, 0xffffffffbfffffffffffffffffffffffffffffff0000000000000000000000000000000000000000])
def claim157 : Claim := (6, [0x8040000000040048001000002005000d800000000000000000000000000000000000000d80, 0x802000000004c02e800b00000000000040000000000000000004c02e800b000000000000000, 0x8824000000044002800000000200100000000000982c00000004c0028000000006001000000, 0x982c000000040022000800000002000082000000982c0000000000000000000000000000000, 0x982c00000004c02e800000000602d00010000000982c00000004c02e800000000602d000000, 0xfffffffd3ffffffffffd97ff6fffffffdafff2df00000980000000004c0000000000006000000000])
def claim158 : Claim := (6, [0x1008400488014000000040007800000000000000000000000000000000000000780, 0x8022c01d800000000001c00010000000000000000002c01d800000000001c000000, 0x902a400188004000000000000000000000000000b03ac0019800400000000000000, 0xb03a001100040000000100002100000000000000b03800000000000000000000000, 0xb03ac01d98074000000000004000000000000000b03ac01d9807400000000000000, 0xfffffffffffffffc7ffea7ffabffffffebfff8ef0000000000000b002c0001800000000000000000])
def claim159 : Claim := (3, [0x10000000000000000000000000, 0xffffffffffffffefffffffffffffffffffffffff0000000000000000000000000000000000000000])
def claim160 : Claim := (6, [0x8000000080008000000091000800000005e400000000000000000000000000000000000000e40, 0x800000004000980000006dd00000000000040000000000000000980000006dd000000000000000, 0x880000004800880000000500008000000010000098000000580098000000050001800000001000, 0x980000005800800000004480000000000208200098000000580000000000000000000000000000, 0x980000005800980000006d000180000003504000980000005800980000006d0001800000035000, 0xffffffffffa7ffffffffffb26ffffffffffda39f0098000000000098000000000001800000000000])
def claim161 : Claim := (6, [0x844002000440ce800038000c0040000000000400000000000000ce800038000c00000000000000, 0xc06003000040c600003000080404000200000000c86003400040ce800038000c04840003000000, 0xc90000000000c800000000000490000000000000c80000000000c8000000000004800000000000, 0xcf6001000000ce800010000004f4000200000000cf6000000000ce800000000004f40000000000, 0xcf60034006408400002000080000000000000000cf600340064000000000000000000000000000, 0xff72bffffffbbf737ffffffff3ff2ffffffffffb0000000340000000000038000000000003000000])
def claim162 : Claim := (6, [0xd800000080008800000091000d80000005e400005800000000000000000000000580000000e40, 0x8440000040009d8000006dd000400000000400000000000000009d8000006dd000000000000000, 0x8d40000048008c800000050000d00000001000009dd0000058009d800000050001da0000001000, 0x990000005800980000006d000190000003504000980000005800980000006d0001800000035000, 0x9dd00000580084000000448000000000020820009dd00000580000000000000000000000000000, 0xffffffffffa7ffffffffffb26ffffffffffda39f009dd0000000009d800000000001da0000000000])
def claim163 : Claim := (6, [0x8000400080000000000000000800244005b400000000000000000000000000000000000000b40, 0x40002c00000000000000000004001b740001000000002c00000000000000000000001b74000000, 0x480024000800000000000000048001400010000058002c00180000000000000005800140001000, 0x58002c001800000000000000000010200208200058002c00180000000000000000000000000000, 0x58002c00180000000000000005801b400350400058002c00180000000000000005801b40035000, 0xfffffff3ffe7ffffffffffffffffffed9bfda69f0058000000000000000000000005800000000000])
def claim164 : Claim := (6, [0x84404200444006800038000c004000000000040000000000000006800038000c00000000000000, 0xc060630040400600003000080004000200000000c8606740484006800038000c00040003000000, 0xc900640049000000000000000000000000000000c8006400480000000000000000000000000000, 0xcf60210000000680001000000064000200000000cf600000000006800000000000640000000000, 0xcf6067404f400400002000080000000000000000cf6067404f4000000000000000000000000000, 0xff72bfffffb2bffb7ffffffff3ffbffffffffffb0000006740000000000038000000000003000000])
def claim165 : Claim := (6, [0xb8004400b8000000000000000800244005b400003800000038000000000000000000000000b40, 0x42202dc0020000000000000004001b740001000000002dc0000000000000000000001b74000000, 0x4b2025400b0000000000000004800140001000005bb02dc01ba000000000000005800140001000, 0x59002c00190000000000000005801b400350400058002c00180000000000000005801b40035000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffffff33fe45fffffffffffffffffed9bfda69f005bb00000000000000000000005800000000000])
def claim166 : Claim := (3, [0x100000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000010000000000000000000000000])
def claim167 : Claim := (6, [0x44000000000048000000000004000000000000005d000000000058000000000005a0000000000, 0x109000001000110000006800010a00000340000000000000000000000000680000000000034000, 0x8440000040009d8000006d0000400000000000000000000000009d8000006d0000000000000000, 0x9dd0000000009d800000200001da0000010000009dd0000000009d800000000001da0000000000, 0x9dd00000580084000000440000000000020000009dd00000580000000000000000000000000000, 0xff6fafffffafff6affffff9bfffefdfffffcffff0005800000000000000000000000580000000000])
def claim168 : Claim := (6, [0x22001400200000000000000000000000000000003b001c003a000000000000000000000000000, 0x1090088010a000000000000001001a000340000000000000000000000000000000001a00034000, 0x42202dc0020000000000000004001b400000000000002dc0000000000000000000001b40000000, 0x5bb02100000000000000000005800900010000005bb00000000000000000000005800000000000, 0x5bb02dc01ba000000000000000001000020000005bb02dc01ba000000000000000000000000000, 0xffafcfd67fefdffffffffffffffaffe6fffcffff0003800000038000000000000000000000000000])
def claim169 : Claim := (6, [0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000, 0xffffffffddfbbffffffffb7ff3ffffffff7ffffb00000000007800000000005fb00000000002fce8])
def claim170 : Claim := (6, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000, 0xfffffffffffffffffffffffffedfdadffcbffffd0000000000000000000000000007800fdc01f3d8])
def claim171 : Claim := (7, [0x8440000000044448081000002245004d400000000000000000000000000000000000000d40, 0x25c0000000012ec004800000096c00240400000005c0000000002ec004800000016c0024000, 0x842000000005eeee848900000000000040000000000000000005eeee8489000000000000000, 0xad640000000542c2800000000a0c100000000000bdec00000005c2c2800000000e0c1000000, 0xb90000000005c888000000000e48800000000000b80000000005c000000000000e000000000, 0xbdec00000005eeee800000000f6ed00010000000bdec00000005eeee800000000f6ed000000, 0xffffffffffffffffe33337f7efffff1932ffbabf00000bdec0000000000000000000000000000000])
def claim172 : Claim := (7, [0x1088444488914000002040047400000000000000000000000000000000000000740, 0x47811dc023b0000000a00014040000000000000007801dc003b0000000a00014000, 0x8423dddd8000000000a1400010000000000000000003dddd8000000000a14000000, 0xd6ab41c1a8304000000000000000000000000000f7bbc1c1b830400000000000000, 0xf203c88839220000000000000000000000000000f003c0003800000000000000000, 0xf7bbddddbbb74000000000004000000000000000f7bbddddbbb7400000000000000, 0xffffffffffffffffe3333464cbfffffdfbffbabf0000000000000f7b800000000000000000000000])
def claim173 : Claim := (3, [0x10000000000000000000000000000000000, 0xfffffeffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000])
def claim174 : Claim := (7, [0xe200e1003201c207008060200320180800820000e000e8003001d0074000680003001a000080000, 0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim175 : Claim := (6, [0x10001400050000a001400071000000000000000000001c000700000001c000798, 0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000])
def claim176 : Claim := (3, [0x2000000000000200000000000000000000000000240000000000028000000000001000000, 0x2000400000000280000000000000000040000000000000000000028000000000000000000, 0x2400600000000200000000000000000000000000240060000000000000000000000000000, 0xfffffffffffbfffffffffffffffffffffffffffb0000000240000000000028000000000001000000])
def claim177 : Claim := (6, [0x8074000000040048801000002005d00d800000000034000000000000000000000000d00d80, 0x802220000004c02ed80b00000000080040000000000000000004c02ed80b000000000000000, 0x8827200000044002c800000002001c0000000000982f68000004c002d800000006001d40000, 0x982d00000004c02e800000000602d40010000000982c00000004c02e800000000602d000000, 0x982f680000040022400800000002000082000000982f6800000000000000000000000000000, 0xfffffffd3ffffffffffd97ff6fffffffdafff2df00000980368000004c0005800000006000d40000])
def claim178 : Claim := (6, [0x100840048801740002004d007800000000000000000000000000340000000d00780, 0x8022c01d800012001601c40010000000000000000002c01d800000001601c000000, 0x902a40018800720012000c000000000000000000b03ac0019800768016000d40000, 0xb03a001100043680100100002100000000000000b03800000000368000000000000, 0xb03ac01d98076000000008004000000000000000b03ac01d9807400000000000000, 0xfffffffffffffffc7ffea7ffabffffffebfff8ef0000000000000b002c0001800368016000d40000])
def claim179 : Claim := (3, [0x100000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000010000000000000000000000000000000000])
def claim180 : Claim := (6, [0x1090088010a0000000000000010a1a34034b700000000000000000000000000000001a34034b70, 0x42202dc0020000000000000004241b770001020000002dc0000000000000000000001b77000000, 0x503029801020000000000000050619320300300058302dc0182000000000000005861b77035030, 0x5bb02100000000000000000005be0912010210005bb00000000000000000000005be0000000000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd1ffc8fff4cd0058002c00180000000000000005801b40035000])
def claim181 : Claim := (6, [0x6003000040060000300008000400020000000000700380006007000030000800060002000000, 0x4002d03800008026803b000002005403a00000000000d03800000006803b000000001403a000000, 0x800480202005a076803b500e8000000000000000000000000001a076803b500e800000000000000, 0xc006c03020058066000340008200500020000000d007d0382807a07680035000828074002040000, 0xd00740100001a072001100040280700120000100d00700000001a07000000000028060000000000, 0xd007d03828070044002240088000000200000200d007d0382806000000000000000000000000000, 0xffff8ffc7fff9ff8fffccfff37fff9ffcdffffcf0d000d0002801a00680005000028014000040000])
def claim182 : Claim := (3, [0x8002000000000000000000000000000000000000a00280001000000000000000000, 0x8002801800000000000000000000000000000000000280180000000000000000000, 0xa002001000040000000000000000000000000000a00000000000000000000000000, 0xfffffffffffffffffffeffffbfffffffffffffff0000000000000a00280001000000000000000000])
def claim183 : Claim := (6, [0x1088000008914000000000046c000000000000000000000000000000000000006c0, 0x4380000023b000000000001c04000000000000000380000003b000000000001c000, 0x5288000028304000000000000000000000000000739800003830400000000000000, 0x7398000002040000000000102100000000000000739800000000000000000000000, 0x739800003bb74000000000004000000000000000739800003bb7400000000000000, 0xffffffffffffffe67fffffd6abfffffffffeb9af0000000000000700000003800000000000000000])
def claim184 : Claim := (6, [0x80022444000540006870c000000008000040000000000000000540006870c00000000000000, 0xa000360400050000606080000800008200000000a8003684000540006870c0000a000083000, 0xa801000000054000000000000a00040000000000a800000000054000000000000a000000000, 0xa803b20000054000682000000a000e8200000000a803b00000054000680000000a000e80000, 0xa803b6d400040000404080000000000000000000a803b6d4000000000000000000000000000, 0xfffff77fcdfbbfffbbfffb7ff3ffffdfff3ffffb0000000000680000000000070000000000003000])
def claim185 : Claim := (6, [0x84400000000000000000000022450049c000000000000000000000000000000000000009c0, 0x21c000000000000000000000096c002c0400000001c000000000000000000000016c002c000, 0x2944000000000000000000000a0c10000000000039cc000000000000000000000e0c1000000, 0x39cc00000000000000000000010200208200000039cc0000000000000000000000000000000, 0x39cc000000000000000000000f6ed0001000000039cc000000000000000000000f6ed000000, 0xfffffff33fffffffffffffffffffffed9afdb69f000003800000000000000000000000e000000000])
def claim186 : Claim := (6, [0x84222444000000006870c000000008000040000000000000000000006870c00000000000000, 0xa520360400000000606080000000008200000000ad643684000000006870c00000000083000, 0xa903b200000000006820000000000a8200000000a803b000000000006800000000000a80000, 0xad65002000000000000000000000000000000000ad640000000000000000000000000000000, 0xad67b6f400000000404080000000000000000000ad67b6f4000000000000000000000000000, 0xfffff77d8df9bffffffffb7ff3ffffffff7ffffb0000005400680000000000070000000000003000])
def claim187 : Claim := (6, [0x845c0b80000000000000000022450049c0000000001c0380000000000000000000000009c0, 0x21c093900000000000000000096c002c0400000001c003800000000000000000016c002c000, 0x294592b000000000000000000a0c10000000000039cddbba00000000000000000e0c1000000, 0x39cd002000000000000000000f6ed0001000000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffff33fe45fffffffffffffffffed9afdb69f000003801d80000000000000000000e000000000])
def claim188 : Claim := (6, [0x2c000000000026800000000002500000000000002c00000000002e800000000002d000000, 0x8074000000040048800000002005d000000000000034000000000000000000000000d00000, 0x802220000004c02ed80000000000080000000000000000000004c02ed800000000000000000, 0x982f680000040022400000000002000000000000982f6800000000000000000000000000000, 0xfffff77d8dffffffbbffd37fffffffdffe3fffff00000000000000000002c000000000002c000000, 0xffffffffddfffffffffffb7fffffffffff7fffff00000982c00000004c02e800000000602d000000])
def claim189 : Claim := (6, [0x9290000000000000000000000000000000000001dbba000000000000000000000000000, 0x1088490a00000000000000000562c000000000000000000000000000000000000162c000000, 0x21c093900000000000000000096c00000000000001c003800000000000000000016c0000000, 0x3901da0000000000000000000e488000000000003801d80000000000000000000e000000000, 0x39cddbba0000000000000000010200000000000039cddbba000000000000000000000000000, 0xfffffce77e4fdfffffffffffffffff2b57ffffff000000001c038000000000000000000000000000])
def claim190 : Claim := (6, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000, 0xfffbbffffffbbffb7ffffffff3ffbffffffffffb00000003c000000000037800d000000037000f30])
def claim191 : Claim := (6, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x16d2fefdf55c3da000000000000000000000000000001efdf01c3d8, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim192 : Claim := (7, [0x8000400080008004440091000800244005d400000000000000000000000000000000000000d40, 0x40006c00000040037640000004001b640001000000006c00000000037640000000001b64000000, 0x800040004000d80376406d900000000000040000000000000000d80376406d9000000000000000, 0xc80064004800c800340005000480014000100000d8006c005800d8003400050005800140001000, 0xd80020000000d801100020000580090001000000d80000000000d8000000000005800000000000, 0xd8006c005800d80374006d0005801b4003504000d8006c005800d80374006d0005801b40035000, 0xffffffffffffffa7feabbfd6effa7ff4bbfeaabf00d8006c00580000000000000000000000000000])
def claim193 : Claim := (7, [0x1088444488914000002040045c000000000000000000000000000000000000005c0, 0x47811dc023b000000060000c040000000000000007801dc003b000000060000c000, 0x8423dddd800000000060c00010000000000000000003dddd800000000060c000000, 0xd6ab41c1a8304000000000000000000000000000f7bbc1c1b830400000000000000, 0xf7ba111102040000000000000000000000000000f7b800000000000000000000000, 0xf7bbddddbbb74000000000004000000000000000f7bbddddbbb7400000000000000, 0xffffffffffffffa47eaaa7d6abfffffdfbffbabf0000000000000f003c0003800000000000000000])
def claim194 : Claim := (3, [0x100000000000000000000000000000000000, 0xffffefffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000])
def claim195 : Claim := (7, [0xee0642100001ce62010100000360501020000000ee8600000001dee800000000036840000000000, 0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef6ef77b6f5084402024040800000000000000eeef6ef77b6f4000000000000000000000000000])
def claim196 : Claim := (6, [0x10a000000000489000000000024c60000000000000000000000068d000000000034e70, 0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim197 : Claim := (6, [0x1088000008916c0d800000046c000000000000000000000000002c05800000006c0, 0x4380000023b009390000001c04000000000000000380000003b000380000001c000, 0x528800002830692d0000000000000000000000007398000038306dbda0000000000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x739800003bb76004000000004000000000000000739800003bb7400000000000000, 0xffffffffffffffe67fffffd6abfe25fffffeb9af00000000000007000000038002d8000000000000])
def claim198 : Claim := (6, [0x1088000000812c0d800000046c000000000000000000000000002c05800000006c0, 0x43800000038009390000001c040000000000000003800000038000380000001c000, 0x528800000000292d0000000000000000000000007398000000002dbda0000000000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x7398000003872004000000004000000000000000739800000387000000000000000, 0xffffffffffffffe67fffffd7affe25fffffeb9af00000000000007000000000002d8000000000000])
def claim199 : Claim := (3, [0x1000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000100000000000000000000000000000000000])
def claim200 : Claim := (6, [0x36040000000060608000000000820000000000003f060000000070608000000000c2000, 0x2b00000017004b00000027600130000000ba00000b00000007000b000000076000300000003a000, 0x8804000024056b500000776e80000000000000000000000000016b500000776e800000000000000, 0xaa04000036054a40000060608120000000820000bb0500003f076b500000706081b0200000c2000, 0xbb05000000016b500000020401b0200000100100bb05000000016b500000000001b020000000000, 0xbb0500003f070840000044488000000000200200bb0500003f06000000000000000000000000000, 0xff6fafffffaf9f6affffff9b37fefdfffffcffcf0b000000038016000000070000180000000c0000])
def claim201 : Claim := (6, [0x80034000000012425a1c3400002000000000000000034000000000001a1c3000000, 0xc003000020000360581820820000000000000000d0034000280003685a1c3083000, 0xd002000000003b6b501020000000000000000000d000000000003b6b40000000000, 0xd003400028002000000008000000000000000000d00340002800000000000000000, 0xd003400028003b201a080e820000000000000000d003400028003b001a000e80000, 0xfffffffffffff6ffdbffff7ffcdfdadffc3ffffd00000000000000000000000000068001c0003000])
def claim202 : Claim := (6, [0x84200000000012425a1c3400002000000000000000000000000000001a1c3000000, 0xc620000000000360581820820000000000000000d6a80000000003685a1c3083000, 0xd200000000003b201a0806820000000000000000d000000000003b001a000680000, 0xd6a8000000002004000000000000000000000000d6a800000000000000000000000, 0xd6a8000000003b6f501020000000000000000000d6a8000000003b6f40000000000, 0xfffffffffffff6fd7ffffffffcdf9adffcbffffd00000000000000680000000000068001c0003000])
def claim203 : Claim := (6, [0x380015800540000000000000000000000000000038001d8007400000000000000, 0x100840048801740002000d000000000000000000000000000000340000000d00000, 0x8022c01d800012001600040000000000000000000002c01d8000000016000000000, 0xb03a001100043680100000000000000000000000b03800000000368000000000000, 0xfffffffffffff6fd5bffe77ff8dffedfff3fffff00000000000000000001c0007000000000000000, 0xfffffffffffffffffffffffffedffedfffbfffff0000000000000b03ac01d9807400000000000000])
def claim204 : Claim := (6, [0x39b34000000000000000000000000000000000003bb7400000000000000, 0x1088000008916c0d8000000000000000000000000000000000002c0580000000000, 0x4380000023b009390000000000000000000000000380000003b0003800000000000, 0x7200000039222da00000000000000000000000007000000038002d8000000000000, 0xfffffffffffffad77ffffd7cf96d2fffffffffff0000000000000000000000387000000000000000, 0xffffffffffffffffffffffffff6d6fffffffffff0000000000000739800003bb7400000000000000])
def claim205 : Claim := (6, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x4d0028004e00780037800dc004a0034000f34000000000000000780037800dc00000034000f30, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim206 : Claim := (6, [0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x26d4e000000007dfbc0000000096ccec0000000000000000000007dfbc0000000002cce8, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim207 : Claim := (7, [0x80004000800080044400910008002440057400000000000000000000000000000000000000740, 0x40006c00000040037540000004001b540001000000006c00000000037540000000001b54000000, 0x800040004000d80375406d500000000000040000000000000000d80375406d5000000000000000, 0xc80064004800c800340005000480014000100000d8006c005800d8003400050005800140001000, 0xd8006c0058008002200044000000100002000000d8006c00580000000000000000000000000000, 0xd8006c005800d80374006d0005801b4003504000d8006c005800d80374006d0005801b40035000, 0xffffffb3ffa7fffffd9bbfb2efffffedbbfdaabf00d80000000000d8000000000005800000000000])
def claim208 : Claim := (7, [0x84400000000444480810000022450045c000000000000000000000000000000000000005c0, 0x25c0000000012ec001800000096c000c0400000005c0000000002ec001800000016c000c000, 0x842000000005eeee818300000000000040000000000000000005eeee8183000000000000000, 0xad640000000542c2800000000a0c100000000000bdec00000005c2c2800000000e0c1000000, 0xbdec000000042222000000000102000000000000bdec0000000000000000000000000000000, 0xbdec00000005eeee800000000f6ed00010000000bdec00000005eeee800000000f6ed000000, 0xffffffb13ffffffffd9997f7efffffed9affbabf00000b80000000005c000000000000e000000000])
def claim209 : Claim := (7, [0xee06e73036050844020240408000000000000000ee86ef743684000000000000000000000000000, 0xee06e7303605ce67038360608360581820820000ee86ef743685deef43c3e870c3685a1c3083000, 0x33f9937c8df9a6f91bffc37ff0df9adffc3ffff900e80074006800e8003c000700068001c0003000, 0x44422ef750020842743c3800012425a1c340000200000ef740000000743c3800000001a1c3000000, 0x8884484222445deef43c3e870e004000008000040000000000001deef43c3e870c00000000000000, 0xee200e903b201d207408068203b201a080e82000ee000e803b001d007400068003b001a000e80000, 0xeeef642100001deea010100003b6f50102000000eeef600000001dee8000000003b6f40000000000])
def claim210 : Claim := (6, [0x460c14c1c8000000000000000000000000000000162c02c9e8, 0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000])
def claim211 : Claim := (3, [0x400020000000000000000000000000000000000050002800100000000000000000000000000000, 0x400028000000000000000000000018000000000000002800000000000000000000001800000000, 0x500028001000000000000000000010000200000050002800100000000000000000000000000000, 0xfffffff7ffefffffffffffffffffffeffffdffff0050000000000000000000000000000000000000])
def claim212 : Claim := (6, [0x1090000010a00100000000d0000a0000000e30000000000000000000000000d000000000000e30, 0x9050000050600500000000c800020000000030009850000058600580000000dc00020000000030, 0x990000005900000000000000000000000000000098000000580000000000000000000000000000, 0x9dd000000000058000000040004a0000000210009dd000000000058000000000004a0000000000, 0x9dd000005de004000000008800000000000820009dd000005de000000000000000000000000000, 0xffe66fffffe65ffffffffffffffff5fffffff5cf000000000000000580000000dc00000000000000])
def claim213 : Claim := (6, [0x110110880902000000000000001005c380380000000000000000000000000000000001c38038000, 0x44027398000000000000000000401ddba000000000007398000000000000000000001ddba000000, 0x50035018080200000000000000001403a000000070037018180200000000000000001c03a000000, 0x7703421000000000000000000070109120100000770300000000000000000000007000000000000, 0x770373981b020000000000000000010200200000770373981b02000000000000000000000000000, 0xffafcfd67fefdffffffffffffffaffe6cdfcffff070007000180000000000000000001c000000000])
def claim214 : Claim := (3, [0x200000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000020000000000000000000000000000000000])
def claim215 : Claim := (6, [0x1008480a0000802c100b00000402c140da800000000000000000002c000b00000002c000da8, 0x802220440004c02ed80bc0000000080040400000000000000004c02ed80bc00000000000000, 0x902828060004802a500a80000402804002800000982c28060004c02ed80bc0000602d040028, 0x980368000004c0085802000006008d4008800000980368000004c0005800000006000d40000, 0x982f686e00040022400880000002000082000000982f686e000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000982c00000004c02e800000000602d000000])
def claim216 : Claim := (3, [0x60000000000088000000000000200000000000006000000000009c00000000000020, 0xa000000000009000000000000c200000000000000000000000009000000000000c20, 0x4e000000000008800000000000820000000000004e000000000000000000000000000, 0xffffffffffff5ffffffffffffffffffffffff7df0000000000000000000000009c00000000000000])
def claim217 : Claim := (6, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000, 0xffffffffffffffffffffffffffb7f5ffffebfd67000000000000000000000000000781efdf01f000])
def claim218 : Claim := (6, [0x11010000010021100000170e009020000038000000000000000000000000070e000000000038000, 0x8804000004016b500000776e80000000000000000000000000016b500000776e800000000000000, 0x90050000000120500000500e8080200000000000b0050000000160500000700e818020000000000, 0xbb05000000016b500000020401b0200000100000bb05000000016b500000000001b020000000000, 0xbb05000007010840000044488000000000200000bb0500000700000000000000000000000000000, 0xff6fafffffafff6affffff9b37fefdfffffcffff0b00000000001600000007000018000000000000])
def claim219 : Claim := (6, [0x66003400640068000000000006400000000000007600340074006800000000000740000000000, 0x422067400200420034000000042401400000000000006740000000003400000000000140000000, 0x844042004440ce80340005000040000000000000000000000000ce803400050000000000000000, 0xcf6021000000ce801000000004f4010000000000cf6000000000ce800000000004f40000000000, 0xcf6067404f408400200004000000000000000000cf6067404f4000000000000000000000000000, 0xff3f9f9cffbfbf39ffcffffbfffbfbfeffffffff0007000000070000000000000000700000000000])
def claim220 : Claim := (3, [0x8000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000800000000])
def claim221 : Claim := (6, [0x1008480a0000802c100b00000402c140da800000000000000000002c000b00000002c000da8, 0x802220440004c02ed80bc0000000080040400000000000000004c02ed80bc00000000000000, 0x902828060004802a500a80000402804002800000982c28060004c02ed80bc0000602d040028, 0x980368000004c0085802000006008d4008800000980368000004c0005800000006000d40000, 0x982f686e00040022400880000002000082000000982f686e000000000000000000000000000, 0x982f686e0004c02ed80bc00000020800c2400000982f686e0004c02ed80bc00000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000982c00000004c02e800000000602d000000])
def claim222 : Claim := (6, [0x2010000000000480a401c140398000000000000000000000000000000001c000398, 0xa0300000000002807401a0400180000000000000b0380000000002807601f040018, 0xb000000000003680160085400880000000000000b00000000000368016000540000, 0xb038000000002004000000000000000000000000b03800000000000000000000000, 0xb038000000003686f00120002100000000000000b038000000003686e0000000000, 0xfffffffffffffcfe7ffffffffdb7b5ffffebfd67000000000000000000000000000001601f000000])
def claim223 : Claim := (3, [0x800000000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0080000000000000000000000000000000000000])
def claim224 : Claim := (6, [0x10800800108000000000000001081a00034b400000000000000000000000000000001a00034b40, 0x42002c00020000000000000004201b400001020000002c00000000000000000000001b40000000, 0x500028001000000000000000050019000300000058002c00180000000000000005801b40035000, 0x5b802000000000000000000005b80900010200005b800000000000000000000005b80000000000, 0x5b802c001b8000000000000000001000020800005b802c001b8000000000000000000000000000, 0xfffd7ffffffd7fffffffffffffffd7fffffff4fd0058002c00180000000000000005801b40035000])
def claim225 : Claim := (3, [0x600120000100000000000000000000000000000060017000010, 0xa00140003100000000000000000000000000000000014000310, 0x2e001200021000000000000000000000000000002e0000000000, 0xfffffffffffffffffffffffffffff5fffffffdef0000000000000000000000000000000017000000])
def claim226 : Claim := (6, [0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000, 0xfffffffffb7f5fffffffffffffffffffffebf7570000000000780000000007dfbc0000000002f000])
def claim227 : Claim := (6, [0x2010801c10070480a401c14079800000000000000000001c000700000001c000798, 0xa0328019100602807401a0400180000000000000b03ac01d980742807601f040018, 0xb002c0081802368016008d400880000000000000b002c0001800368016000d40000, 0xb03a001100043686f00120002100000000000000b038000000003686e0000000000, 0xb03ac01d98076004000008004040000000000000b03ac01d9807400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000002c01d800000001601f000000, 0xfffffffffffffffffffffe7fcbffffffff6bfb730000000000000b03ac01d80003686f601f000000])
def claim228 : Claim := (6, [0x38000000700033000c80000003200000000000003800000070003b000e80000003a000000, 0x4000d03800008026803b000002001403a00000000000d03800000006803b000000001403a000000, 0x800080202001a076803b500e8000000000000000000000000001a076803b500e800000000000000, 0xd00040100001a072001100040280100120000000d00000000001a07000000000028000000000000, 0xd000d03828010044002240088000000200000000d000d0382800000000000000000000000000000, 0xf3fff3fcfdffe7f99fffcbfff7dffefffdffffff000000000000000000038000e000000038000000])
def claim229 : Claim := (6, [0x46404f400000242800000000004100000000000056406f4000002c280000000000c1000000, 0x84780f0000040408800000002041e000000000000038070000000000000000000000e00000, 0x84222444000542c2e8000000000008000000000000000000000542c2e800000000000000000, 0xad650020000542c2800000000a0c140000000000ad640000000542c2800000000a0c1000000, 0xad67b6f400040202400000000000000000000000ad67b6f4000000000000000000000000000, 0xfffff77d8df9bfffbbffd37fffffffdffe3fffff0000005400680000002c000000000000c0000000])
def claim230 : Claim := (3, [0x100000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000010000000000000000000000000000000])
def claim231 : Claim := (6, [0x1090000010a01100000068d0010a0000034e70000000000000000000000068d000000000034e70, 0x8440000044409d8000006ddc00400000000404000000000000009d8000006ddc00000000000000, 0x9050000050609500000064c801020000030030009850000058609d8000006ddc01820000035030, 0x9dd0000000009d800000204001da0000010210009dd0000000009d800000000001da0000000000, 0x9dd000005de084000000448800000000020820009dd000005de000000000000000000000000000, 0x9dd000005de09d8000006ddc00400000020c24009dd000005de09d8000006ddc00000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00980000005800980000006d0001800000035000])
def claim232 : Claim := (6, [0x9d800000204000000000000000000000000000009d800000000000000000000000, 0x10a01100000068d000000000024c60000000000000000000000068d000000000024c60, 0x44409d8000006ddc00000000000404000000000000009d8000006ddc00000000000000, 0x50609500000064c800000000020020000000000058609d8000006ddc00000000025020, 0x5de08400000044880000000002082000000000005de000000000000000000000000000, 0xfffffffffffb1ffa7fffffff23fffffffffff3db00000000005800980000006d0000000000025000])
def claim233 : Claim := (6, [0x4a801418010404f40000000000000000000000006a801c18030406f40000000000, 0x108840408810780f02000e000000000000000000000000000000380700000e00000, 0x842341c1800012425a0004000000000000000000000341c1800000001a000000000, 0xd6aa010100003b6f500000000000000000000000d6a8000000003b6f40000000000, 0xd6ab41c1a8306004000008000000000000000000d6ab41c1a830400000000000000, 0xfffffffffffff6fd5bffe77ff8df9adfff3fffff0000000000000068001c00030006800000000000])
def claim234 : Claim := (3, [0x200000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000020000000000000000000000000])
def claim235 : Claim := (6, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0x1ffbfed9a7da29800000000000000000000000001ffbfe0007c0000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim236 : Claim := (3, [0x1000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000000100000000000000000])
def claim237 : Claim := (6, [0x1090088010a0000000000000010a1a34034b700000000000000000000000000000001a34034b70, 0x42202dc0020000000000000004241b770001020000002dc0000000000000000000001b77000000, 0x503029801020000000000000050619320300300058302dc0182000000000000005861b77035030, 0x5bb02100000000000000000005be0912010210005bb00000000000000000000005be0000000000, 0x5bb02dc0020000000000000005be1b77010312005bb02dc0000000000000000005be1b77000000, 0x5bb02dc01ba000000000000000001020020820005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd1ffc8fff4cd0058002c00180000000000000005801b40035000])
def claim238 : Claim := (6, [0x8800000000000000000010a1a340143500000000000000000000000000000001a34014350, 0x2100000000000000000005be09120102100000000000000000000000000005be0000000000, 0x29800000000000000000050619320100100000002dc0000000000000000005861b77015010, 0x2dc00000000000000000000010200000000000002dc0000000000000000000000000000000, 0x2dc0000000000000000004241b770001020000002dc0000000000000000000001b77000000, 0xfffffffe3fffffffffffffffffffd1ffc8fffced0000002c00000000000000000005801b40015000])
def claim239 : Claim := (3, [0x40000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000000000000000004000000000000000000])
def claim240 : Claim := (6, [0x3f0600000000756a8000000000ea0280000000003f86000000007dfbc000000000ef028, 0x490a00000000158b00000000016cce8000000000000000000000058b00000000002cce8, 0x22444000000007dfbc000000008004040000000000000000000007dfbc00000000000000, 0x2fa00000000007922000000000bca088000000002f800000000007800000000000bc0000, 0x2ffde000000004448800000000020820000000002ffde000000000000000000000000000, 0x2ffde000000007d6a800000000bea8a8000000002ffde000000007800000000000bc0000, 0xffffffffd97b1ffffffffa7f43ffffffff6bf35300000000007800000000005f000000000002f000])
def claim241 : Claim := (6, [0x1088400800000000000000000562c1009c0000000000000000000000000000000162c0009c0, 0x3188000000000000000000000d4a80000000000039cc000000000000000000000f6ed000000, 0x3901c00000000000000000000e488700080000003801c00000000000000000000e000700000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cdc0380000000000000000010200008000000039cdc038000000000000000000000000000, 0xfffffe7f2bfd7fffffffffffffffff9fd2aff67d0000001c000000000000000000000016c0000000])
def claim242 : Claim := (3, [0x12000000082000000000000000000000000000001b0200000c2000, 0x1300000009a000000000000000000000000000000300000001a000, 0x1b020000010010000000000000000000000000001b020000000000, 0xfffffffffffffffffffffffffffefdfffffeffef00000000000000000000000000180000000c0000])
def claim243 : Claim := (6, [0x2000000010000490a000015c2d8000000000000000000000000000000000001c2d8, 0x60000000300001b0200000da018000000000000070000000380001b8200000df018, 0x7000000000002db9a000001021000000000000007000000000002db9a0000000000, 0x7000000038002000000008000000000000000000700000003800000000000000000, 0x7000000038002da000000bca08800000000000007000000038002d8000000bc0000, 0xfffffffffffffcfffffffe7ffdb7f5ffff6bfd67000000000000000000000000000380000001f000])
def claim244 : Claim := (3, [0x2000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000200000000000000000000000000000000])
def claim245 : Claim := (6, [0x2110000013870400800001006c000000000000000000000003870000000000006c0, 0x6310000033260000000000000000000000000000739800003bb7400000000000000, 0x7200000039222c0000000b0008000000000000007000000038002c0000000b00000, 0x7398000002042c058000000020000000000000007398000000002c0580000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89bfb7ffff6ff97b00000000000000380000003b0000000000000000])
def claim246 : Claim := (6, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000, 0xffff6fffffff5ffffffffffffffff5fffffff5cf00000003c000000780037800dc00000037000000])
def claim247 : Claim := (3, [0xca00800000000000000000000000000000000000cf008, 0x14c0c8000000000000000000000000000000000000c0c8, 0x3ca08800000000000000000000000000000000003c0000, 0xffffffffffffffffffffffffffffffffffebff77000000000000000000000000000000000000f000])
def claim248 : Claim := (6, [0x2110000013870490a000015c6d8000000000000000000000038700000000001c6d8, 0x63100000332601b0200000da0180000000000000739800003bb741b8200000df018, 0x7200000039222da000000bca08800000000000007000000038002d8000000bc0000, 0x7398000002042dbda000001021000000000000007398000000002dbda0000000000, 0x739800003bb76004000008004040000000000000739800003bb7400000000000000, 0xfffffffffffffcfe7ffffe7f89b7b5ffff6bf96300000000000000380000003b000380000001f000, 0xfffffffffffffffe7fffffffabffb5fffffff9eb0000000000000738000003bb02db800000bdf000])
def claim249 : Claim := (6, [0x1088490a00000000000000000562c16c9e8000000000000000000000000000000162c02c9e8, 0x31881b0200000000000000000d4a80ea0280000039cc1b8200000000000000000f6ed0ef028, 0x3901da0000000000000000000e4887ca088000003801d80000000000000000000e0007c0000, 0x39cd002000000000000000000f6ed4001020000039cc000000000000000000000f6ed000000, 0x39cddbba0000000000000000010200208200000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffff9fd2abf6550000001c003800000000000000000016c002f000, 0xffffffff3ffd5fffffffffffffffffffdafff6dd0000039c1db8000000000000000000f6c07ef000])
def claim250 : Claim := (6, [0xd8000000d8008800000081000d80000004e400005800000058000000000000000580000000e40, 0x8440000044409d80000068d000400000000400000000000000009d80000068d000000000000000, 0x8d4000004d408c800000000000d00000000000009dd000005de09d800000000001da0000000000, 0x990000005900980000006800019000000340400098000000580098000000680001800000034000, 0x9dd000005de084000000408000000000020820009dd000005de000000000000000000000000000, 0xffffffffffa21fffffffffb76ffffffffffdb39f009dd0000000009d800000000001da0000000000])
def claim251 : Claim := (6, [0x1000000138300100000015c4c8000000000000000000000038300000000001c4c8, 0x20000003922002000000bca0880000000000000000000003800000000000bc0000, 0x300000033220030000000da0080000000000000038000003bb34038000000df008, 0x380000002000038000000100000000000000000038000000000003800000000000, 0x38000003bb34000000008004040000000000000038000003bb3400000000000000, 0xfffffffffffffffffffffe7fcbffffffff6bfb7300000000000000380000003b000380000001f000])
def claim252 : Claim := (3, [0x1000000000000000000000000000000000000000000000000000000000000000000000000, 0xffffffffffffffffffffffffffffffffffffffff0000000100000000000000000000000000000000])
def claim253 : Claim := (6, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0x6f003c006e00780033000c8006e0032000a300006f003c006e0078000000000006e0000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim254 : Claim := (7, [0x60030000400600003000080004000200000000007003c0006007800038000c00060003000000, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim255 : Claim := (7, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe9fd2dff8affc7d0000000000000000000000000007800fdc01f018])
def claim256 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb3ffffffb3ffb7fffffffe3ffb7fffffff1fb00000003c000000000037800d000000037000030])
def claim257 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x450028004600780037800dc00420030000434000000000000000780037800dc00000034000030, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim258 : Claim := (6, [0x2000800010000480840001407800000000000000000000000000000000000000780, 0x8002000000000200100000000000000000000000b002c0001800028016000040000, 0xa002800010000280140000400000000000000000b002c0001800028016000040000, 0xb002000000003686900000002000000000000000b00000000000368680000000000, 0xb002c00018002004000008004040000000000000b002c0001800000000000000000, 0xb002c0001800368016000d400800000000000000b002c0001800368016000d40000, 0xfffffffffffffcfffffffe7ffdb7b7ffff6bf97b00000000000000002c0000000000016000000000])
def claim259 : Claim := (6, [0x109000000080110000000000010a0000000e400000000000000000000000000000000000000e40, 0x80400000000084000000000000000000000000009850000000009d800000000001820000000000, 0x8440000004009d800000000000400000000404000000000000009d800000000000000000000000, 0x90500000000095000000000001020000000000009850000000009d800000000001820000000000, 0x9dd0000000009d800000000001da0000000200009dd0000000009d800000000001da0000000000, 0x9dd00000058084000000000000000000000800009dd00000058000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffffffb5fffffff1fb0098000000000098000000000001800000000000])
def claim260 : Claim := (6, [0x1090088010a000000000000000080000000b400000000000000000000000000000000000000b40, 0x402021000000000000000000000000000000000058302dc0182000000000000000000000000000, 0x42202dc00200000000000000002000000001020000002dc0000000000000000000000000000000, 0x503029801020000000000000000000000000000058302dc0182000000000000000000000000000, 0x5bb02100000000000000000000380000000200005bb00000000000000000000000380000000000, 0x5bb02dc01ba000000000000000000000000800005bb02dc01ba000000000000000000000000000, 0xfffd4ffe3ffd5fffffffffffffffd7fffffff4fd0058002c00180000000000000000000000000000])
def claim261 : Claim := (6, [0x8000400080000000000000000800244005b400000000000000000000000000000000000000b40, 0x400020000000000000000000040001000000000058002c00180000000000000005800140001000, 0x40002c00000000000000000004001b740001000000002c00000000000000000000001b74000000, 0x480024000800000000000000048001400010000058002c00180000000000000005800140001000, 0x58002c001800000000000000000010200208200058002c00180000000000000000000000000000, 0x58002c00180000000000000005801b400350400058002c00180000000000000005801b40035000, 0xfffffff3ffe7ffffffffffffffffffed9bfda69f0058000000000000000000000005800000000000])
def claim262 : Claim := (6, [0x8040000000040048001000002005000d800000000000000000000000000000000000000d80, 0x8020000000040002000000000000000000000000982c00000004c0028000000006001000000, 0x802000000004c02e800b00000000000040000000000000000004c02e800b000000000000000, 0x8824000000044002800000000200100000000000982c00000004c0028000000006001000000, 0x982c000000040022000800000002000082000000982c0000000000000000000000000000000, 0x982c00000004c02e800000000602d00010000000982c00000004c02e800000000602d000000, 0xfffffffd3ffffffffffd97ff6fffffffdafff2df00000980000000004c0000000000006000000000])
def claim263 : Claim := (6, [0x1088000008914000000000046c000000000000000000000000000000000000006c0, 0x4200000020200000000000000000000000000000739800003830400000000000000, 0x4380000023b000000000001c04000000000000000380000003b000000000001c000, 0x5288000028304000000000000000000000000000739800003830400000000000000, 0x7398000002040000000000102100000000000000739800000000000000000000000, 0x739800003bb74000000000004000000000000000739800003bb7400000000000000, 0xffffffffffffffe67fffffd6abfffffffffeb9af0000000000000700000003800000000000000000])
def claim264 : Claim := (7, [0x50e0b160143500000000000000000000000000007860fdf01f3d8, 0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim265 : Claim := (7, [0x28000e000000260009800000024000d2000000003c000600000037800dc00000037000f30, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim266 : Claim := (7, [0x30001500050000e0016000710000000000000000780037800dc00060037000f30, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim267 : Claim := (7, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1fa01e4887ca08800000000000000000000000001f801e0007c0000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe97d69ff2abfc750000000000000000000000000007860fdf01f018])
def claim268 : Claim := (6, [0x8040000000040048001000002005000d800000000000000000000000000000000000000d80, 0x802000000004c02e800b00000000000040000000000000000004c02e800b000000000000000, 0x8824000000044002800000000200100000000000982c00000004c0028000000006001000000, 0x982c000000040022000800000002000082000000982c0000000000000000000000000000000, 0x982c00000004c02e800000000602d00010000000982c00000004c02e800000000602d000000, 0xfffffffd3ffffffffffd97ff6fffffffdafff2df00000980000000004c0000000000006000000000, 0xfffffffd7ffffffffffddfff7fffffffdfffffdf00000980000000004c0000000000006000000d80])
def claim269 : Claim := (6, [0x2000800010000480840001407800000000000000000000000000000000000000780, 0xa002800010000280140000400000000000000000b002c0001800028016000040000, 0xb002000000003686900000002000000000000000b00000000000368680000000000, 0xb002c00018002004000008004040000000000000b002c0001800000000000000000, 0xb002c00018002484840009407840000000000000b002c0001800000000000000780, 0xb002c0001800368016000d400800000000000000b002c0001800368016000d40000, 0xfffffffffffffcfffffffe7ffdb7b7ffff6bf97b00000000000000002c0000000000016000000000])
def claim270 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffabffb5fffffff1eb00000003c000600000037800dc00000037000030])
def claim271 : Claim := (6, [0x109000000080110000000000010a0000000e400000000000000000000000000000000000000e40, 0x8440000004009d800000000000400000000404000000000000009d800000000000000000000000, 0x90500000000095000000000001020000000000009850000000009d800000000001820000000000, 0x9dd0000000009d800000000001da0000000200009dd0000000009d800000000001da0000000000, 0x9dd00000058084000000000000000000000800009dd00000058000000000000000000000000000, 0xfffb2ffffffb7ffa7fffffffffffb5fffffff1fb0098000000000098000000000001800000000000, 0xfffbbffffffbfffb7fffffffffffbffffffffffb0098000000000098000000000001800000000e40])
def claim272 : Claim := (6, [0x1088000008914000000000046c000000000000000000000000000000000000006c0, 0x4380000023b000000000001c04000000000000000380000003b000000000001c000, 0x5288000028304000000000000000000000000000739800003830400000000000000, 0x7398000002040000000000102100000000000000739800000000000000000000000, 0x739800000a954000000000146d000000000000007398000000000000000000006c0, 0x739800003bb74000000000004000000000000000739800003bb7400000000000000, 0xffffffffffffffe67fffffd6abfffffffffeb9af0000000000000700000003800000000000000000])
def claim273 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00460012000414000000000000000780037800dc00060037000030, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim274 : Claim := (6, [0x8000400080000000000000000800244005b400000000000000000000000000000000000000b40, 0x40002c00000000000000000004001b740001000000002c00000000000000000000001b74000000, 0x480024000800000000000000048001400010000058002c00180000000000000005800140001000, 0x58002c001800000000000000000010200208200058002c00180000000000000000000000000000, 0x58002c00180000000000000000801264025b600058002c00180000000000000000000000000b40, 0x58002c00180000000000000005801b400350400058002c00180000000000000005801b40035000, 0xfffffff3ffe7ffffffffffffffffffed9bfda69f0058000000000000000000000005800000000000])
def claim275 : Claim := (6, [0x1088490a0000000000000000000001009c000000000000000000000000000000000000009c0, 0x31881b020000000000000000000000000000000039cc1b82000000000000000000000000000, 0x3901da00000000000000000000000700080000003801d800000000000000000000000700000, 0x39cd00200000000000000000000004001020000039cc0000000000000000000000000000000, 0x39cd492a0000000000000000000005009c20000039cc00000000000000000000000000009c0, 0x39cddbba0000000000000000000000008000000039cddbba000000000000000000000000000, 0xfffffe7f2b7d5fffffffffffffffffffffaff67d0000001c00380000000000000000000000000000])
def claim276 : Claim := (7, [0x3f07cd9a0da018000000000000000000000000003f87efdf0df018, 0x490a4e1c15c3d80000000000000000000000000000000e1c01c3d8, 0x12425efdf400102000000000000000000000000000001efdf000000, 0x1ffbf091201021000000000000000000000000001ffbe0000000000, 0xfffffffffffffffffffffffffe05da1b74835f750000000000000000000000000007800fdc01f3d8, 0xfffffffffffffffffffffffffe97d09fe0abfc650000000000000000000000000007800fc001f000])
def claim277 : Claim := (7, [0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f003c006e0040002200088000000200008200006f003c006e000000000000000000000000000, 0xfff90ffefffbbff87ffeefffb3ff91ffedfffdeb00000003c000000000037800d000000037000f30, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])
def claim278 : Claim := (7, [0x38001580054004a0014000714000000000000000780037800dc00000034000f30, 0x70038000600700033000c80006003200003000007003c000600780037800dc00060037000030, 0x90008000a00100034000d0000a0034000f30000000000000000000034000d000000034000f30, 0x440020004400780037800dc00400000000404000000000000000780037800dc00000000000000, 0x6f001000000078001100040006e00120002100006f000000000078000000000006e0000000000, 0xfffb2ffffffb1ffa7fffffff23ffb5fffffff1cb00000003c0000000000378000000000037000000])

def claims : List Claim := [claim0, claim1, claim2, claim3, claim4, claim5, claim6, claim7, claim8, claim9, claim10, claim11, claim12, claim13, claim14, claim15, claim16, claim17, claim18, claim19, claim20, claim21, claim22, claim23, claim24, claim25, claim26, claim27, claim28, claim29, claim30, claim31, claim32, claim33, claim34, claim35, claim36, claim37, claim38, claim39, claim40, claim41, claim42, claim43, claim44, claim45, claim46, claim47, claim48, claim49, claim50, claim51, claim52, claim53, claim54, claim55, claim56, claim57, claim58, claim59, claim60, claim61, claim62, claim63, claim64, claim65, claim66, claim67, claim68, claim69, claim70, claim71, claim72, claim73, claim74, claim75, claim76, claim77, claim78, claim79, claim80, claim81, claim82, claim83, claim84, claim85, claim86, claim87, claim88, claim89, claim90, claim91, claim92, claim93, claim94, claim95, claim96, claim97, claim98, claim99, claim100, claim101, claim102, claim103, claim104, claim105, claim106, claim107, claim108, claim109, claim110, claim111, claim112, claim113, claim114, claim115, claim116, claim117, claim118, claim119, claim120, claim121, claim122, claim123, claim124, claim125, claim126, claim127, claim128, claim129, claim130, claim131, claim132, claim133, claim134, claim135, claim136, claim137, claim138, claim139, claim140, claim141, claim142, claim143, claim144, claim145, claim146, claim147, claim148, claim149, claim150, claim151, claim152, claim153, claim154, claim155, claim156, claim157, claim158, claim159, claim160, claim161, claim162, claim163, claim164, claim165, claim166, claim167, claim168, claim169, claim170, claim171, claim172, claim173, claim174, claim175, claim176, claim177, claim178, claim179, claim180, claim181, claim182, claim183, claim184, claim185, claim186, claim187, claim188, claim189, claim190, claim191, claim192, claim193, claim194, claim195, claim196, claim197, claim198, claim199, claim200, claim201, claim202, claim203, claim204, claim205, claim206, claim207, claim208, claim209, claim210, claim211, claim212, claim213, claim214, claim215, claim216, claim217, claim218, claim219, claim220, claim221, claim222, claim223, claim224, claim225, claim226, claim227, claim228, claim229, claim230, claim231, claim232, claim233, claim234, claim235, claim236, claim237, claim238, claim239, claim240, claim241, claim242, claim243, claim244, claim245, claim246, claim247, claim248, claim249, claim250, claim251, claim252, claim253, claim254, claim255, claim256, claim257, claim258, claim259, claim260, claim261, claim262, claim263, claim264, claim265, claim266, claim267, claim268, claim269, claim270, claim271, claim272, claim273, claim274, claim275, claim276, claim277, claim278]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok0 : goodClaim claim0 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok1 : goodClaim claim1 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok2 : goodClaim claim2 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok3 : goodClaim claim3 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok4 : goodClaim claim4 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok5 : goodClaim claim5 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok6 : goodClaim claim6 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok7 : goodClaim claim7 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok8 : goodClaim claim8 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok9 : goodClaim claim9 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok10 : goodClaim claim10 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok11 : goodClaim claim11 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok12 : goodClaim claim12 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok13 : goodClaim claim13 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok14 : goodClaim claim14 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok15 : goodClaim claim15 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok16 : goodClaim claim16 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok17 : goodClaim claim17 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok18 : goodClaim claim18 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok19 : goodClaim claim19 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok20 : goodClaim claim20 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok21 : goodClaim claim21 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok22 : goodClaim claim22 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok23 : goodClaim claim23 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok24 : goodClaim claim24 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok25 : goodClaim claim25 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok26 : goodClaim claim26 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok27 : goodClaim claim27 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok28 : goodClaim claim28 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok29 : goodClaim claim29 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok30 : goodClaim claim30 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok31 : goodClaim claim31 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok32 : goodClaim claim32 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok33 : goodClaim claim33 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok34 : goodClaim claim34 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok35 : goodClaim claim35 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok36 : goodClaim claim36 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok37 : goodClaim claim37 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok38 : goodClaim claim38 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok39 : goodClaim claim39 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok40 : goodClaim claim40 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok41 : goodClaim claim41 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok42 : goodClaim claim42 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok43 : goodClaim claim43 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok44 : goodClaim claim44 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok45 : goodClaim claim45 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok46 : goodClaim claim46 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok47 : goodClaim claim47 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok48 : goodClaim claim48 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok49 : goodClaim claim49 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok50 : goodClaim claim50 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok51 : goodClaim claim51 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok52 : goodClaim claim52 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok53 : goodClaim claim53 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok54 : goodClaim claim54 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok55 : goodClaim claim55 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok56 : goodClaim claim56 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok57 : goodClaim claim57 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok58 : goodClaim claim58 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok59 : goodClaim claim59 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok60 : goodClaim claim60 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok61 : goodClaim claim61 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok62 : goodClaim claim62 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok63 : goodClaim claim63 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok64 : goodClaim claim64 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok65 : goodClaim claim65 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok66 : goodClaim claim66 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok67 : goodClaim claim67 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok68 : goodClaim claim68 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok69 : goodClaim claim69 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok70 : goodClaim claim70 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok71 : goodClaim claim71 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok72 : goodClaim claim72 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok73 : goodClaim claim73 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok74 : goodClaim claim74 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok75 : goodClaim claim75 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok76 : goodClaim claim76 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok77 : goodClaim claim77 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok78 : goodClaim claim78 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok79 : goodClaim claim79 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok80 : goodClaim claim80 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok81 : goodClaim claim81 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok82 : goodClaim claim82 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok83 : goodClaim claim83 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok84 : goodClaim claim84 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok85 : goodClaim claim85 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok86 : goodClaim claim86 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok87 : goodClaim claim87 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok88 : goodClaim claim88 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok89 : goodClaim claim89 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok90 : goodClaim claim90 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok91 : goodClaim claim91 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok92 : goodClaim claim92 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok93 : goodClaim claim93 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok94 : goodClaim claim94 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok95 : goodClaim claim95 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok96 : goodClaim claim96 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok97 : goodClaim claim97 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok98 : goodClaim claim98 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok99 : goodClaim claim99 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok100 : goodClaim claim100 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok101 : goodClaim claim101 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok102 : goodClaim claim102 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok103 : goodClaim claim103 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok104 : goodClaim claim104 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok105 : goodClaim claim105 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok106 : goodClaim claim106 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok107 : goodClaim claim107 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok108 : goodClaim claim108 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok109 : goodClaim claim109 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok110 : goodClaim claim110 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok111 : goodClaim claim111 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok112 : goodClaim claim112 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok113 : goodClaim claim113 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok114 : goodClaim claim114 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok115 : goodClaim claim115 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok116 : goodClaim claim116 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok117 : goodClaim claim117 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok118 : goodClaim claim118 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok119 : goodClaim claim119 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok120 : goodClaim claim120 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok121 : goodClaim claim121 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok122 : goodClaim claim122 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok123 : goodClaim claim123 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok124 : goodClaim claim124 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok125 : goodClaim claim125 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok126 : goodClaim claim126 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok127 : goodClaim claim127 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok128 : goodClaim claim128 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok129 : goodClaim claim129 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok130 : goodClaim claim130 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok131 : goodClaim claim131 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok132 : goodClaim claim132 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok133 : goodClaim claim133 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok134 : goodClaim claim134 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok135 : goodClaim claim135 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok136 : goodClaim claim136 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok137 : goodClaim claim137 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok138 : goodClaim claim138 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok139 : goodClaim claim139 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok140 : goodClaim claim140 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok141 : goodClaim claim141 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok142 : goodClaim claim142 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok143 : goodClaim claim143 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok144 : goodClaim claim144 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok145 : goodClaim claim145 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok146 : goodClaim claim146 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok147 : goodClaim claim147 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok148 : goodClaim claim148 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok149 : goodClaim claim149 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok150 : goodClaim claim150 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok151 : goodClaim claim151 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok152 : goodClaim claim152 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok153 : goodClaim claim153 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok154 : goodClaim claim154 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok155 : goodClaim claim155 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok156 : goodClaim claim156 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok157 : goodClaim claim157 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok158 : goodClaim claim158 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok159 : goodClaim claim159 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok160 : goodClaim claim160 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok161 : goodClaim claim161 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok162 : goodClaim claim162 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok163 : goodClaim claim163 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok164 : goodClaim claim164 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok165 : goodClaim claim165 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok166 : goodClaim claim166 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok167 : goodClaim claim167 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok168 : goodClaim claim168 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok169 : goodClaim claim169 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok170 : goodClaim claim170 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok171 : goodClaim claim171 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok172 : goodClaim claim172 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok173 : goodClaim claim173 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok174 : goodClaim claim174 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok175 : goodClaim claim175 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok176 : goodClaim claim176 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok177 : goodClaim claim177 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok178 : goodClaim claim178 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok179 : goodClaim claim179 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok180 : goodClaim claim180 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok181 : goodClaim claim181 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok182 : goodClaim claim182 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok183 : goodClaim claim183 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok184 : goodClaim claim184 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok185 : goodClaim claim185 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok186 : goodClaim claim186 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok187 : goodClaim claim187 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok188 : goodClaim claim188 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok189 : goodClaim claim189 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok190 : goodClaim claim190 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok191 : goodClaim claim191 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok192 : goodClaim claim192 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok193 : goodClaim claim193 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok194 : goodClaim claim194 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok195 : goodClaim claim195 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok196 : goodClaim claim196 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok197 : goodClaim claim197 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok198 : goodClaim claim198 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok199 : goodClaim claim199 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok200 : goodClaim claim200 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok201 : goodClaim claim201 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok202 : goodClaim claim202 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok203 : goodClaim claim203 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok204 : goodClaim claim204 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok205 : goodClaim claim205 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok206 : goodClaim claim206 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok207 : goodClaim claim207 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok208 : goodClaim claim208 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok209 : goodClaim claim209 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok210 : goodClaim claim210 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok211 : goodClaim claim211 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok212 : goodClaim claim212 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok213 : goodClaim claim213 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok214 : goodClaim claim214 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok215 : goodClaim claim215 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok216 : goodClaim claim216 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok217 : goodClaim claim217 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok218 : goodClaim claim218 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok219 : goodClaim claim219 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok220 : goodClaim claim220 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok221 : goodClaim claim221 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok222 : goodClaim claim222 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok223 : goodClaim claim223 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok224 : goodClaim claim224 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok225 : goodClaim claim225 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok226 : goodClaim claim226 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok227 : goodClaim claim227 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok228 : goodClaim claim228 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok229 : goodClaim claim229 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok230 : goodClaim claim230 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok231 : goodClaim claim231 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok232 : goodClaim claim232 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok233 : goodClaim claim233 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok234 : goodClaim claim234 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok235 : goodClaim claim235 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok236 : goodClaim claim236 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok237 : goodClaim claim237 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok238 : goodClaim claim238 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok239 : goodClaim claim239 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok240 : goodClaim claim240 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok241 : goodClaim claim241 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok242 : goodClaim claim242 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok243 : goodClaim claim243 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok244 : goodClaim claim244 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok245 : goodClaim claim245 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok246 : goodClaim claim246 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok247 : goodClaim claim247 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok248 : goodClaim claim248 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok249 : goodClaim claim249 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok250 : goodClaim claim250 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok251 : goodClaim claim251 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok252 : goodClaim claim252 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok253 : goodClaim claim253 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok254 : goodClaim claim254 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok255 : goodClaim claim255 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok256 : goodClaim claim256 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok257 : goodClaim claim257 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok258 : goodClaim claim258 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok259 : goodClaim claim259 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok260 : goodClaim claim260 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok261 : goodClaim claim261 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok262 : goodClaim claim262 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok263 : goodClaim claim263 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok264 : goodClaim claim264 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok265 : goodClaim claim265 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok266 : goodClaim claim266 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok267 : goodClaim claim267 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok268 : goodClaim claim268 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok269 : goodClaim claim269 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok270 : goodClaim claim270 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok271 : goodClaim claim271 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok272 : goodClaim claim272 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok273 : goodClaim claim273 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok274 : goodClaim claim274 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok275 : goodClaim claim275 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok276 : goodClaim claim276 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok277 : goodClaim claim277 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
theorem ok278 : goodClaim claim278 = true := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 3000000 in
theorem allClaims : claims.all goodClaim = true := by
  simp only [claims, List.all_cons, List.all_nil, Bool.true_and, ok0, ok1, ok2, ok3, ok4, ok5, ok6, ok7, ok8, ok9, ok10, ok11,
    ok12, ok13, ok14, ok15, ok16, ok17, ok18, ok19, ok20, ok21, ok22, ok23,
    ok24, ok25, ok26, ok27, ok28, ok29, ok30, ok31, ok32, ok33, ok34, ok35,
    ok36, ok37, ok38, ok39, ok40, ok41, ok42, ok43, ok44, ok45, ok46, ok47,
    ok48, ok49, ok50, ok51, ok52, ok53, ok54, ok55, ok56, ok57, ok58, ok59,
    ok60, ok61, ok62, ok63, ok64, ok65, ok66, ok67, ok68, ok69, ok70, ok71,
    ok72, ok73, ok74, ok75, ok76, ok77, ok78, ok79, ok80, ok81, ok82, ok83,
    ok84, ok85, ok86, ok87, ok88, ok89, ok90, ok91, ok92, ok93, ok94, ok95,
    ok96, ok97, ok98, ok99, ok100, ok101, ok102, ok103, ok104, ok105, ok106, ok107,
    ok108, ok109, ok110, ok111, ok112, ok113, ok114, ok115, ok116, ok117, ok118, ok119,
    ok120, ok121, ok122, ok123, ok124, ok125, ok126, ok127, ok128, ok129, ok130, ok131,
    ok132, ok133, ok134, ok135, ok136, ok137, ok138, ok139, ok140, ok141, ok142, ok143,
    ok144, ok145, ok146, ok147, ok148, ok149, ok150, ok151, ok152, ok153, ok154, ok155,
    ok156, ok157, ok158, ok159, ok160, ok161, ok162, ok163, ok164, ok165, ok166, ok167,
    ok168, ok169, ok170, ok171, ok172, ok173, ok174, ok175, ok176, ok177, ok178, ok179,
    ok180, ok181, ok182, ok183, ok184, ok185, ok186, ok187, ok188, ok189, ok190, ok191,
    ok192, ok193, ok194, ok195, ok196, ok197, ok198, ok199, ok200, ok201, ok202, ok203,
    ok204, ok205, ok206, ok207, ok208, ok209, ok210, ok211, ok212, ok213, ok214, ok215,
    ok216, ok217, ok218, ok219, ok220, ok221, ok222, ok223, ok224, ok225, ok226, ok227,
    ok228, ok229, ok230, ok231, ok232, ok233, ok234, ok235, ok236, ok237, ok238, ok239,
    ok240, ok241, ok242, ok243, ok244, ok245, ok246, ok247, ok248, ok249, ok250, ok251,
    ok252, ok253, ok254, ok255, ok256, ok257, ok258, ok259, ok260, ok261, ok262, ok263,
    ok264, ok265, ok266, ok267, ok268, ok269, ok270, ok271, ok272, ok273, ok274, ok275,
    ok276, ok277, ok278]

def hint0 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 0)
def hint1 : Option Hint := some (0x240064000000028000c00000001000006, 1, 1)
def hint2 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 2)
def hint3 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 3)
def hint4 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 4)
def hint5 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 5)
def hint6 : Option Hint := some (0x6e0034006c006800038000c006c0003000f06, 1, 6)
def hint7 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 7)
def hint8 : Option Hint := some (0xcf6067404f40ce803438050c04f40143001007, 0, 8)
def hint9 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 9)
def hint10 : Option Hint := some (0x2f6dc000000006870c00000000b83cc5, 0, 10)
def hint11 : Option Hint := some (0xad67b6f4000542c2e870c0000a0c1e83007, 0, 11)
def hint12 : Option Hint := some (0x1ffbfefdf7df3db, 0, 12)
def hint13 : Option Hint := some (0x1f6bda1c37833c3, 0, 13)
def hint14 : Option Hint := some (0xd6ab41c1a8307b6f5a1c3e83007, 0, 14)
def hint15 : Option Hint := some (0x90000000000000000, 64, 15)
def hint16 : Option Hint := some (0xd007d0382807a076803b500e82807403a040038, 3, 16)
def hint17 : Option Hint := some (0x88032000000440004800000002000c00000, 22, 17)
def hint18 : Option Hint := some (0x2830400000000a83005, 0, 18)
def hint19 : Option Hint := some (0xbb0500003f076b500000776e81b0200000fa038, 3, 19)
def hint20 : Option Hint := some (0x528800000000292d00000000000, 44, 20)
def hint21 : Option Hint := some (0x294592b0000000000000000000000000000, 112, 21)
def hint22 : Option Hint := some (0x770373981b0200000000000003f07ddba0fa038, 3, 22)
def hint23 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 23)
def hint24 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 24)
def hint25 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 25)
def hint26 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 26)
def hint27 : Option Hint := some (0x5b802c001b8000000000000005b81b74035b73, 0, 27)
def hint28 : Option Hint := some (0x5b802c001b8000000000000005b81b74035b73, 0, 28)
def hint29 : Option Hint := some (0xb002c01c180736869601cd4079e, 1, 29)
def hint30 : Option Hint := some (0xb002c01c180736869601cd4079e, 1, 30)
def hint31 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 31)
def hint32 : Option Hint := some (0x982f40680004c02e800b00000602dd00dae, 1, 32)
def hint33 : Option Hint := some (0x982f40680004c02e800b00000602dd00dae, 1, 33)
def hint34 : Option Hint := some (0x7398000003872dbda0000b1c6dd, 0, 34)
def hint35 : Option Hint := some (0x7398000003872dbda0000b1c6dd, 0, 35)
def hint36 : Option Hint := some (0x1ffbfefdf7df3db, 0, 36)
def hint37 : Option Hint := some (0x739800003bb76c0580000b1c6dd, 0, 37)
def hint38 : Option Hint := some (0x739800003bb76c0580000b1c6dd, 0, 38)
def hint39 : Option Hint := some (0x5bb02dc01ba000000000000000381a34034b73, 0, 39)
def hint40 : Option Hint := some (0x5bb02dc01ba000000000000000381a34034b73, 0, 40)
def hint41 : Option Hint := some (0x90000000000000000, 64, 41)
def hint42 : Option Hint := some (0xdd068d8036869b006c0005800368696000d40f86, 1, 42)
def hint43 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 43)
def hint44 : Option Hint := some (0xbbbdd0002c0597bd8000000002dbda0000b00ec5, 0, 44)
def hint45 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 45)
def hint46 : Option Hint := some (0x777bb7bdddbba0000000000001c0380000700bc3, 0, 46)
def hint47 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 47)
def hint48 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 48)
def hint49 : Option Hint := some (0xd8006c005800d80377406dd005801b74035f70, 4, 49)
def hint50 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 50)
def hint51 : Option Hint := some (0xbdec00000005eeee858b00000f6ed02cde8, 3, 51)
def hint52 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 52)
def hint53 : Option Hint := some (0xf7bbddddbbb7400000e1c01c7d8, 3, 53)
def hint54 : Option Hint := some (0x7007398030000000000000000701ddba03a000, 13, 54)
def hint55 : Option Hint := some (0x982f686e0004c02ed80bc0000602dd40dae, 1, 55)
def hint56 : Option Hint := some (0xb00000007016b500000776e80300000003a000, 13, 56)
def hint57 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 57)
def hint58 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 58)
def hint59 : Option Hint := some (0xd6ab400028003b6f5a000e80000, 19, 59)
def hint60 : Option Hint := some (0x5bb02dc01ba000000000000005be1b77035b73, 0, 60)
def hint61 : Option Hint := some (0xad67b6f400054000680000000a000e80000, 19, 61)
def hint62 : Option Hint := some (0xd0380001a076803b500e80001403a000000, 25, 62)
def hint63 : Option Hint := some (0x739800003bb76dbda0000bdf6dd, 0, 63)
def hint64 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 64)
def hint65 : Option Hint := some (0xcf6067404f40ce800000000004f40000000000, 42, 65)
def hint66 : Option Hint := some (0x50000000600500000000c800020000000030, 4, 66)
def hint67 : Option Hint := some (0x2807401a040018, 3, 67)
def hint68 : Option Hint := some (0x902800000004802a0000000004028000000, 27, 68)
def hint69 : Option Hint := some (0x70038000600700037000d800060036000f30, 4, 69)
def hint70 : Option Hint := some (0x3f060000000075eb8000000000eece8, 3, 70)
def hint71 : Option Hint := some (0x3f07cf9e0de3d8, 3, 71)
def hint72 : Option Hint := some (0x90000000500090000000640001000000030000, 16, 72)
def hint73 : Option Hint := some (0xa03280191006000000000000000, 61, 73)
def hint74 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 74)
def hint75 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 75)
def hint76 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 76)
def hint77 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 77)
def hint78 : Option Hint := some (0x9dd000005d809d8000006d0001da0000035e45, 0, 78)
def hint79 : Option Hint := some (0xb03ac01d9807740680000d00786, 1, 79)
def hint80 : Option Hint := some (0x5bb02dc01ba000000000000005b81b40035b43, 0, 80)
def hint81 : Option Hint := some (0x81000000000000000, 60, 41)
def hint82 : Option Hint := some (0xcf6067404f40ce803438050c04f40143001007, 0, 81)
def hint83 : Option Hint := some (0x50000000000500000000c000020000000030, 4, 82)
def hint84 : Option Hint := some (0x4b00140001003, 0, 83)
def hint85 : Option Hint := some (0x30f0c1, 0, 84)
def hint86 : Option Hint := some (0xbbbdd000240497bd8000000002dbda0000900e84, 2, 85)
def hint87 : Option Hint := some (0x777bb7bdddbba000000000000140280000500b82, 1, 86)
def hint88 : Option Hint := some (0x81000000000000000, 60, 15)
def hint89 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 87)
def hint90 : Option Hint := some (0x980000005800980000006dd001800000035e70, 4, 88)
def hint91 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 89)
def hint92 : Option Hint := some (0xd6ab41c1a8307b6f5a1c3e83007, 0, 90)
def hint93 : Option Hint := some (0x980368680004c0005800000006000d40d86, 1, 91)
def hint94 : Option Hint := some (0x982f68680004c02ed80000000602dd40d86, 1, 92)
def hint95 : Option Hint := some (0x7d03800060076803b000c80007403a000030, 4, 93)
def hint96 : Option Hint := some (0x9dd0000005809d800000000001da0000000e45, 0, 94)
def hint97 : Option Hint := some (0x300180002000000000000000060032000030, 4, 95)
def hint98 : Option Hint := some (0xb03ac01d9807768696000d40786, 1, 96)
def hint99 : Option Hint := some (0x700380007a076803b500e800060032000030, 4, 97)
def hint100 : Option Hint := some (0x5bb02dc01ba000000000000000380000000b43, 0, 98)
def hint101 : Option Hint := some (0xb002c0001800368696000d40786, 1, 99)
def hint102 : Option Hint := some (0x88, 3, 100)
def hint103 : Option Hint := some (0x900240000800320012000c00000, 22, 101)
def hint104 : Option Hint := some (0x980368680004c0005800000006000d40d86, 1, 102)
def hint105 : Option Hint := some (0x982f68000004c02ed80000000602dd40000, 18, 103)
def hint106 : Option Hint := some (0xb03ac01d9807768016000d40000, 18, 104)
def hint107 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 105)
def hint108 : Option Hint := some (0x1ffbfefdf7df3db, 0, 106)
def hint109 : Option Hint := some (0x88, 3, 107)
def hint110 : Option Hint := some (0x39cddbba00000000000000000f6ed7009c3, 0, 108)
def hint111 : Option Hint := some (0x4000080000000000000000, 67, 109)
def hint112 : Option Hint := some (0x3188000000000000000000000d4a8000000, 27, 110)
def hint113 : Option Hint := some (0x739800003bb76dbda0000bdf6dd, 0, 111)
def hint114 : Option Hint := some (0x631000003326000000000000000, 61, 112)
def hint115 : Option Hint := some (0xad67b6f4000542c2e870c0000a0c1e83007, 0, 113)
def hint116 : Option Hint := some (0x88030000000440000000000002000c00000, 22, 114)
def hint117 : Option Hint := some (0xa0c1600003, 0, 115)
def hint118 : Option Hint := some (0xdd048d8036849b006c0005800368496000d40e84, 2, 116)
def hint119 : Option Hint := some (0x777bb7bdddbba0000000000000c0180000300ac1, 0, 117)
def hint120 : Option Hint := some (0x4000080000000000000000, 67, 118)
def hint121 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 119)
def hint122 : Option Hint := some (0x39cc000000000000000000000f6ed02c9e8, 3, 120)
def hint123 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 121)
def hint124 : Option Hint := some (0xd6ab41c1a8307b6f5a1c3e83007, 0, 122)
def hint125 : Option Hint := some (0x28014018040018, 3, 123)
def hint126 : Option Hint := some (0xb0000003f060b000000776a8030000000fa028, 3, 124)
def hint127 : Option Hint := some (0x739800003bb76dbda0000b006c5, 0, 125)
def hint128 : Option Hint := some (0x3f076b500000776e8000000000ea028, 3, 126)
def hint129 : Option Hint := some (0x7398000000002dbda0000b006c5, 0, 127)
def hint130 : Option Hint := some (0x210, 4, 128)
def hint131 : Option Hint := some (0x8d40000000008c800000000000d00000000000, 44, 129)
def hint132 : Option Hint := some (0x9dd0000005809d800000000001da0000000e45, 0, 130)
def hint133 : Option Hint := some (0x9dd0000058009d8000006d0001da0000035000, 12, 131)
def hint134 : Option Hint := some (0x739800003bb76dbda0000000000, 41, 132)
def hint135 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 133)
def hint136 : Option Hint := some (0x1ffbfefdf7df3db, 0, 134)
def hint137 : Option Hint := some (0x39cddbba0000000000000000000007009c3, 0, 135)
def hint138 : Option Hint := some (0x210, 4, 136)
def hint139 : Option Hint := some (0x80000000000004000, 14, 41)
def hint140 : Option Hint := some (0x50002800100000000000000005001900030000, 16, 137)
def hint141 : Option Hint := some (0xd6ab41c1a8307b6f5a1c3e83007, 0, 138)
def hint142 : Option Hint := some (0x631000000306000000000000000, 61, 139)
def hint143 : Option Hint := some (0x900240000800300000000c00000, 22, 140)
def hint144 : Option Hint := some (0xdd028d8036829b006c0005800368296000d40b82, 1, 141)
def hint145 : Option Hint := some (0xbbbdd0000c0197bd8000000002dbda0000300ac1, 0, 142)
def hint146 : Option Hint := some (0x80000000000004000, 14, 15)
def hint147 : Option Hint := some (0xff07f7b83f07ef77bbbb776e83f07ddba0fa038, 3, 143)
def hint148 : Option Hint := some (0xb03ac01d980740000001c000798, 3, 144)
def hint149 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 145)
def hint150 : Option Hint := some (0xcf6067404f40ce803438050c04f40143001007, 0, 146)
def hint151 : Option Hint := some (0x7000380030000000000000003f07dd9a0fa018, 3, 147)
def hint152 : Option Hint := some (0x7398000000000000000003f07ddba0da018, 3, 148)
def hint153 : Option Hint := some (0x40000000000000000000000001000000, 24, 149)
def hint154 : Option Hint := some (0x4b2025400b0000000000000000000000000000, 112, 150)
def hint155 : Option Hint := some (0x39cddbba0000000000000000000007009c3, 0, 151)
def hint156 : Option Hint := some (0x5bb02dc01ba000000000000005801b40035000, 12, 152)
def hint157 : Option Hint := some (0x39cddbba00000000000000000f6ed000000, 24, 153)
def hint158 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 154)
def hint159 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 155)
def hint160 : Option Hint := some (0x40000000000000000000000001000000, 24, 156)
def hint161 : Option Hint := some (0x982c00000004c02e800b00000602d000da8, 3, 157)
def hint162 : Option Hint := some (0xb03ac01d980740000001c000798, 3, 158)
def hint163 : Option Hint := some (0x11000000000000000000000000, 96, 159)
def hint164 : Option Hint := some (0x980000005800980000006dd001800000035e70, 4, 160)
def hint165 : Option Hint := some (0xcf6003400640ce800038000c04f40003000006, 1, 161)
def hint166 : Option Hint := some (0x9dd0000058009d8000006dd001da0000035e70, 4, 162)
def hint167 : Option Hint := some (0x58002c00180000000000000005801b74035b70, 4, 163)
def hint168 : Option Hint := some (0xcf6067404f4006800038000c00640003000006, 1, 164)
def hint169 : Option Hint := some (0x5bb02dc01ba000000000000005801b74035b70, 4, 165)
def hint170 : Option Hint := some (0x11000000000000000000000000, 96, 166)
def hint171 : Option Hint := some (0x9dd0000058009d8000006d0001da0000035000, 12, 167)
def hint172 : Option Hint := some (0x5bb02dc01ba000000000000005801b40035000, 12, 168)
def hint173 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 169)
def hint174 : Option Hint := some (0x1ffbfefdf7df3db, 0, 170)
def hint175 : Option Hint := some (0xbdec00000005eeee848900000f6ed024d60, 5, 171)
def hint176 : Option Hint := some (0xf7bbddddbbb7400000a14014750, 4, 172)
def hint177 : Option Hint := some (0x10080000000000000000000000000000000, 127, 173)
def hint178 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 174)
def hint179 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 175)
def hint180 : Option Hint := some (0x240060000000028000000000001000006, 1, 176)
def hint181 : Option Hint := some (0x982f68000004c02ed80b00000602dd40da8, 3, 177)
def hint182 : Option Hint := some (0xb03ac01d980776801601cd40798, 3, 178)
def hint183 : Option Hint := some (0x10080000000000000000000000000000000, 127, 179)
def hint184 : Option Hint := some (0x5bb02dc01ba000000000000005be1b77035b73, 0, 180)
def hint185 : Option Hint := some (0xd007d0382807a076803b500e82807403a040038, 3, 181)
def hint186 : Option Hint := some (0xa00280181006000000000000000, 61, 182)
def hint187 : Option Hint := some (0x739800003bb740000000001c6d8, 3, 183)
def hint188 : Option Hint := some (0x10000800000000000000000000000000000, 119, 173)
def hint189 : Option Hint := some (0xa803b6d4000540006870c0000a000e83005, 0, 184)
def hint190 : Option Hint := some (0x39cc000000000000000000000f6ed02c9e8, 3, 185)
def hint191 : Option Hint := some (0xad67b6f4000000006870c00000000a83005, 0, 186)
def hint192 : Option Hint := some (0x39cddbba00000000000000000f6ed02c9e8, 3, 187)
def hint193 : Option Hint := some (0x10000800000000000000000000000000000, 119, 179)
def hint194 : Option Hint := some (0x982f68000004c02ed80000000602dd40000, 18, 188)
def hint195 : Option Hint := some (0x39cddbba00000000000000000f6ed000000, 24, 189)
def hint196 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 190)
def hint197 : Option Hint := some (0x1ffbfefdf7df3db, 0, 191)
def hint198 : Option Hint := some (0xd8006c005800d80376406d9005801b64035d60, 5, 192)
def hint199 : Option Hint := some (0xf7bbddddbbb740000060c00c5c8, 3, 193)
def hint200 : Option Hint := some (0x100000002000000000000000000000000000, 109, 194)
def hint201 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 195)
def hint202 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 196)
def hint203 : Option Hint := some (0x739800003bb76dbda000001c6d8, 3, 197)
def hint204 : Option Hint := some (0x7398000003872dbda000001c6d8, 3, 198)
def hint205 : Option Hint := some (0x100000002000000000000000000000000000, 109, 199)
def hint206 : Option Hint := some (0xbb0500003f076b500000776e81b0200000fa038, 3, 200)
def hint207 : Option Hint := some (0x10000000000001000000000000, 48, 159)
def hint208 : Option Hint := some (0xd003400028003b6b5a1c3e83003, 0, 201)
def hint209 : Option Hint := some (0xd6a8000000003b6f5a1c3683003, 0, 202)
def hint210 : Option Hint := some (0x10000000000001000000000000, 48, 166)
def hint211 : Option Hint := some (0xb03ac01d9807768016000d40000, 18, 203)
def hint212 : Option Hint := some (0x739800003bb76dbda0000000000, 41, 204)
def hint213 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 205)
def hint214 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 206)
def hint215 : Option Hint := some (0xd8006c005800d80375406d5005801b54035750, 4, 207)
def hint216 : Option Hint := some (0xbdec00000005eeee818300000f6ed00c5c8, 3, 208)
def hint217 : Option Hint := some (0x10000000000000000000000004000000000, 38, 173)
def hint218 : Option Hint := some (0xeeef6ef77b6f5deef43c3e870fb6f5a1c3e83007, 0, 209)
def hint219 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 210)
def hint220 : Option Hint := some (0x10000000000000000000000004000000000, 38, 179)
def hint221 : Option Hint := some (0x50002800100000000000000000001800030000, 16, 211)
def hint222 : Option Hint := some (0x9dd000005de00580000000dc004a0000000e34, 2, 212)
def hint223 : Option Hint := some (0x770373981b0200000000000000701ddba03a000, 13, 213)
def hint224 : Option Hint := some (0x20001000000000000000000000000000000, 120, 214)
def hint225 : Option Hint := some (0x982f686e0004c02ed80bc0000602dd40dae, 1, 215)
def hint226 : Option Hint := some (0x4e000000000009c00000000000c24, 2, 216)
def hint227 : Option Hint := some (0x1ffbfefdf7df3db, 0, 217)
def hint228 : Option Hint := some (0xbb05000007016b500000776e81b02000003a000, 13, 218)
def hint229 : Option Hint := some (0xcf6067404f40ce803400050004f40140001000, 12, 219)
def hint230 : Option Hint := some (0x810000000, 28, 220)
def hint231 : Option Hint := some (0x982f686e0004c02ed80bc0000602dd40dae, 1, 221)
def hint232 : Option Hint := some (0xb038000000003686f601f54039a, 1, 222)
def hint233 : Option Hint := some (0x80400000000000000000000000000000000000, 142, 223)
def hint234 : Option Hint := some (0x5b802c001b8000000000000005b81b40035b43, 0, 224)
def hint235 : Option Hint := some (0x2e0017000312, 1, 225)
def hint236 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 226)
def hint237 : Option Hint := some (0x20000000000000000000000008000000000, 39, 214)
def hint238 : Option Hint := some (0xb03ac01d98077686f601fd4079e, 1, 227)
def hint239 : Option Hint := some (0xd000d0382801a076803b500e82801403a040000, 18, 228)
def hint240 : Option Hint := some (0xad67b6f4000542c2e80000000a0c1e80000, 19, 229)
def hint241 : Option Hint := some (0x10020000000000000000000000000000, 113, 230)
def hint242 : Option Hint := some (0x9dd000005de09d8000006ddc01da0000035e75, 0, 231)
def hint243 : Option Hint := some (0x5de09d8000006ddc00000000025c65, 0, 232)
def hint244 : Option Hint := some (0xd6ab41c1a8307b6f5a000e80000, 19, 233)
def hint245 : Option Hint := some (0x20000000020000000000000000, 65, 234)
def hint246 : Option Hint := some (0x1ffbfefdf7df3db, 0, 235)
def hint247 : Option Hint := some (0x100000000000008000, 15, 236)
def hint248 : Option Hint := some (0x5bb02dc01ba000000000000005be1b77035b73, 0, 237)
def hint249 : Option Hint := some (0x2dc0000000000000000005be1b77015353, 0, 238)
def hint250 : Option Hint := some (0x4000800000000000000, 59, 239)
def hint251 : Option Hint := some (0x2ffde000000007dfbc00000000befced, 0, 240)
def hint252 : Option Hint := some (0x39cdc03800000000000000000f6ed7009c3, 0, 241)
def hint253 : Option Hint := some (0x1b0200000da018, 3, 242)
def hint254 : Option Hint := some (0x7000000038002db9a0000bdf2d9, 0, 243)
def hint255 : Option Hint := some (0x200004000000000000000000000000000, 110, 244)
def hint256 : Option Hint := some (0x739800003bb76c0580000b006c5, 0, 245)
def hint257 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 246)
def hint258 : Option Hint := some (0x3cf0c9, 0, 247)
def hint259 : Option Hint := some (0x10000000000000000000000000400000, 22, 230)
def hint260 : Option Hint := some (0x739800003bb76dbda0000bdf6dd, 0, 248)
def hint261 : Option Hint := some (0x80000000400000000000000000000000000000, 118, 223)
def hint262 : Option Hint := some (0x39cddbba00000000000000000f6ed7ef9eb, 0, 249)
def hint263 : Option Hint := some (0x9dd000005de09d80000068d001da0000034e70, 4, 250)
def hint264 : Option Hint := some (0x38000003bb3403800000bdf4cd, 0, 251)
def hint265 : Option Hint := some (0x100000000000000000000000002000000, 25, 252)
def hint266 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 253)
def hint267 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 254)
def hint268 : Option Hint := some (0x1ffbfefdf7df3db, 0, 255)
def hint269 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 256)
def hint270 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 257)
def hint271 : Option Hint := some (0xb002c0001800368696000d40786, 1, 258)
def hint272 : Option Hint := some (0x9dd0000005809d800000000001da0000000e45, 0, 259)
def hint273 : Option Hint := some (0x5bb02dc01ba000000000000000380000000b43, 0, 260)
def hint274 : Option Hint := some (0x58002c00180000000000000005801b74035b70, 4, 261)
def hint275 : Option Hint := some (0x982c00000004c02e800b00000602d000da8, 3, 262)
def hint276 : Option Hint := some (0x739800003bb740000000001c6d8, 3, 263)
def hint277 : Option Hint := some (0x1ffbfefdf7df3db, 0, 264)
def hint278 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 265)
def hint279 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 266)
def hint280 : Option Hint := some (0x1ffbfefdf7df3db, 0, 267)
def hint281 : Option Hint := some (0x982c00000004c02e800b00000602d000da8, 3, 268)
def hint282 : Option Hint := some (0xb002c0001800368696000d40786, 1, 269)
def hint283 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 270)
def hint284 : Option Hint := some (0x9dd0000005809d800000000001da0000000e45, 0, 271)
def hint285 : Option Hint := some (0x739800003bb740000000001c6d8, 3, 272)
def hint286 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 273)
def hint287 : Option Hint := some (0x58002c00180000000000000005801b74035b70, 4, 274)
def hint288 : Option Hint := some (0x39cddbba0000000000000000000007009c3, 0, 275)
def hint289 : Option Hint := some (0x1ffbfefdf7df3db, 0, 276)
def hint290 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 277)
def hint291 : Option Hint := some (0x6f003c006e00780037800dc006e0037000f36, 1, 278)

-- The lookup table selects a suggested restriction. The usable predicate checks its validity.
def saltAtChunkBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x120c107100000600602105618896160cf96000c2861a0040128013ae else 0x16281000c04005080001100149831c04484083c68100041060600181) else (if i < 3 then 0x4a4a160000b0b180078700000050a20102205841770086041008080 else 0xa0038e220c08f0200e02020402e44143160a28302083c200021400a)) else (if i < 6 then (if i < 5 then 0xcc022e40101000010a16002882c0c107020448234042990800994 else 0x20081a0000843006441010414006005400016ac403020c2011c00484) else (if i < 7 then 0xe90487002821a000008400183000a0010a040048e00044b60005283 else 0x2b20080160410106140000010202082000200000000224400040071f))) else (if i < 12 then (if i < 10 then (if i < 9 then 0xe0538c12287083c0c0000404c0222212100e3010a0c000880010602 else 0x141428008101060004b09263878904440020024f03101050c248c000) else (if i < 11 then 0x64850002145970048e13080c0025a001800204091020c0812200e09 else 0x1e081050c00100781408206001090000087082009f0c103951800181)) else (if i < 14 then (if i < 13 then 0x32404990434d840ca418200001000e100011c000802030180004c883 else 0x8080830270e0d020630118101972408081000428102041050800d8f) else (if i < 15 then 0x468000516180040c0c90c6e082810a1de833a7011b140c009020832b else 0x24c20300140071800120013810108001ea060420000280000280100))))
def saltAtChunkBlock1 (i : Nat) : Nat :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x42400022230204082c0070e04001142400b240061a1444e8b3804011 else 0x38001010e04007046c08c0a2960e0014082280000002140180c1c80a) else (if i < 19 then 0xe383a51e7c180004c32f0e041840a003030c2c082082048a0e08402 else 0x1c4409700403040c003800400580020428332040050a1000ab81988a)) else (if i < 22 then (if i < 21 then 0xc1c1020018416048029b02059860e1000514142ad2a002040004d02 else 0x63cb96120c02b76042801a0c09a06380001c04185148d1940228110) else (if i < 23 then 0x43cc0502043001a1408f300080212105846e2878106093000874806 else 0xe140902c3c2c40200184660c199441008100041190c19887104c186))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x183000235500062c4840a2030c06181020a00c03100478d0600603 else 0x143428728002021a00581086c18604140250a00a02021da02001040a) else (if i < 27 then 0x4440870e502873668385020c1010ea80090414a9112481100424b00 else 0x6185811005303020500efa5540626045ac0e2cd0730280050121e07)) else (if i < 30 then (if i < 29 then 0x123408f083428c069c00708b0107000088902000050828287625071c else 0x80870c1a04703420cc80181040c3c264011a0c1840c0c8807a44097) else (if i < 31 then 0x11010c301001a2802c180c8801c000001414729081c0c20a14688 else 0x2a3c000082030126180100a0048016280070ac809f120c1990404021))))
def saltAtChunk (i : Nat) : Nat :=
  match i / 16 with
  | 0 => saltAtChunkBlock0 i
  | 1 => saltAtChunkBlock1 i
  | _ => 0

def saltAt (i : Nat) : Nat :=
  ((saltAtChunk (i / 32)) >>> ((i % 32) * 7)) % 128

def slotAtChunkBlock0 (i : Nat) : Nat :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then 0x21300114009b000000000310100005010102a002213802030012c3444000000b16 else 0x10c12000004c0000698009c140011000008600000000000000e60080c0000000040600) else (if i < 3 then 0x228181000229102400000000000008008813000486000271148abf011881002220097e00 else 0x880067210000a0b0000a130004c00430010c00430500010000008c1000000000043)) else (if i < 6 then (if i < 5 then 0x44e218000001220048a021e0000000000001124002e4004422008000000000c400 else 0x2484800160a81400000000c00432200000050000000420000c8800249140000218000044) else (if i < 7 then 0x800008600000000011000430005092441f80000007e00800010101488000000c0000 else 0x28000001000080043000000403008009200219148813000040000218000000))) else (if i < 12 then (if i < 10 then (if i < 9 then 0x40001000140c082205c0016000102a0001800248f0000c0000000000016020001000 else 0xb00400450011400003880810020011508430680c00ba22000900022000001600800c400) else (if i < 11 then 0x2484c000000002267224800000200018104301028f60021808887101804026300001b444 else 0x40000000030012404020016c0000030016a00000000000001c40043000501a02)) else (if i < 14 then (if i < 13 then 0x40000000248580644478008606228008600000088601041142612008041005001100003 else 0xb858000005000000022000101300000884401afc34430110c000000800c416021102e16) else (if i < 15 then 0x10c00002180086002191456430000026040005400000000088120000800652480c0044 else 0x30000000080108026000026c0000218000071128000c08000000443000010800))))
def slotAtChunkBlock1 (i : Nat) : Nat :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then 0x10580062228300c0021820000021800861602000000c000000000000140000008580000 else 0x3b082000000800150022802160100000000100000b92200c0045248000400000002a00) else (if i < 19 then 0x1400000000800450005800000002000002190c080006800d00000000bc00021580000 else 0x581a4509800000000010866200004d60100020000000010000000048c400000002600)) else (if i < 22 then (if i < 21 then 0x1000e40600001d800221388843000000411088000c0400014000000000000212c2c0044 else 0xb1140c00028040600000340002000001aa8000002c002180000000010c0600540080000) else (if i < 23 then 0x1910681500048e60a2181800005b8000000000000012000000000250580000001140005 else 0x1800000000010023f0900010150a80088000000086030000000435c8000000001780008))) else (if i < 28 then (if i < 26 then (if i < 25 then 0x2180000000111000000000800030000000002580088e2010000400000000000008017874 else 0x251c400000000000490980000000000000002200000000006c86000190c000000114000a) else (if i < 27 then 0x2a0080a45218208800000583c000010c001522000104400000000000124000d1c90c0003 else 0x900002000791404000280000000000000000000000002185800002186414080010e1c00)) else (if i < 30 then (if i < 29 then 0x2210c0413000000002868580000218000482270202a000021472030010c0006000002600 else 0xa4800008004400000000000198000f308640000001141e080042c22000010c1000) else (if i < 31 then 0x218000000040000400010000000010008600218000000000009200000008a00010000000 else 0x38800264501854881300000000800000870c00000000001008000121800880000800004b))))
def slotAtChunkBlock2 (i : Nat) : Nat :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then 0x8860300014000022aa00000000000000860002613220180003000000849018288600 else 0x21800e20031000ca002186814001880c000000000040021b6c00000000c0013018001400) else (if i < 35 then 0x1004ea17218081a002190c00000010c3600000008a00000000000000002c00000000000 else 0xb0000045000011c002500092000010c0804028082400010000643000588a00218011a00)) else (if i < 38 then (if i < 37 then 0x10c24440000000000028c0000001380011010540071000000002000000449000000800 else 0x1110864531018000000000000022924000300000000376048180522000104e000100400) else (if i < 39 then 0x2199800000180804000000d3600000140000000000045761c40003221140076002e40000 else 0x110d70060000800430a8340208510000043020080449000200c12021102c00008008a4a))) else (if i < 44 then (if i < 42 then (if i < 41 then 0x280400000000086000010c100422801cc02229380c00019140000000001400229f00043 else 0x100000003110c0612218000202040000008000000000003c40000000000600001108800) else (if i < 43 then 0x28000000000580043000552000228000000000008a002180002000100000050b00c2c43 else 0x404c043c0101804000000000000011402435c80000060980000002190c00000004c0000)) else (if i < 46 then (if i < 45 then 0x8008801001140025000000000311100000248000000011149c6200018000800000009b else 0x2c0522001c400002fc0602068008a0000000920001000e400020008a000000c0643) else (if i < 47 then 0x908003100000000026c00110001800000000000000010c0000000000400000023608 else 0x2006440000000000004c00005b000000006914000009000061601129d80200001d800))))
def slotAtChunkBlock3 (i : Nat) : Nat :=
  (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then 0x10c0801000000008000000043000009244000000000010542600000200844 else 0x229c498000010c00002218800002280800030000c00840000c00440010c044a21b3c0000) else (if i < 51 then 0x1140000310000000000000004040000002008000600388000000228000000220000444 else 0x680000001e0000000000001a450000c00050004c0000010000000001348800000000600)) else (if i < 54 then (if i < 53 then 0x6000000002012210c2a000000c9c150004c0002008007e00219100203069157200 else 0x248008a0d000548a00040008816090482200311f400450110c10012210c1a00098000008) else (if i < 55 then 0x4c8800000000a00218013600000008a4500a9400020000000020010c0000000588800 else 0x218080000000000000008000000228000400000000208000000200))) else (if i < 60 then (if i < 58 then (if i < 57 then 0x2280000450000000370000400000001000000410c000000000000000000d000000008a44 else 0x44504800000000000000001800000005014040400000411c3880c0002000000055) else (if i < 59 then 0x1108a4300000040b22800020d000000a008d10c0000010008a05000000400150009215 else 0x10c8603248140a4500004000000000000021804000001001c400000000001000000c00)) else (if i < 62 then (if i < 61 then 0x10000b008004a0005400138182000122290e10450080000003110c00002190c0002 else 0x8a002180000000000c042e00000004501008000d4d80000003d8008a003400c0416) else (if i < 63 then 0x88002500404032210c1211041149a000101424003084c00190001414180011086f7 else 0x8000600000100617000180000001100000228000208090000000078000000))))
def slotAtChunkBlock4 (i : Nat) : Nat :=
  (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then 0x18800000000000000000000000000088030080086022280086a30000c000022800864f else 0x2180000120b00000000d8000002000000a000000086440111400440980000000010c8600) else (if i < 67 then 0x219101000000000000228000000000000013000002a08220002c000000c00000b0000000 else 0x1c00000104800002200086442200000120000000000012c00032290c0000)) else (if i < 70 then (if i < 69 then 0x4ec00914860a090080000000000200000000045018001045228000013218000000 else 0x860000000860000058000025014e20000000001304000000d668000000000200061) else (if i < 71 then 0x1000860101000005e0011404430000000150100000151293000001d801f000000080604 else 0x40001a00000000043470580000000100000002e400010000004000980c0008388000000))) else (if i < 76 then (if i < 74 then (if i < 73 then 0x180006000010c0000000088602030480044000002802019153600000082643218001e16 else 0x8a4a3100000000000000bc000480003218000000000009402078000002000000000) else (if i < 75 then 0x9d844089140200220800000000000000010008608218000200310000000050000200 else 0x38ba8c40a0000012012180c0045220000800218002d07058197800010008a02000017200)) else (if i < 78 then (if i < 77 then 0x3000000580000391100000079102c1f00114009a7601800000000000432200c0643 else 0x1124000201910006201114260001800007300004000000000046800060002e010000000) else (if i < 79 then 0x219880001048d400013800094000005524020010c0042011100012000080003000080603 else 0x14000a80001150000006000011000432e800000000000000024800040009000e401))))
def slotAtChunkBlock5 (i : Nat) : Nat :=
  (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then 0x342a020300000450000c00000021000450000972160104c0000010000045389248602 else 0x2280000150000000000220c003c248000a000290c2662000020400218000043760000a14) else (if i < 83 then 0x10c8c000000000000118c00050a9c88a00020488a00021148600000080044000000003 else 0x60800004140822004000a7600000000000000000100000002480000a2018000443)) else (if i < 86 then (if i < 85 then 0x1114000151000008a0100400020180000133100c00000082400000000004004e0540800 else 0x8800000000014218002a0000000001321a094400000008800000000602040288644) else (if i < 87 then 0x3b000000110c8a437600c0600248f00002018540072000080416000000a00040000045 else 0x4dbb00008000002444660688a0027004246f098180073000000043010080004218090865))) else (if i < 92 then (if i < 90 then (if i < 89 then 0x80000000000000020005c1400249380c000000000b92180000000000c0045020000603 else 0x82600251c4260000114001300010000a000000043010000000000000600228002c00) else (if i < 91 then 0x18400000d800c400000040000000080000018000600270000043000000000018008800 else 0x11280000002e40000000000600000000013000000002220000000000000200550002694)) else (if i < 94 then (if i < 93 then 0x980086010000004020000158153111000002285410150006c2c00000000400008000000 else 0x220000c01248000002390000044248000000000088616050048602760009204020340000) else (if i < 95 then 0x190c06060010c00044ebb02600040000000001140a002190c8a13020190044001148a03 else 0x388000001001248643000042a710a85800005281000000000000000a8000000))))
def slotAtChunkBlock6 (i : Nat) : Nat :=
  (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then 0x1400080190c000300110009741008000d001300000001140013001881021388288645 else 0x11004e1000000a000000812000200000030000000000180000120085800bc000000000) else (if i < 99 then 0x860100001be16010008a000000004720000000000000c0003008000016000548a00 else 0x18020000800920421910004500000260009810086e2480006030000c0043000008843)) else (if i < 102 then (if i < 101 then 0x114004e0180086000100000000181888002f0000043000100045001c40001 else 0x11004050000000fe0000886000000008000000086000000000430000000000b10c0400) else (if i < 103 then 0x2240021800e21600000000000000000000000869b010000800000e80000229340000 else 0x7f800000a020000000000082a00033f8884500000c4ab001280016219100000220000000))) else (if i < 108 then (if i < 106 then (if i < 105 then 0x6120000c9405000008a610000800000000014000400000032280000000a8580000 else 0x100c0615218540000040000000050082c03028000a000900086020001400450081800f6) else (if i < 107 then 0x2000024100010000010c0400003608a010004800002180c1000128000000004688600 else 0x21814c4130000088450300000430000c00000000800be0080000b9328000005000009045)) else (if i < 110 then (if i < 109 then 0x40000000004e229240400000080005218000000008000045000089400218000000 else 0x86000004c064a01ae40400000000015000000000000000045000000043221100043) else (if i < 111 then 0x9800000004000004500000000000020007c000082c00018000000000000043000000037 else 0x8001222000043e040000012009140000000101a0200000860200914868f000000045))))
def slotAtChunkBlock7 (i : Nat) : Nat :=
  (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then 0x32210c86002281402150000000000000000000a80094002190c9c13010000200 else 0x46800860000114040022800280000000000500008bc02030000003000000000000088a00) else (if i < 115 then 0x1422000011406970100010000010c860024804100022000864e218000000100012045 else 0x2002000992800002711486000883c06040685c2a450000004ec000000002001894400)) else (if i < 118 then (if i < 117 then 0x18000212000000000218000062000000000000000000000080200000000002388008600 else 0x1814000209801d8002210cd000000080004218004a000000150050900000a800000c445) else (if i < 119 then 0x8a00000000012000000000000000000000000002000040008000000043000080003 else 0x79218000400000000000250000a430100c1400218008a00219c80004228001003))) else (if i < 124 then (if i < 122 then (if i < 121 then 0x4c8a00000000000000000800000000045000000008000341287000540845040001000 else 0x80000008081200000000000001d400000010c00000001000000191488003400c9ca3) else (if i < 123 then 0xc060000000000021c6c0049003b068002180c0000310080a43000282645 else 0x890c00020900024160111400003300000000990c0000000000002000002c00)) else (if i < 126 then (if i < 125 then 0x218dc04000011000b200000000200188000000110c40049808000800801d8000a8000000 else 0x1189d802018002c432280c24130000492432190c00440000000010d914000002ae40045) else (if i < 127 then 0x104c00002200000000000086001f000244a5184400080011406b9000000000218000000 else 0x1148613000008a445285c860000114000022234000004000004504000100d000000045))))
def slotAtChunkBlock8 (i : Nat) : Nat :=
  (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then 0x1c400162180000000000000490000000050000000000990c0000000000000000dc860d else 0x888710000086000000004002480c0400000340204000480400218580000000080000) else (if i < 131 then 0x1448845000002600000008800128002a000000000000010c8600000100008220000004 else 0xb0000003010000a01040000000218000416001100200002e40000000000a00001108600)) else (if i < 134 then (if i < 133 then 0x40000008030010c0000763b0004900000000022800241300000e600219248800 else 0x390010461000080206000000600860000c00270008a01011142400098009200000001000) else (if i < 135 then 0x10c88430084c8a0000020000003004880000000860000000000000000000000020260a else 0x2580006002281400000500402440100000000004c86020000000000100c0a00010149400))) else (if i < 140 then (if i < 138 then (if i < 137 then 0x220206e000000000000011000000000000020000000000000000440015000135110c0044 else 0x80000000008603000000008098a0004300054004522000060d0010c041e218201043) else (if i < 139 then 0x500228860221bb1e2000100000000000086000b0000002618018200228002643 else 0x2181426000110c04162180000002284c0045218002600000000415000000400248000000)) else (if i < 142 then (if i < 141 then 0x20ac00440111492020000000020000800000005806004d82000010001012030104c0016 else 0x800002190c00000c00000432200000000000000000000006000000006d4000000243) else (if i < 143 then 0x200178488a570005404000014c0013000000000012e400440001400000690c0000 else 0x2190c9e0000000000000048000300000ba00000008800218184a00000080000000000000))))
def slotAtChunkBlock9 (i : Nat) : Nat :=
  (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then 0x1000000003000200000000082612280000000000000000000000a05000000600 else 0xb058040006b8936000010dd914000000043028008600018000a000b111c404010088800) else (if i < 147 then 0x10c0001000088a04010088649000000000000008608021140006091108600218000003 else 0x8a0000000005c2180888082480000440002800002180836000004c0600000000400)) else (if i < 150 then (if i < 149 then 0x44008008800018000000000000044000088600218000008000000000040082c43 else 0x108a000aae48a00000000402000000044218008600001102a00000000000000002a45) else (if i < 151 then 0xc00020280000000010c0000000002aec5c8000000018480012000000813000000003 else 0x20e24e2180c0c005c8002c000000088440a8000045000000601000080000000000401))) else (if i < 156 then (if i < 154 then (if i < 153 then 0x4000000000248000000001c80049068003603000000002001c48606000008800 else 0x20860000000864a00010040800058004521810000000000000022988400000000001b) else (if i < 155 then 0x11408020000002020010c2c00218008600040188845000000000041100013000dc0002 else 0x922486040118800062192800000000800000000000432200000040000000550010c0043)) else (if i < 158 then (if i < 157 then 0x2180002000010c00432710c00e50400000000000000000100c0412219140200220000000 else 0x229980045000000000000202645000002803008000600000008801000000043) else (if i < 159 then 0x643000080001540000013019140000000000000000009c440000c0000 else 0x12c404120000008000d8000000228000416001249400000001208228540008000004a00))))
def slotAtChunkBlock10 (i : Nat) : Nat :=
  (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then 0xc860600000000d228540443000000043219cc0044218000000000000000001240044 else 0x1115d8000011400002290c0000220140000000000400000040008008002c1b00001d800) else (if i < 163 then 0x940001000000000048009b000088603000482e020b11002000000c00430010c0400 else 0x2114867d000080443000000045000208a0000008040100014008a000002a0f000000045)) else (if i < 166 then (if i < 165 then 0x8a01000000002003342800018009400000008844311242c01000000002010000400 else 0x4b124000200020001b228000400000000000000e000000000c0000040000001000000000) else (if i < 167 then 0x20681026080000024000000000492182800000000004490b0008645000000000 else 0x990c10000310c100000000000000000260d00000000021afc0000000008a004d8000000))) else (if i < 172 then (if i < 170 then (if i < 169 then 0x20000818000940000000d00000000084500000060000000000021800020a000080000 else 0x140414218000000700000a1309004860409000881259804c408000000000000008a00) else (if i < 171 then 0x2a080000138450b10cc400000008a00000080000000000042001100071001108a04 else 0x18042c00218040808000301a00248082a00218000013218000043008000015000000000)) else (if i < 174 then (if i < 173 then 0x3100024000785800000000000000010c00000004c00120002000000400000000a9108802 else 0x1154a000004800080010c008606000000000124000000000920000000003f001100603) else (if i < 175 then 0x228092c0010800264a128040003010042c4401000880500000000021810044e008008a00 else 0x10c0a00218080043000000800219114e43050000013218008845100006600021100200))))
def slotAtChunkBlock11 (i : Nat) : Nat :=
  (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then 0x16828000007018020101914001502820000021c4000450011004452291402000010c1808 else 0x1808000000110e243018000000000680402000001016099100603000080000000000000) else (if i < 179 then 0x2d928040001474040100000004a129102c02000024000409102a4e030008a05000000000 else 0xd0c1140449000080003000000000218001800219540400000340045068002600)) else (if i < 182 then (if i < 181 then 0x1c4861621808e60000000040202001fa050010c00000000004f00008d420a000800001 else 0x248004a0000000040000000000500000004500014000002800000000110060276138000d) else (if i < 183 then 0x68180000000100000000080000000000003043b00000010000400068340013001100000 else 0x218000013018008a000000000010000000000000000005c8000000000002c00000080000))) else (if i < 188 then (if i < 186 then (if i < 185 then 0x100004012192c2c00378008a08420000000000008800000000000000000000078000000 else 0x18800080000014000000000000d000000000000000000000000000000000000001100044) else (if i < 187 then 0x4001080000114000400114004400020e6002480086000000086000200c0000001100000 else 0xc000022000000200008000000049d81b098008a04098000600011c40245000000443)) else (if i < 190 then (if i < 189 then 0x38888000004c00000000000040680086080000004000000000040b0000044250008600 else 0x11400050005800000000800000001806170c10c00002190c9c0d000000000000581a00) else (if i < 191 then 0xa1a00000000001043000008800218e5764e0000c8600000000000218000000000200000 else 0x110c400310000000000008a00001282a000000000442282024000000004000005400e2))))
def slotAtChunkBlock12 (i : Nat) : Nat :=
  (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then 0xc10000190c0000710c800001d80888000000000042280026002290c8600000200000 else 0x1000000004000000000000040002800000021800004e00000000024800000000110000d) else (if i < 195 then 0x540000000008602050f0001204000004300110004300004880001800009d229108a02 else 0x3b00400000001043000001a02440001000000000000000080000000000002000003600)) else (if i < 198 then (if i < 197 then 0x4000d218000044000002c003134400002184c0099003942415000000400000540008 else 0x10dd800220000045001cc00620100000007600000008fbb00400000000600010000a44) else (if i < 199 then 0x220000000000008800000580001008208800710000a43000000044000080044219240443 else 0xc00001140400000000000010200000000000002000000005001140443))) else (if i < 204 then (if i < 202 then (if i < 201 then 0xa85410020010c0000421101000000008a000a910860d028000000391141000000008600 else 0x2189400000000092491b800c2000090c8600000001000219280000270081402000081000) else (if i < 203 then 0xa80000a20000004030000800442511000450100004000000000000011136430b0048800 else 0x2c002280c0c00000480c002180c0600760000404001100601010000016011140002)) else (if i < 206 then (if i < 205 then 0x310081119000000a002212802080b1248800000000002000008800001880000228000468 else 0x2180418ec30800004600008000000000040000001d00021800e200310000055028008800) else (if i < 207 then 0x8004e0000000000000000030010c0000000000003000000043000040043 else 0x462000000200000000000000000044219282600000008600000080600000002a44))))
def slotAtChunkBlock13 (i : Nat) : Nat :=
  (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then 0x211000002492800000010c00000000c0000000008602219c88a00000008600098000000 else 0x21910007d5111402430104c10150000c00000000000000110c8608011080a02420000008) else (if i < 211 then 0x22800040c001100000000f8004e00000004431000000021914048d008080c434d800a200 else 0x2204c00432490c2c1b0000000000d80000450980800020110c26020000000000004c000a)) else (if i < 214 then (if i < 213 then 0x58e2000010c00000011400000010c00003880826010200000450010cc443010000200 else 0x1f400000010c8643218500a00018008800000002643000488a00000001000000000000) else (if i < 215 then 0x2184c02000001000002292404001b830000201800000000114020039008011e000000043 else 0x86000000000020000400000000802c20080000ec040e800000b3640000228001400))) else (if i < 220 then (if i < 218 then (if i < 217 then 0x228480013051142602020042a620184536002200088e60100086000010c004500000050c else 0x22895a80a2184810020418800162280144010b13800004d8000000230642c00000000006) else (if i < 219 then 0x420000400248000000228000000000000000010340a49000480000000200400008080c13 else 0x1d8e331110000000000d000570008a0022bb000450980000030100c0000000000000)) else (if i < 222 then (if i < 221 then 0x450b0000043069140000000001200000000c00000000008000001415091102c02 else 0x2e0200029520003048860022008000a0180000030400014440000092060b0000008) else (if i < 223 then 0x100800b90000000000600000430011400710100000080138800000a90c0000228000001 else 0x47f01000080600000064400138060d0000000020000c8800000188600228008868))))
def slotAtChunkBlock14 (i : Nat) : Nat :=
  (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then 0x4c0044000001002000000043000000000000000003218000000010040000010008600 else 0x10c004400048000001800cc430004c88000004c00000000000082290c6e00) else (if i < 227 then 0x326c8600218482a4a001cc00162290c0600228f09c44220007a00048000000000002600 else 0x218801445000001a0200015d8050980400021b8000000000000000088000000002080000)) else (if i < 230 then (if i < 229 then 0x1289c0702000ba000000000002480086000000000000d80000490006c240000001d873 else 0x22114060209110043f0200010620000000000018888ad000007e4300000000c028008603) else (if i < 231 then 0x7100136732211400000000400000400c009b2205486000010c8a00229114600010048845 else 0x41100000000000c130980000000085800720000000030000000450210c00000004c1049))) else (if i < 236 then (if i < 234 then (if i < 233 then 0x40000000090000049228000003001140012000008a13003b01000018002602000009c00 else 0x2290c8a4a220308600000000013000088643040040000630008600218000003130000400) else (if i < 235 then 0x20004a000180000000000a4e2691000000000800020000406022190c0600028008a01 else 0x10000608003e402000000000000000088246080000000011436440010c0002000000000)) else (if i < 238 then (if i < 237 then 0x1400000000086000990c00440290c00430000c00010005400000000000000104c00ec else 0x106005060280000040000000000000000ec000000000000002468001008a00218000000) else (if i < 239 then 0x11400000000c000000059dc00268000000001102c000011000020010c86130000c2c03 else 0x8340000000000400000000071028000443000008600098000000001100600000008600))))
def slotAtChunkBlock15 (i : Nat) : Nat :=
  (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then 0xc0000010000a43040040044010000400760002615000000000000080000010008a82 else 0x18084a0d0098800010000120000000000430b10d1a430011000133b80000ca) else (if i < 243 then 0x92120000000000105400000000000000000000f50000000430010c000021bb02608 else 0x691618000000002000000000000110c86000110c040001000000000000000021814c400)) else (if i < 246 then (if i < 245 then 0x8a440a80086002600800cd0010c88000000c0002003b0000891000e8452710c040f else 0x48a1990988349b010140201000200002001156a49000040000229102c16011140408) else (if i < 247 then 0x10c0000000108a000000000430980168dc3880026450800000002280026440100c0200 else 0x10430002000120712406000000000000010c86008582804000000004ec000008802))) else (if i < 252 then (if i < 250 then (if i < 249 then 0x20000021800000000000000000000064300114000a2180086003100800440000400b9 else 0x2190c04020000000150101004000004c100000000000002a10000000000000600000004a) else (if i < 251 then 0x1c81402000500044000000001221140400228080002000002612000000012028001045 else 0x8a000100000430001886620110c1044010000a16228000400010000000221100000)) else (if i < 254 then (if i < 253 then 0x2800860000000000400001040d0000000000011404620100972000180c0016001140444 else 0x2c00250000000000000400020182600004040043330140003000002c112190c8843) else (if i < 255 then 0x480000450000000450b0341a002192800000023410007f10c0000000008a00098001000 else 0x100000000003c00050a00000440680086000a00000000000000002190c010c010000043))))
def slotAtChunkBlock16 (i : Nat) : Nat :=
  (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then 0x4c0044438088800001140000018100000220000000000f0001500800000200048928a else 0x2280000000980004002291408000b110881500000104300000000000058040004110bc00) else (if i < 259 then 0x1148600000000043218000000019108600000080045001780000020000000000000000 else 0x88800003b08649228000000248048a6100114860000800100022800fa00001100212)) else (if i < 262 then (if i < 261 then 0x22000004422800001604014a0000105400000080000060010c003e0010c0000470100043 else 0x20008600270102443219100000000200008220000000001bc8600000000000000000000) else (if i < 263 then 0xc0003000000000000008a00218584a0609000ec00000000415000000600000540643 else 0x100400000010c040009800000001800003c00050003f2280000000010c0000000080000))) else (if i < 268 then (if i < 266 then (if i < 265 then 0x20000000864400008047309855d8450000000000000000000980006020b3882c03 else 0x13800000100000ba0000000000105400002184c2c03008001000218487200221100000) else (if i < 267 then 0x800d0000002000000010c00000110c8a00040001000028000000270040401040040245 else 0x8000000000000000000000000000040645000780002000000c00000008800000000002)) else (if i < 270 then (if i < 269 then 0x50588843000080001001380043000000c000012400000a81000440880c6e01000000600 else 0xc044900048000a000008a00002dc9200000000002000004c02040000000000000016) else (if i < 271 then 0x10002a02218082c000005400020010c00430000c0400018007800219140002270000043 else 0x404c02030005800000004800000010c06432280400000b10c0400311100111000009244))))
def slotAtChunkBlock17 (i : Nat) : Nat :=
  (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then 0x2180000430010c1400000540000410008a4f003cc64000190c062500000000022c100000 else 0x4d810000000001ea092190cc40000008001a028001000000080049000001000000040004) else (if i < 275 then 0x400010180000000012400000007408440000c8a02000080200000588a00000000000 else 0x620110c100002800860121800864501000000000000064e0000002000010c0000)) else (if i < 278 then (if i < 277 then 0x11000000d04886000010c00002200000000000000000010da000000000000003b08a00 else 0x880006800c4000000008432280026b92280000000000000000190c0013000280000) else (if i < 279 then 0x58000000001360500000007100000ca000510c00110000000000900000000004c0002 else 0x8602000000645000008a452210800000006c0003001240000000001045000000000))) else (if i < 284 then (if i < 282 then (if i < 281 then 0x22ae400680b0000043000080400228008600000000044000000000000048a000783c0043 else 0x220000000211140043008000c002211086012191400000100c0049000200000760000045) else (if i < 283 then 0x26000980000c40002006000c9240400218000006008000000000000c1500014ba13 else 0x98001a44000000616000000002218000045018040200000000000000009601220000005)) else (if i < 286 then (if i < 285 then 0x5c90c2600478088600000008a00001249c00010080000001100c45228000000098000600 else 0xc858000d000080016000000000000040000000000000000000000000080044000000000) else (if i < 287 then 0x86002184800000000000002490c0000001108600000000c08000000000218008813 else 0x21858000a3100008030400000453113800000000000490145400450000c8600030040200))))
def slotAtChunkBlock18 (i : Nat) : Nat :=
  (if i < 296 then (if i < 292 then (if i < 290 then (if i < 289 then 0x4d910020004021e200001100015078040003000000005220000400000000002050008600 else 0x3880800432180000130000000035c80000430000000000010c2403000340044001253602) else (if i < 291 then 0x2182000440000c149b00000c400040000601228081a430004c0043010008643219140002 else 0x68002a002200088000908c00000190c02020029a3cec2200400430004d100301114c400)) else (if i < 294 then (if i < 293 then 0x60019000000080013218000a490180000131f000924400034000021bb0c40004020000a else 0x31116801218341012000000118000008600000000043001400644008000400162e40a08) else (if i < 295 then 0x228000003040000043000009c00000008862000080105000000000000000000000000003 else 0x4710c00000000000112280088000002888000400000000110c00450010cfa02030580004))) else (if i < 300 then (if i < 298 then (if i < 297 then 0x228000017220000a430001400000080002160b0000400028540043010140000018000804 else 0x99140000228080013001ac8a030a8002c004d81146003a8040000000000000000048800) else (if i < 299 then 0x4c000000000066c0980000430000000430010c8600388000045220000000861101400 else 0x280000098000000040000012000000000000000000000580405000007800251100000)) else (if i < 302 then (if i < 301 then 0x50000000160b1282406091880043000480c1262000000200188000303000a608 else 0x2820000a2480800000010c00030b8340002000000000000000049010000000010000043) else (if i < 303 then 0x2bc78000000086250910c00000b00086080000c00020500000250000004430a8080004 else 0x110c8600220000000001a00016000000045000000000000000000000140008010080012))))
def slotAtChunkBlock19 (i : Nat) : Nat :=
  (if i < 312 then (if i < 308 then (if i < 306 then (if i < 305 then 0x22000000000000004e000002444089140449000000000468f806020d8000000000000000 else 0x4c04002280000433985400000000000000097400d52191400000010c000000008001c) else (if i < 307 then 0x88000000010000100086000000000020900008000aa000044018108a00000000400 else 0x43000000000000000000218008600000008a023a0100043018182c08000000043)) else (if i < 310 then (if i < 309 then 0x2700000000680002180005800000000c00080010c00000001010020000000442180006ec else 0x430001086008a0000c2d010201043000200400000000000010002600000000000) else (if i < 311 then 0x1240015228000204000000044000dc861300000000022801c408229897a43000000003 else 0x58040000025d20d098100002000008600001240000000000000010000000000180000))) else (if i < 316 then (if i < 314 then (if i < 313 then 0x5c9148801000002a49000000003001100001008004a0222000000821814e200000008600 else 0x2210c26010000c000000000920d711100000000000603000540005010080000000000000) else (if i < 315 then 0x100c04000010c10002180088000b0000012001248a430090c0000001140400001880444 else 0xec0300004000180000440104c000000000860a000002400228000008)) else (if i < 318 then (if i < 317 then 0x9000004322008144600010004300800d000000000443000000043010001000068008862 else 0x110c0608000000200001100000000200000010001000000000000000000000000000000) else (if i < 319 then 0x3100000020680000f5388000000000000000000000008018000600218002600000000015 else 0x22058000521914887104000044300004861521800009b0002006000a84800020000c0000))))
def slotAtChunkBlock20 (i : Nat) : Nat :=
  (if i < 328 then (if i < 324 then (if i < 322 then (if i < 321 then 0x18088a00000000000000008a122200000430011000000110c00010100c06002290c0000 else 0x2200000030010c040000000000000000100021a6c86040b1248a4e000094a00) else (if i < 323 then 0x4300008000500020860200008004e0042c00000000000000a800004a else 0x304c0000090040000218a400000011402000004c364306848000801aa97616001380004)) else (if i < 326 then (if i < 325 then 0xc86003100c004300001da0001808860f01800884a218580600000080000000000000 else 0x886200011000000b00000e00000000000000004ec218000000) else (if i < 327 then 0x905c00022280814490000000052180488005e0002401018000000310008600000000000 else 0x1000000280000000000000000011000000000800000001400010004c0000228056000))) else (if i < 332 then (if i < 330 then (if i < 329 then 0x3092002180000022f810860056000000d000f000000510c8a430000888032190c8800 else 0x8a020000c000000000040024a7800000010e1245018040000218000000000000600) else (if i < 331 then 0xb1948805040e00000000009443000008645229c486089080c86020000000000004c0044 else 0x5886005c8480000018000043220000002001280412248001a0a2290c0000228140045)) else (if i < 334 then (if i < 333 then 0x40000000000000008200c430010c020025000920001800005d00000001810000864a else 0x2600000000000000000400000008800218000600018342a02030008a00003348600) else (if i < 335 then 0x190c00002180000000010c0000001100043000080000000000000000140000000002c00 else 0x1243800218148608220002243098009400228180000218008a00000000000000000043))))
def slotAtChunkBlock21 (i : Nat) : Nat :=
  (if i < 344 then (if i < 340 then (if i < 338 then (if i < 337 then 0x992c0800220040c01001f80045001c40062001142c4300000000a018000000040000400 else 0x103c0000020002402000000008228240600001109400050000000040000006000540000) else (if i < 339 then 0x2704cc200000140403018200000000000408858001000018008a130000144000080c0013 else 0x220008a4304020a000000001a1500110860002a6c00003100086b9003b09200001102c00)) else (if i < 342 then (if i < 341 then 0xb00978002190d8a045c9382c12010080003030dc2620008149c02000a1d80a001140043 else 0x1f804000827008000209938e40d1e8002443218080813000008600000002600000200002) else (if i < 343 then 0x10c26000b0000016000008a00000049200000000000000021800002088800001140000 else 0x88000000000082800000000010c0602000980000000000000001140000218000000))) else (if i < 348 then (if i < 346 then (if i < 345 then 0x100000030080000450010c780000114000000004040001a380000000000000000000000 else 0x12400000913800000000004520180086440000000e22190c0045000000013028000c02) else (if i < 347 then 0x91006010000c000821914000021bb08a000000000ec4400800437610c0000000000000 else 0xb0001a0000048020a000180002000002c0000000e802010001a44001e08602000000062)) else (if i < 350 then (if i < 349 then 0xc0000228000000000008a450110ce200001a000443a11402130000000b900800009b else 0x1c8002a000004c88000000006000011010030500000000010c00000000c8644000082600) else (if i < 351 then 0x2030100000012282004020a9100000310088a000004c04000010c860001001d800 else 0x10080015000589208001cc0000228080000010000600000000400100000002010000000))))
def slotAtChunkBlock22 (i : Nat) : Nat :=
  (if i < 360 then (if i < 356 then (if i < 354 then (if i < 353 then 0x198804002f91486000200c000021800000104114023c010180043000088a43001288a00 else 0x111c402068340a00238008a0d00000004500000004300000000022808060039138e41b) else (if i < 355 then 0x86002500004030110d544e0000000002200000000980800000910c0472028000000 else 0x90002c4400114080031110861601004000231004864e0000400000005c0002218000002)) else (if i < 358 then (if i < 357 then 0x68000402008082a02009117200000080000008042800249100000000000411218088800 else 0x978000002000000004c100038988000000000009b000000005000008665660008612) else (if i < 359 then 0x1cc00de011140a00000000000000480000001c4860200000c4000000086001a9cc8a00 else 0x110c40021b80008d00000000025001d80d0000800430000c00000043c8e02000001013))) else (if i < 364 then (if i < 362 then (if i < 361 then 0x2801d8000192806432210c00000000c2e12229100000001108a0300001d80300000000c else 0x4d80c000233800940051814000000000040000001d8000000000080025c000300054e200) else (if i < 363 then 0x521100000388140003000097200112e4c403000808a00050000000000000000001140000 else 0x1c4050010c00000000026000000000020000086000000006454d8008a170010c0000)) else (if i < 366 then (if i < 365 then 0x111000b90900086000000814001f0008600010000000000000002220000a43 else 0x8861300048000d0080026000011000032510c2c000000000040105c7245000099800) else (if i < 367 then 0x63001a8880000000241500000000006b0000ec028040000000000002000088662 else 0x1240045000080600018000003001142643000800000000001000010000000000000013))))
def slotAtChunkBlock23 (i : Nat) : Nat :=
  (if i < 376 then (if i < 372 then (if i < 370 then (if i < 369 then 0x80016220001a000002086003410c0004011100217040001000000002600008048804 else 0x3100000040200c000000000000a0004c12f47625c86000b0000a000010c0044000002c00) else (if i < 371 then 0x4b8000005000208600013919e08000000400228000008220080000229280043012600008 else 0x20018e000004c004e010080012019280045000000000030000c1600018004300210009b)) else (if i < 374 then (if i < 373 then 0x28002a0000004000000110860d0000000430000000020280000432290c0002000008a00 else 0x104c0045010000400000008600000000510001390c000980086014680800430b0588800) else (if i < 375 then 0x220000000000000000018000000000008600000008608000000000218000044000009212 else 0x229148808099142c16310541045001381a082190d1a44028008800001140002000040000))) else (if i < 380 then (if i < 378 then (if i < 377 then 0x5280086452205000000000c0243009c8260a000000401000140043000148a003100c0049 else 0x13c800680300800690100c0003218fc0000001008816218080008000000000000008600) else (if i < 379 then 0x10c26000a92806000010c2600011100000018208a00000008e43001140000298001044 else 0x430000000002200004088610d160000000000001000000001000c400010080401)) else (if i < 382 then (if i < 381 then 0x3680172440604c00130000800de0010c2c8e000000400000000002000008a00 else 0x12200026430a8000612858000000218006c010b00c8600070000443040080000) else (if i < 383 then 0xb10c00000010ce600098142c020280400a7050009c161c90c000021828880d219108843 else 0x2700000080500002000000c1e002185426452610c00000011402450a8301a01218348a20))))
def slotAtChunkBlock24 (i : Nat) : Nat :=
  (if i < 392 then (if i < 388 then (if i < 386 then (if i < 385 then 0x90080043220288a00228588a022191086440000000000000000000d80002000000c2a00 else 0x1291618000002004b60002402000004c003e0010c86432181400650090c00000280c0005) else (if i < 387 then 0x62000011a430004c00000002092430000000000000086080100004000010c0000 else 0x2480c00150110c00000000000000080000020000000000042c0400000500000000000803)) else (if i < 390 then (if i < 389 then 0xaafc0000011148a000000000005c80000001288004452500c0001041888800 else 0xb00150000501800000002002020180000000026c0253000280000218548800010080045) else (if i < 391 then 0x402004030b114000d048002601000000000710000000000480002218540003228008a37 else 0x980000000923404134a82002000680004000680136000000c00002210c0000000340043))) else (if i < 396 then (if i < 394 then (if i < 393 then 0x412228000000220002c00000002c1300000004d008000000018000000758000045 else 0x100d5000000009245018000000010002a002480008a8040003216001100a003f1c40000) else (if i < 395 then 0x1c400000b000000000000064300000000000000000000000020000000020000000860a else 0x2280010000b0008600000001a020000800003080c8643003b0c202000002a00001948843)) else (if i < 398 then (if i < 397 then 0x90040000001100400218000800000000001738000000000300600000000000000000000 else 0x89245001895004001241a43000000000000000000000240600010000000) else (if i < 399 then 0x8e80c040056928000022000860000000e2620000000000100092432191c0000013b02a49 else 0x28000081800060000000000021800d0000001410050000006120000004000010dae16))))
def slotAtChunkBlock25 (i : Nat) : Nat :=
  (if i < 408 then (if i < 404 then (if i < 402 then (if i < 401 then 0x228000000000002416000002a00000042600220013600000000013250000000000000400 else 0x49000008a00002e400020010c0403000000400008008a00000017200228008605) else (if i < 403 then 0xb430020009028000200189d844220cc0a0021808000800000000000800004a0017c0645 else 0x228000000000000444000008600000008600010000000000000000760940000)) else (if i < 406 then (if i < 405 then 0x1000020000800d64f1100001000082a03000289402270001000000009c00220008800 else 0x51141000068000002000001043000000c08218012e00001288600000009400008000073) else (if i < 407 then 0x206c0400000000000001cc860022800880200000001600000880b310000600000002600 else 0x80c2a06728142a03220000044228041012000000400000001a4e000000000128082400))) else (if i < 412 then (if i < 410 then (if i < 409 then 0x178000011026020010c88a22180006720a8040044229140000001148844229240408 else 0x11000000003400000918810000000000000b80002ec000000000000080000001140200) else (if i < 411 then 0xa8000000000000010c004300000000100048000000000004a0000800000000000a0 else 0x11404030110c00000002002020000000440000400000000086000000c0200000080000)) else (if i < 414 then (if i < 413 then 0x11000020000d14000a3b002490b910000d0180000002280000020000c0003310002a43 else 0x8861642000021a02854000021914140c0011000000011400000010cc29b0100c8845) else (if i < 415 then 0xc00430001400430780012002202800000000120430000002430129c0201 else 0x3890c044322000880600000000022070000000000000000028109f000000044028009200))))
def slotAtChunkBlock26 (i : Nat) : Nat :=
  (if i < 424 then (if i < 420 then (if i < 418 then (if i < 417 then 0xa800000821800000800020d0440000c8a0000800fc000003c000021800000a098000044 else 0x8a0000000920000008000000110884300000e400000080202000180027001140043) else (if i < 419 then 0xd804c40000000860021800001206000004500000046200000d200040180a05001108800 else 0x2a2c0780094000100000000180000490008006020000000000004c00001f0000000)) else (if i < 422 then (if i < 421 then 0x40bc86000010c100d0400c8800000000644009140000000001000678480000000009c00 else 0x22855e0002210d4a067d0140002001140c0021800fa0200058000021911d84301000d000) else (if i < 423 then 0x11426ec2185806025400004430030572442180086034d80000e3222d80002272888800 else 0x2280010430a8008600000002a09010000004000000000000008800021148a9b228540020))) else (if i < 428 then (if i < 426 then (if i < 425 then 0x4c0815000080002008080000000008843861140000028008a060000406167610c8600 else 0x21800ca00000002c12000180000218481002000003000028008a00000040c37000002400) else (if i < 427 then 0x10c88000003c8a150a91000004283000000980000450011400162190c0000000008a41 else 0xa048000000000e2002180000440001400000000002440880004000200cba023281c0000)) else (if i < 430 then (if i < 429 then 0x18000d0900008160000000440011406030000c0002000080045228000400000180400 else 0x2480000010000000000026c00004d8100000000040054000100043001e80000000000045) else (if i < 431 then 0x510c02440280088000010c00010010c0002000088a00310000000010fc0400001100043 else 0x680010002d00c0000000000000000009c00000200a16069140000000000043))))
def slotAtChunkBlock27 (i : Nat) : Nat :=
  (if i < 440 then (if i < 436 then (if i < 434 then (if i < 433 then 0x100000000000000000300000000008a00000080000218000000000000000011140000 else 0xb0000013008001a040092488000002026031e00088000000808130010c8600001880000) else (if i < 435 then 0x9800c4450000000fd010008a002180092002180800000d800010c0002802b9018080000 else 0x1100644010081008020081a040100400000b0000244000040043000000805000540415)) else (if i < 438 then (if i < 437 then 0x400010081a1500000100000114040009910e2020900800056580092000000c9402 else 0x990df6000105886000090c880421a3400000000018000000000005c800000000000002a) else (if i < 439 then 0x1100400000008604001100000000000616219141a45030002e04018080044218009200 else 0x4000000644220d806030000c00004d8040000010000000010000208000080000))) else (if i < 444 then (if i < 442 then (if i < 441 then 0x5000000a430000000e222000d0000182010ec000008600000000049000582600 else 0x1a000000026642200000000018808000b0000049000588a08099100071) else (if i < 443 then 0x5c8000443000080c08000000000000008600000080415010108a6a0190c00000b0140000 else 0x547c13050000600000000000000088a00000000000000499600010540008218000000)) else (if i < 446 then (if i < 445 then 0x40080006000040000220000016018000044068000400010000043010000800218000003 else 0x22000c408010000000000000000000002c0002ae40000000000000000000044919240000) else (if i < 447 then 0x1d80021800020200000920045000040d218002c00010002600000009445 else 0x9800000000000321a0080000432280000000100c000000000000000000004302a540000))))
def slotAtChunkBlock28 (i : Nat) : Nat :=
  (if i < 456 then (if i < 452 then (if i < 450 then (if i < 449 then 0x980000ec000000000000004000000009400000000000218002a000d8000243028000000 else 0x40000000c400000000000000000000000000071000200000000000000) else (if i < 451 then 0x40002400010482a00000588a001f0009c020180000002526c0000009cc0628018080e00 else 0x310c0003219280000000000003000000000000000000000008872218000004000000049)) else (if i < 454 then (if i < 453 then 0x2000002200000433900000000b00c0000000080000040202600000000000000000000 else 0x183cb2000100800000000004003100000450280092bc000000003000000013000008602) else (if i < 455 then 0xdc028200000008000a000081040000a9240013000008a02220446e000310c0400 else 0x10c02020b138020000800004300000c444000008600000080000003b0040a))) else (if i < 460 then (if i < 458 then (if i < 457 then 0x182800002180804020012486000010c00000400000000000000000b0000644010000400 else 0xc4002280000450004c0000043b090000a80006ec0000000000004e0000000000000) else (if i < 459 then 0x10a0008a0000914001500000000001010004a311340000002f00005390000000 else 0x218002c02028008a020002c0113000080000270008a00000022e13000000000218180000)) else (if i < 462 then (if i < 461 then 0x30000000000198004300000000022800e200001102400000000006010000043001080008 else 0xc869b0006402032600092a8000040014000080008220000400128000000000000000) else (if i < 463 then 0x8a032280ce43e2180000000000000000b0210445000000000010000600001280400 else 0x2b0000415000001000000000000000000043000308a00010000003008082a012510c0045))))
def slotAtChunkBlock29 (i : Nat) : Nat :=
  (if i < 472 then (if i < 468 then (if i < 466 then (if i < 465 then 0x3110c86620900000135104c1e02000008a000000d0044000108600218000000218008a00 else 0xb188060000000004502000264e2700004450004c0000000100001019140002000580001) else (if i < 467 then 0x8008a1000114000022820000000011aa03218000043000000213388288800219442600 else 0x2200000020011000dd000002e00000208600048000000000200000229380401218008802)) else (if i < 470 then (if i < 469 then 0x78114080021800004300000000d0000c2675901380000000100000040000043 else 0x11002000111000000a8000000000008800000000000000000000000000008000000000) else (if i < 471 then 0x2280004002280000000a90d1a0600000860022800040022112241b000000200310009400 else 0x402008000400091100111010000008001100005220588a622180c6e43000042645))) else (if i < 476 then (if i < 474 then (if i < 473 then 0x240008090000800010000012098008a00228040013000200000218001a002e0940043 else 0x2180000002280000430000000020000088003902004000010c0002218002617010000000) else (if i < 475 then 0xa90c06452210c007d010082a00000004200000f09a4a011116e0004000000202800c402 else 0x2e90ccc000400000150010c00032501800710005c2c00000000000010008a00228340000)) else (if i < 478 then (if i < 477 then 0x1d000000018800ef0000000130018400370aa5c000000000001200008000261818000e else 0x11404082242824002181086440000000007600000000b0000044000000000041100000) else (if i < 479 then 0x4c9200010080000000000c0022000000a000208600228002600001892243000008643 else 0x68000000001c82400000000408000002c02010000400540000002000000000003b00a00))))
def slotAtChunkBlock30 (i : Nat) : Nat :=
  (if i < 484 then (if i < 482 then (if i < 481 then 0x10c00000100000002100000120023000450010c0005000000400000000000219141001 else 0x38800080d0000000022180006490011000d20011000010000886160010c0000002102600) else (if i < 483 then 0xa2200192000010c06020000088030000000020000004000304c8600000000004 else 0x21af000001e0000000000000001000000000000000000000580002000000000000002600)) else (if i < 486 then (if i < 485 then 0x2191404440a0082ab92c00c921200124060209000040000928c40008924000200034000d else 0x213804060400006000204c00002280c8662090140045000000000000000c000180c0000) else (if i < 487 then 0x10c0000000000043001100000000040014218080000009140000010000000000281401 else (if i < 488 then 0x1140200001149c00228f800000000000000980000450000086440110c00122200c0c00 else 0x8600000000000002348a1100000000300058044300000001b0004800020011000bf))))
def slotAtChunk (i : Nat) : Nat :=
  match i / 16 with
  | 0 => slotAtChunkBlock0 i
  | 1 => slotAtChunkBlock1 i
  | 2 => slotAtChunkBlock2 i
  | 3 => slotAtChunkBlock3 i
  | 4 => slotAtChunkBlock4 i
  | 5 => slotAtChunkBlock5 i
  | 6 => slotAtChunkBlock6 i
  | 7 => slotAtChunkBlock7 i
  | 8 => slotAtChunkBlock8 i
  | 9 => slotAtChunkBlock9 i
  | 10 => slotAtChunkBlock10 i
  | 11 => slotAtChunkBlock11 i
  | 12 => slotAtChunkBlock12 i
  | 13 => slotAtChunkBlock13 i
  | 14 => slotAtChunkBlock14 i
  | 15 => slotAtChunkBlock15 i
  | 16 => slotAtChunkBlock16 i
  | 17 => slotAtChunkBlock17 i
  | 18 => slotAtChunkBlock18 i
  | 19 => slotAtChunkBlock19 i
  | 20 => slotAtChunkBlock20 i
  | 21 => slotAtChunkBlock21 i
  | 22 => slotAtChunkBlock22 i
  | 23 => slotAtChunkBlock23 i
  | 24 => slotAtChunkBlock24 i
  | 25 => slotAtChunkBlock25 i
  | 26 => slotAtChunkBlock26 i
  | 27 => slotAtChunkBlock27 i
  | 28 => slotAtChunkBlock28 i
  | 29 => slotAtChunkBlock29 i
  | 30 => slotAtChunkBlock30 i
  | _ => 0

def slotAt (i : Nat) : Nat :=
  ((slotAtChunk (i / 32)) >>> ((i % 32) * 9)) % 512

def hintAtBlock0 (i : Nat) : Option Hint :=
  (if i < 8 then (if i < 4 then (if i < 2 then (if i < 1 then none else hint0) else (if i < 3 then hint1 else hint2)) else (if i < 6 then (if i < 5 then hint3 else hint4) else (if i < 7 then hint5 else hint6))) else (if i < 12 then (if i < 10 then (if i < 9 then hint7 else hint8) else (if i < 11 then hint9 else hint10)) else (if i < 14 then (if i < 13 then hint11 else hint12) else (if i < 15 then hint13 else hint14))))
def hintAtBlock1 (i : Nat) : Option Hint :=
  (if i < 24 then (if i < 20 then (if i < 18 then (if i < 17 then hint15 else hint16) else (if i < 19 then hint17 else hint18)) else (if i < 22 then (if i < 21 then hint19 else hint20) else (if i < 23 then hint21 else hint22))) else (if i < 28 then (if i < 26 then (if i < 25 then hint23 else hint24) else (if i < 27 then hint25 else hint26)) else (if i < 30 then (if i < 29 then hint27 else hint28) else (if i < 31 then hint29 else hint30))))
def hintAtBlock2 (i : Nat) : Option Hint :=
  (if i < 40 then (if i < 36 then (if i < 34 then (if i < 33 then hint31 else hint32) else (if i < 35 then hint33 else hint34)) else (if i < 38 then (if i < 37 then hint35 else hint36) else (if i < 39 then hint37 else hint38))) else (if i < 44 then (if i < 42 then (if i < 41 then hint39 else hint40) else (if i < 43 then hint41 else hint42)) else (if i < 46 then (if i < 45 then hint43 else hint44) else (if i < 47 then hint45 else hint46))))
def hintAtBlock3 (i : Nat) : Option Hint :=
  (if i < 56 then (if i < 52 then (if i < 50 then (if i < 49 then hint47 else hint48) else (if i < 51 then hint49 else hint50)) else (if i < 54 then (if i < 53 then hint51 else hint52) else (if i < 55 then hint53 else hint54))) else (if i < 60 then (if i < 58 then (if i < 57 then hint55 else hint56) else (if i < 59 then hint57 else hint58)) else (if i < 62 then (if i < 61 then hint59 else hint60) else (if i < 63 then hint61 else hint62))))
def hintAtBlock4 (i : Nat) : Option Hint :=
  (if i < 72 then (if i < 68 then (if i < 66 then (if i < 65 then hint63 else hint64) else (if i < 67 then hint65 else hint66)) else (if i < 70 then (if i < 69 then hint67 else hint68) else (if i < 71 then hint69 else hint70))) else (if i < 76 then (if i < 74 then (if i < 73 then hint71 else hint72) else (if i < 75 then hint73 else hint74)) else (if i < 78 then (if i < 77 then hint75 else hint76) else (if i < 79 then hint77 else hint78))))
def hintAtBlock5 (i : Nat) : Option Hint :=
  (if i < 88 then (if i < 84 then (if i < 82 then (if i < 81 then hint79 else hint80) else (if i < 83 then hint81 else hint82)) else (if i < 86 then (if i < 85 then hint83 else hint84) else (if i < 87 then hint85 else hint86))) else (if i < 92 then (if i < 90 then (if i < 89 then hint87 else hint88) else (if i < 91 then hint89 else hint90)) else (if i < 94 then (if i < 93 then hint91 else hint92) else (if i < 95 then hint93 else hint94))))
def hintAtBlock6 (i : Nat) : Option Hint :=
  (if i < 104 then (if i < 100 then (if i < 98 then (if i < 97 then hint95 else hint96) else (if i < 99 then hint97 else hint98)) else (if i < 102 then (if i < 101 then hint99 else hint100) else (if i < 103 then hint101 else hint102))) else (if i < 108 then (if i < 106 then (if i < 105 then hint103 else hint104) else (if i < 107 then hint105 else hint106)) else (if i < 110 then (if i < 109 then hint107 else hint108) else (if i < 111 then hint109 else hint110))))
def hintAtBlock7 (i : Nat) : Option Hint :=
  (if i < 120 then (if i < 116 then (if i < 114 then (if i < 113 then hint111 else hint112) else (if i < 115 then hint113 else hint114)) else (if i < 118 then (if i < 117 then hint115 else hint116) else (if i < 119 then hint117 else hint118))) else (if i < 124 then (if i < 122 then (if i < 121 then hint119 else hint120) else (if i < 123 then hint121 else hint122)) else (if i < 126 then (if i < 125 then hint123 else hint124) else (if i < 127 then hint125 else hint126))))
def hintAtBlock8 (i : Nat) : Option Hint :=
  (if i < 136 then (if i < 132 then (if i < 130 then (if i < 129 then hint127 else hint128) else (if i < 131 then hint129 else hint130)) else (if i < 134 then (if i < 133 then hint131 else hint132) else (if i < 135 then hint133 else hint134))) else (if i < 140 then (if i < 138 then (if i < 137 then hint135 else hint136) else (if i < 139 then hint137 else hint138)) else (if i < 142 then (if i < 141 then hint139 else hint140) else (if i < 143 then hint141 else hint142))))
def hintAtBlock9 (i : Nat) : Option Hint :=
  (if i < 152 then (if i < 148 then (if i < 146 then (if i < 145 then hint143 else hint144) else (if i < 147 then hint145 else hint146)) else (if i < 150 then (if i < 149 then hint147 else hint148) else (if i < 151 then hint149 else hint150))) else (if i < 156 then (if i < 154 then (if i < 153 then hint151 else hint152) else (if i < 155 then hint153 else hint154)) else (if i < 158 then (if i < 157 then hint155 else hint156) else (if i < 159 then hint157 else hint158))))
def hintAtBlock10 (i : Nat) : Option Hint :=
  (if i < 168 then (if i < 164 then (if i < 162 then (if i < 161 then hint159 else hint160) else (if i < 163 then hint161 else hint162)) else (if i < 166 then (if i < 165 then hint163 else hint164) else (if i < 167 then hint165 else hint166))) else (if i < 172 then (if i < 170 then (if i < 169 then hint167 else hint168) else (if i < 171 then hint169 else hint170)) else (if i < 174 then (if i < 173 then hint171 else hint172) else (if i < 175 then hint173 else hint174))))
def hintAtBlock11 (i : Nat) : Option Hint :=
  (if i < 184 then (if i < 180 then (if i < 178 then (if i < 177 then hint175 else hint176) else (if i < 179 then hint177 else hint178)) else (if i < 182 then (if i < 181 then hint179 else hint180) else (if i < 183 then hint181 else hint182))) else (if i < 188 then (if i < 186 then (if i < 185 then hint183 else hint184) else (if i < 187 then hint185 else hint186)) else (if i < 190 then (if i < 189 then hint187 else hint188) else (if i < 191 then hint189 else hint190))))
def hintAtBlock12 (i : Nat) : Option Hint :=
  (if i < 200 then (if i < 196 then (if i < 194 then (if i < 193 then hint191 else hint192) else (if i < 195 then hint193 else hint194)) else (if i < 198 then (if i < 197 then hint195 else hint196) else (if i < 199 then hint197 else hint198))) else (if i < 204 then (if i < 202 then (if i < 201 then hint199 else hint200) else (if i < 203 then hint201 else hint202)) else (if i < 206 then (if i < 205 then hint203 else hint204) else (if i < 207 then hint205 else hint206))))
def hintAtBlock13 (i : Nat) : Option Hint :=
  (if i < 216 then (if i < 212 then (if i < 210 then (if i < 209 then hint207 else hint208) else (if i < 211 then hint209 else hint210)) else (if i < 214 then (if i < 213 then hint211 else hint212) else (if i < 215 then hint213 else hint214))) else (if i < 220 then (if i < 218 then (if i < 217 then hint215 else hint216) else (if i < 219 then hint217 else hint218)) else (if i < 222 then (if i < 221 then hint219 else hint220) else (if i < 223 then hint221 else hint222))))
def hintAtBlock14 (i : Nat) : Option Hint :=
  (if i < 232 then (if i < 228 then (if i < 226 then (if i < 225 then hint223 else hint224) else (if i < 227 then hint225 else hint226)) else (if i < 230 then (if i < 229 then hint227 else hint228) else (if i < 231 then hint229 else hint230))) else (if i < 236 then (if i < 234 then (if i < 233 then hint231 else hint232) else (if i < 235 then hint233 else hint234)) else (if i < 238 then (if i < 237 then hint235 else hint236) else (if i < 239 then hint237 else hint238))))
def hintAtBlock15 (i : Nat) : Option Hint :=
  (if i < 248 then (if i < 244 then (if i < 242 then (if i < 241 then hint239 else hint240) else (if i < 243 then hint241 else hint242)) else (if i < 246 then (if i < 245 then hint243 else hint244) else (if i < 247 then hint245 else hint246))) else (if i < 252 then (if i < 250 then (if i < 249 then hint247 else hint248) else (if i < 251 then hint249 else hint250)) else (if i < 254 then (if i < 253 then hint251 else hint252) else (if i < 255 then hint253 else hint254))))
def hintAtBlock16 (i : Nat) : Option Hint :=
  (if i < 264 then (if i < 260 then (if i < 258 then (if i < 257 then hint255 else hint256) else (if i < 259 then hint257 else hint258)) else (if i < 262 then (if i < 261 then hint259 else hint260) else (if i < 263 then hint261 else hint262))) else (if i < 268 then (if i < 266 then (if i < 265 then hint263 else hint264) else (if i < 267 then hint265 else hint266)) else (if i < 270 then (if i < 269 then hint267 else hint268) else (if i < 271 then hint269 else hint270))))
def hintAtBlock17 (i : Nat) : Option Hint :=
  (if i < 280 then (if i < 276 then (if i < 274 then (if i < 273 then hint271 else hint272) else (if i < 275 then hint273 else hint274)) else (if i < 278 then (if i < 277 then hint275 else hint276) else (if i < 279 then hint277 else hint278))) else (if i < 284 then (if i < 282 then (if i < 281 then hint279 else hint280) else (if i < 283 then hint281 else hint282)) else (if i < 286 then (if i < 285 then hint283 else hint284) else (if i < 287 then hint285 else hint286))))
def hintAtBlock18 (i : Nat) : Option Hint :=
  (if i < 290 then (if i < 289 then hint287 else hint288) else (if i < 291 then hint289 else (if i < 292 then hint290 else hint291)))
def hintAt (i : Nat) : Option Hint :=
  match i / 16 with
  | 0 => hintAtBlock0 i
  | 1 => hintAtBlock1 i
  | 2 => hintAtBlock2 i
  | 3 => hintAtBlock3 i
  | 4 => hintAtBlock4 i
  | 5 => hintAtBlock5 i
  | 6 => hintAtBlock6 i
  | 7 => hintAtBlock7 i
  | 8 => hintAtBlock8 i
  | 9 => hintAtBlock9 i
  | 10 => hintAtBlock10 i
  | 11 => hintAtBlock11 i
  | 12 => hintAtBlock12 i
  | 13 => hintAtBlock13 i
  | 14 => hintAtBlock14 i
  | 15 => hintAtBlock15 i
  | 16 => hintAtBlock16 i
  | 17 => hintAtBlock17 i
  | 18 => hintAtBlock18 i
  | _ => none

def advice (k : Nat) : Option Hint :=
  hintAt (slotAt ((k / 1024 + saltAt (k % 1024)) % 15647))

def firstPair (i : Nat) : Bool :=
  ((pairs inputs)[i]?).any (fun (a,b,r) => dispatch 4 (front claims advice 1 10) a b r)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair0 : firstPair 0 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair1 : firstPair 1 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair2 : firstPair 2 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair3 : firstPair 3 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair4 : firstPair 4 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair5 : firstPair 5 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair6 : firstPair 6 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair7 : firstPair 7 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair8 : firstPair 8 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair9 : firstPair 9 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair10 : firstPair 10 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair11 : firstPair 11 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair12 : firstPair 12 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair13 : firstPair 13 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair14 : firstPair 14 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair15 : firstPair 15 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair16 : firstPair 16 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair17 : firstPair 17 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair18 : firstPair 18 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair19 : firstPair 19 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair20 : firstPair 20 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair21 : firstPair 21 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair22 : firstPair 22 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair23 : firstPair 23 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair24 : firstPair 24 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair25 : firstPair 25 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair26 : firstPair 26 = false := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
theorem pair27 : firstPair 27 = false := by decide +kernel

set_option maxHeartbeats 3000000 in
theorem checked : front claims advice 2 11 4 inputs = false := by
  have hlen : (pairs inputs).length = 28 := by decide
  have each : ∀ i : Fin 28, firstPair i.val = false := by
    intro i
    fin_cases i
    · exact pair0
    · exact pair1
    · exact pair2
    · exact pair3
    · exact pair4
    · exact pair5
    · exact pair6
    · exact pair7
    · exact pair8
    · exact pair9
    · exact pair10
    · exact pair11
    · exact pair12
    · exact pair13
    · exact pair14
    · exact pair15
    · exact pair16
    · exact pair17
    · exact pair18
    · exact pair19
    · exact pair20
    · exact pair21
    · exact pair22
    · exact pair23
    · exact pair24
    · exact pair25
    · exact pair26
    · exact pair27
  apply Bool.eq_false_iff.mpr
  intro yes
  change (!(matched claims advice 11 inputs) && ((inputs == [goal]) ||
    (pairs inputs).any (fun (a,b,r) => dispatch 4 (front claims advice 1 10) a b r))) = true at yes
  simp only [Bool.and_eq_true, Bool.or_eq_true] at yes
  rcases yes.2 with stop | step
  · exact (by decide : (inputs == [goal]) ≠ true) stop
  · obtain ⟨p,hp,ok⟩ := List.any_eq_true.mp step
    obtain ⟨i,hi⟩ := List.get_of_mem hp
    have no := each (Fin.cast hlen i)
    simp only [Fin.val_cast, firstPair, List.getElem?_eq_getElem i.isLt, Option.any_some] at no
    rw [← hi] at ok
    exact Bool.noConfusion (no.symm.trans ok)

end Check516

theorem PEqualNP.Outside.L_meta_516 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 8 (fun x : Fin 8 → Bool => (x 0 && x 2) || (x 2 && x 3) || (x 3 && x 1) || (x 0 && x 4) || (x 4 && x 5) || (x 5 && x 1) || (x 0 && x 6) || (x 6 && x 7) || (x 7 && x 1)) s → 12 ≤ s :=
  Check516.lower_of_front _ _ _ Check516.allClaims Check516.checked
