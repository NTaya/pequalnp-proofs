import Mathlib.GroupTheory.Index
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_664_aux

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

def quad (b : F) (v : F × F) : F := v.1 ^ 2 + b * v.1 * v.2 + v.2 ^ 2

def mixed (b : F) (p d : F × F) : F := b * (p.1 * d.2 + p.2 * d.1)

def linearPart (a c : F) : F →+ F where
  toFun t := a * t ^ 2 + c * t
  map_zero' := by simp
  map_add' x y := by simp only [add_sq, CharTwo.two_eq_zero, zero_mul, add_zero]; ring

lemma expand (b : F) (p d : F × F) (t : F) :
    quad b (p + t • d) = quad b p + linearPart (quad b d) (mixed b p d) t := by
  change (p.1 + t*d.1)^2 + b*(p.1+t*d.1)*(p.2+t*d.2) + (p.2+t*d.2)^2 = _
  simp only [quad, mixed, linearPart, AddMonoidHom.coe_mk, ZeroHom.coe_mk, add_sq,
    CharTwo.two_eq_zero, zero_mul, add_zero]
  ring

lemma anisotropic (b : F) (hb : ∀ x : F, x^2 + b*x + 1 ≠ 0) (v : F × F)
    (hv : quad b v = 0) : v = 0 := by
  rcases v with ⟨x,y⟩
  change x^2 + b*x*y + y^2 = 0 at hv
  by_cases hy : y = 0
  · subst y
    simp at hv
    simp [hv]
  · exfalso
    apply hb (x/y)
    field_simp
    linear_combination hv

lemma ker_bound (a c : F) (ha : a ≠ 0) : Nat.card (linearPart a c).ker ≤ 2 := by
  classical
  have root (t : (linearPart a c).ker) : t.val = 0 ∨ t.val = -c/a := by
    have ht := t.property
    change a * (t.val)^2 + c*t.val = 0 at ht
    have h : t.val * (a * t.val + c) = 0 := by linear_combination ht
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · right
      apply (eq_div_iff ha).2
      linear_combination h
  let tag (t : (linearPart a c).ker) : Bool := decide (t.val = 0)
  have inj : Function.Injective tag := by
    intro t u eq
    apply Subtype.ext
    rcases root t with ht | ht <;> rcases root u with hu | hu
    · exact ht.trans hu.symm
    · by_contra hn
      have hnu : u.val ≠ 0 := fun h => hn (ht.trans h.symm)
      simp [tag, ht, hnu] at eq
      exact hnu (congrArg Subtype.val (eq.mp (Subtype.ext ht)))
    · by_contra hn
      have hnt : t.val ≠ 0 := fun h => hn (h.trans hu.symm)
      simp [tag, hu, hnt] at eq
      exact hnt (congrArg Subtype.val (eq.mpr (Subtype.ext hu)))
    · exact ht.trans hu.symm
  simpa using Nat.card_le_card_of_injective tag inj

lemma solutionCard (L : F →+ F) (k : F) (A : AddSubgroup F) [DecidablePred (· ∈ A)]
    (t₀ : F) (ht : k + L t₀ ∈ A) (hjoin : L.range ⊔ A = ⊤) :
    (Finset.univ.filter (fun t : F => k + L t ∈ A)).card = Nat.card A := by
  classical
  let e : {t : F // k + L t ∈ A} ≃ (A.comap L) :=
    { toFun := fun t => ⟨t.val - t₀, by
        change L (t.val - t₀) ∈ A
        simpa only [map_sub, add_sub_add_left_eq_sub] using A.sub_mem t.property ht⟩
      invFun := fun u => ⟨u.val + t₀, by
        have h : L u.val ∈ A := u.property
        simpa only [map_add, add_left_comm, add_comm, add_assoc] using A.add_mem h ht⟩
      left_inv := fun t => Subtype.ext (sub_add_cancel _ _)
      right_inv := fun u => Subtype.ext (add_sub_cancel_right _ _) }
  have idx : (A.comap L).index = A.index := by
    rw [AddSubgroup.index_comap, ← AddSubgroup.relIndex_sup_right L.range A, hjoin,
      AddSubgroup.relIndex_top_right]
  have hmul := (A.comap L).index_mul_card.trans A.index_mul_card.symm
  rw [idx] at hmul
  calc
    _ = Fintype.card {t : F // k + L t ∈ A} := (Fintype.card_subtype _).symm
    _ = Nat.card (A.comap L) := by rw [← Nat.card_eq_fintype_card]; exact Nat.card_congr e
    _ = Nat.card A := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero A.index_ne_zero) hmul

lemma hit (b : F) (hb : ∀ x : F, x^2 + b*x + 1 ≠ 0) (A : AddSubgroup F)
    [DecidablePred (· ∈ A)] (p d : F × F) (hd : d ≠ 0) (t₀ : F)
    (ht : quad b (p + t₀ • d) ∈ A) :
    (Finset.univ.filter (fun t : F => quad b (p + t • d) ∈ A)).card = Nat.card A := by
  classical
  let L := linearPart (quad b d) (mixed b p d)
  have ha : quad b d ≠ 0 := fun h => hd (anisotropic b hb d h)
  have he (t : F) : quad b (p + t • d) = quad b p + L t := expand b p d t
  simp only [he] at ht ⊢
  apply solutionCard L _ A t₀ ht
  by_cases hk : quad b p ∈ L.range
  · obtain ⟨t, h⟩ := hk
    have hv : quad b (p + t • d) = 0 := by rw [he, h, CharTwo.add_self_eq_zero]
    have hz := anisotropic b hb _ hv
    have hx := congrArg Prod.fst hz
    have hy := congrArg Prod.snd hz
    change p.1 + t * d.1 = 0 at hx
    change p.2 + t * d.2 = 0 at hy
    have hc : mixed b p d = 0 := by
      unfold mixed
      rw [show p.1 = -(t*d.1) from eq_neg_of_add_eq_zero_left hx,
          show p.2 = -(t*d.2) from eq_neg_of_add_eq_zero_left hy]
      have hh := CharTwo.add_self_eq_zero (t*d.1*d.2)
      linear_combination -b * hh
    have hinj : Function.Injective L := by
      intro x y eq
      change quad b d * x^2 + mixed b p d * x = quad b d * y^2 + mixed b p d * y at eq
      rw [hc, zero_mul, zero_mul, add_zero, add_zero] at eq
      have hh := mul_left_cancel₀ ha eq
      have hh' : (x-y)^2 = 0 := by
        rw [sub_sq, (show (2:F) = 0 from CharTwo.two_eq_zero), zero_mul, zero_mul, sub_zero, hh,
          CharTwo.add_self_eq_zero]
      exact sub_eq_zero.mp (by simpa using hh')
    rw [L.range_eq_top_of_surjective ((Finite.injective_iff_surjective).mp hinj), top_sup_eq]
  · by_contra htop
    have hn : ¬ A ≤ L.range := by
      intro h
      apply hk
      simpa using L.range.sub_mem (h ht) (show L t₀ ∈ L.range from ⟨_,rfl⟩)
    have hlt : L.range < L.range ⊔ A := lt_of_le_of_ne le_sup_left (fun h => hn (h ▸ le_sup_right))
    have hs := AddSubgroup.index_strictAnti hlt
    have htwo := (L.range ⊔ A).one_lt_index_of_ne_top htop
    have hind : L.range.index = Nat.card L.ker :=
      Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := L.range))
        (L.range.index_mul_card.trans (AddSubgroup.card_ker_mul_card_range L).symm)
    have hbnd := ker_bound (quad b d) (mixed b p d) ha
    change Nat.card L.ker ≤ 2 at hbnd
    omega

end PEqualNP.Outside.L_meta_664_aux

theorem PEqualNP.Outside.L_meta_664 : ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F 2] (b : F), (∀ X : F, X ^ 2 + b * X + 1 ≠ 0) → ∀ (A : AddSubgroup F) [DecidablePred (· ∈ A)] (p d : F × F), d ≠ 0 → ((Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = 0 ∨ (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) ∧ (p = 0 → (Finset.univ.filter (fun t : F => (p + t • d).1 ^ 2 + b * (p + t • d).1 * (p + t • d).2 + (p + t • d).2 ^ 2 ∈ A)).card = Nat.card A) := by
  intro F _ _ _ _ b hb A _ p d hd
  change ((Finset.univ.filter (fun t : F => PEqualNP.Outside.L_meta_664_aux.quad b (p + t • d) ∈ A)).card = 0 ∨ _) ∧ _
  constructor
  · by_cases h : ∃ t : F, PEqualNP.Outside.L_meta_664_aux.quad b (p + t • d) ∈ A
    · obtain ⟨t,ht⟩ := h
      exact Or.inr (PEqualNP.Outside.L_meta_664_aux.hit b hb A p d hd t ht)
    · left
      apply Finset.card_eq_zero.mpr
      exact Finset.eq_empty_iff_forall_notMem.mpr (fun t ht => h ⟨t, (Finset.mem_filter.mp ht).2⟩)
  · intro hp
    subst p
    apply PEqualNP.Outside.L_meta_664_aux.hit b hb A 0 d hd 0
    simp [PEqualNP.Outside.L_meta_664_aux.quad]
