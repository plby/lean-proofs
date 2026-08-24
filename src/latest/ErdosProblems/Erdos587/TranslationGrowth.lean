import Mathlib

/-!
Translation growth in the Conlon--Fox--Pham structural argument.
The boundary of a finite set is subadditive in the translation parameter.
Double counting bounds its almost periods, yielding a growth witness from
a large iterated sumset. These arguments work in any additive commutative group.
-/

open scoped BigOperators Pointwise

namespace Erdos587.CFP

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def translate (S : Finset G) (a : G) : Finset G := S.image (fun x => x + a)

@[simp] theorem mem_translate {S : Finset G} {a x : G} :
    x ∈ translate S a ↔ x - a ∈ S := by
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x - a, hx, sub_add_cancel x a⟩

@[simp] theorem card_translate (S : Finset G) (a : G) :
    (translate S a).card = S.card :=
  Finset.card_image_of_injective S (add_left_injective a)

@[simp] theorem translate_zero (S : Finset G) : translate S 0 = S := by
  ext x
  simp

theorem translate_translate (S : Finset G) (a b : G) :
    translate (translate S a) b = translate S (a + b) := by
  simp only [translate, Finset.image_image, Function.comp_def, add_assoc]

theorem translate_sdiff (S T : Finset G) (a : G) :
    translate (S \ T) a = translate S a \ translate T a :=
  Finset.image_sdiff S T (add_left_injective a)

def translationBoundary (S : Finset G) (a : G) : ℕ := (translate S a \ S).card

def translationOverlap (S : Finset G) (a : G) : ℕ :=
  (S.filter fun x => x + a ∈ S).card

@[simp] theorem translationBoundary_zero (S : Finset G) : translationBoundary S 0 = 0 := by
  simp [translationBoundary]

omit [AddCommGroup G] in
theorem card_sdiff_triangle (S T U : Finset G) :
    (S \ U).card ≤ (S \ T).card + (T \ U).card := by
  have hsub : S \ U ⊆ (S \ T) ∪ (T \ U) := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_union] at *
    by_cases hxT : x ∈ T
    · exact Or.inr ⟨hxT, hx.2⟩
    · exact Or.inl ⟨hx.1, hxT⟩
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

theorem translationBoundary_add_le (S : Finset G) (a b : G) :
    translationBoundary S (a + b) ≤ translationBoundary S a + translationBoundary S b := by
  have hshift : (translate S (a + b) \ translate S a).card = translationBoundary S b := by
    rw [show a + b = b + a from add_comm a b, ← translate_translate,
      ← translate_sdiff, card_translate]
    rfl
  have hh := card_sdiff_triangle (translate S (a + b)) (translate S a) S
  rw [hshift] at hh
  simpa only [translationBoundary, Nat.add_comm] using hh

theorem translationBoundary_sum_le {ι : Type*} (S : Finset G) (I : Finset ι) (a : ι → G) :
    translationBoundary S (∑ i ∈ I, a i) ≤ ∑ i ∈ I, translationBoundary S (a i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (translationBoundary_add_le S _ _).trans (Nat.add_le_add (le_refl _) ih)

theorem translationBoundary_add_overlap (S : Finset G) (a : G) :
    translationBoundary S a + translationOverlap S a = S.card := by
  have hinter : translate S a ∩ S = translate (S.filter fun x => x + a ∈ S) a := by
    ext x
    simp only [Finset.mem_inter, mem_translate, Finset.mem_filter, sub_add_cancel]
  have hh := Finset.card_sdiff_add_card_inter (translate S a) S
  rw [hinter, card_translate, card_translate] at hh
  exact hh

theorem sum_translationOverlap_le (S U : Finset G) :
    ∑ a ∈ U, translationOverlap S a ≤ S.card ^ 2 := by
  have hrow (x : G) : (U.filter fun a => x + a ∈ S).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun a => x + a)
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
    · exact (add_right_injective x).injOn
  calc
    ∑ a ∈ U, translationOverlap S a = ∑ a ∈ U, ∑ x ∈ S, if x + a ∈ S then 1 else 0 := by
      simp only [translationOverlap, Finset.card_filter]
    _ = ∑ x ∈ S, ∑ a ∈ U, if x + a ∈ S then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _x ∈ S, S.card := by
      apply Finset.sum_le_sum
      intro x _hx
      simpa only [Finset.card_filter] using hrow x
    _ = S.card ^ 2 := by simp [pow_two]

theorem card_lt_twice_of_small_translationBoundary {S U : Finset G} (hS : S.Nonempty)
    (hsmall : ∀ a ∈ U, 2 * translationBoundary S a < S.card) :
    U.card < 2 * S.card := by
  by_cases hU : U.Nonempty
  · have hpoint (a : G) (ha : a ∈ U) : S.card < 2 * translationOverlap S a := by
      have hh := translationBoundary_add_overlap S a
      have hs := hsmall a ha
      omega
    have hsum : U.card * S.card < 2 * ∑ a ∈ U, translationOverlap S a := by
      calc
        U.card * S.card = ∑ _a ∈ U, S.card := by simp
        _ < ∑ a ∈ U, 2 * translationOverlap S a :=
          Finset.sum_lt_sum_of_nonempty hU hpoint
        _ = 2 * ∑ a ∈ U, translationOverlap S a := (Finset.mul_sum _ _ _).symm
    have htotal := sum_translationOverlap_le S U
    have hpos := hS.card_pos
    nlinarith
  · have hzero : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
    rw [hzero, Finset.card_empty]
    exact Nat.mul_pos (by decide) hS.card_pos

theorem exists_large_translationBoundary {S U : Finset G} (hS : S.Nonempty)
    (hlarge : 2 * S.card ≤ U.card) :
    ∃ a ∈ U, S.card ≤ 2 * translationBoundary S a := by
  by_contra hn
  push Not at hn
  exact (card_lt_twice_of_small_translationBoundary hS hn).not_ge hlarge

theorem translationBoundary_le_mul_of_mem_nsmul {S A : Finset G} {M : ℕ}
    (hM : ∀ a ∈ A, translationBoundary S a ≤ M) :
    ∀ k : ℕ, ∀ z ∈ k • A, translationBoundary S z ≤ k * M := by
  intro k
  induction k with
  | zero =>
      intro z hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      simp
  | succ k ih =>
      intro z hz
      rw [succ_nsmul] at hz
      obtain ⟨x, hx, a, ha, rfl⟩ := Finset.mem_add.mp hz
      calc
        translationBoundary S (x + a) ≤ translationBoundary S x + translationBoundary S a :=
          translationBoundary_add_le S x a
        _ ≤ k * M + M := Nat.add_le_add (ih x hx) (hM a ha)
        _ = (k + 1) * M := by ring

/-- CFP's growing-sum lemma, with denominators cleared. -/
theorem exists_translation_growth_of_large_nsmul {S A : Finset G} {k : ℕ}
    (hS : S.Nonempty) (hA : A.Nonempty) (hlarge : 2 * S.card ≤ (k • A).card) :
    ∃ a ∈ A, S.card ≤ 2 * k * translationBoundary S a := by
  obtain ⟨a, ha, hmax⟩ := A.exists_max_image (translationBoundary S) hA
  obtain ⟨z, hz, hbig⟩ := exists_large_translationBoundary hS hlarge
  have hbound := translationBoundary_le_mul_of_mem_nsmul hmax k z hz
  refine ⟨a, ha, ?_⟩
  calc
    S.card ≤ 2 * translationBoundary S z := hbig
    _ ≤ 2 * (k * translationBoundary S a) := Nat.mul_le_mul_left 2 hbound
    _ = 2 * k * translationBoundary S a := by ring

end Erdos587.CFP
