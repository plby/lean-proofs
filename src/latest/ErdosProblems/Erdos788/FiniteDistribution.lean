import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Elementary probability distributions on finite types

The extractor reconstruction is entirely finite.  Keeping distributions as
nonnegative real mass functions avoids measure-theoretic conditional
probability and, in particular, all zero-denominator cases.
-/

namespace Erdos788

open scoped BigOperators

/-- A probability distribution on a finite type, represented by its mass
function. -/
@[ext]
structure FinDist (α : Type*) [Fintype α] where
  mass : α → ℝ
  nonneg : ∀ a, 0 ≤ mass a
  sum_mass : ∑ a, mass a = 1

namespace FinDist

variable {α β γ : Type*}

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] :
    FinDist α where
  mass := fun _ ↦ (Fintype.card α : ℝ)⁻¹
  nonneg := fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg _)
  sum_mass := by simp

@[simp]
theorem uniform_mass [Fintype α] [Nonempty α] (a : α) :
    (uniform α).mass a = (Fintype.card α : ℝ)⁻¹ :=
  rfl

/-- The uniform distribution on a specified nonempty finset, extended by
zero outside that finset. -/
noncomputable def uniformOn [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) : FinDist α where
  mass := fun a ↦ if a ∈ A then (A.card : ℝ)⁻¹ else 0
  nonneg := by
    intro a
    split_ifs
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact le_rfl
  sum_mass := by
    classical
    simp [hA.card_ne_zero]

@[simp]
theorem uniformOn_mass [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) (a : α) :
    (uniformOn A hA).mass a =
      if a ∈ A then (A.card : ℝ)⁻¹ else 0 :=
  rfl

/-- Push a finite distribution forward along a function. -/
noncomputable def map [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P : FinDist α) : FinDist β where
  mass := fun b ↦ ∑ a with f a = b, P.mass a
  nonneg := by
    intro b
    exact Finset.sum_nonneg fun _ _ ↦ P.nonneg _
  sum_mass := by
    simpa [Finset.sum_fiberwise_eq_sum_filter Finset.univ Finset.univ f P.mass]
      using! P.sum_mass

@[simp]
theorem map_mass [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (P : FinDist α) (b : β) :
    (P.map f).mass b = ∑ a with f a = b, P.mass a :=
  rfl

/-- Total variation distance, written as half the finite `L¹` distance. -/
noncomputable def tv [Fintype α] (P Q : FinDist α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |P.mass a - Q.mass a|

theorem tv_nonneg [Fintype α] (P Q : FinDist α) :
    0 ≤ P.tv Q := by
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)

@[simp]
theorem tv_self [Fintype α] (P : FinDist α) : P.tv P = 0 := by
  simp [tv]

theorem tv_symm [Fintype α] (P Q : FinDist α) : P.tv Q = Q.tv P := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  exact abs_sub_comm _ _

theorem tv_triangle [Fintype α] (P Q R : FinDist α) :
    P.tv R ≤ P.tv Q + Q.tv R := by
  have hpoint : ∀ a : α,
      |P.mass a - R.mass a| ≤
        |P.mass a - Q.mass a| + |Q.mass a - R.mass a| := by
    intro a
    exact abs_sub_le _ _ _
  have hsum := Finset.sum_le_sum fun a (_ha : a ∈ (Finset.univ : Finset α)) ↦
    hpoint a
  rw [Finset.sum_add_distrib] at hsum
  unfold tv
  nlinarith

/-- An event-probability discrepancy is bounded by total variation. -/
theorem event_gap_le_tv [Fintype α] [DecidableEq α]
    (P Q : FinDist α) (T : Finset α) :
    |(∑ x ∈ T, P.mass x) - ∑ x ∈ T, Q.mass x| ≤ P.tv Q := by
  let d : α → ℝ := fun x ↦ P.mass x - Q.mass x
  have htotal : ∑ x, d x = 0 := by
    simp only [d, Finset.sum_sub_distrib, P.sum_mass, Q.sum_mass, sub_self]
  have hcomp : ∑ x ∈ (Finset.univ \ T), d x = -(∑ x ∈ T, d x) := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ T), htotal, zero_sub]
  have hsplitAbs :
      (∑ x, |d x|) =
        (∑ x ∈ (Finset.univ \ T), |d x|) + ∑ x ∈ T, |d x| := by
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ T)]
    ring
  have hT : |∑ x ∈ T, d x| ≤ ∑ x ∈ T, |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have hTc : |∑ x ∈ (Finset.univ \ T), d x| ≤
      ∑ x ∈ (Finset.univ \ T), |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have habs : |∑ x ∈ (Finset.univ \ T), d x| = |∑ x ∈ T, d x| := by
    rw [hcomp, abs_neg]
  have hrewrite :
      (∑ x ∈ T, P.mass x) - ∑ x ∈ T, Q.mass x =
        ∑ x ∈ T, d x := by
    simp [d, Finset.sum_sub_distrib]
  rw [tv, hrewrite]
  rw [habs] at hTc
  nlinarith

/-- A distribution supported on `T` is at least `1 - |T|/|α|` away
from uniform. -/
theorem tv_uniform_ge_one_sub_support [Fintype α] [DecidableEq α]
    [Nonempty α] (P : FinDist α) (T : Finset α)
    (hsupport : ∀ x, x ∉ T → P.mass x = 0) :
    1 - (T.card : ℝ) / Fintype.card α ≤ P.tv (uniform α) := by
  have hout : ∑ x ∈ (Finset.univ \ T), P.mass x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hsupport x (Finset.mem_sdiff.mp hx).2
  have hPT : ∑ x ∈ T, P.mass x = 1 := by
    have hsplit := Finset.sum_sdiff_eq_sub
      (f := P.mass) (Finset.subset_univ T)
    rw [hout, P.sum_mass] at hsplit
    linarith
  have hcard : (T.card : ℝ) ≤ Fintype.card α := by
    exact_mod_cast Finset.card_le_univ T
  have hcardpos : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast Fintype.card_pos
  have hnonneg : 0 ≤ 1 - (T.card : ℝ) / Fintype.card α := by
    rw [sub_nonneg, div_le_one hcardpos]
    exact hcard
  have hevent := event_gap_le_tv P (uniform α) T
  have hsumU : ∑ x ∈ T, (uniform α).mass x =
      (T.card : ℝ) / Fintype.card α := by
    simp [div_eq_mul_inv]
  rw [hPT, hsumU, abs_of_nonneg hnonneg] at hevent
  exact hevent

/-- A denominator-free form of a min-entropy lower bound. -/
def PointBound [Fintype α] (P : FinDist α) (K : ℕ) : Prop :=
  ∀ a, P.mass a ≤ (K : ℝ)⁻¹

theorem uniform_pointBound [Fintype α] [Nonempty α] :
    (uniform α).PointBound (Fintype.card α) := by
  intro a
  exact le_rfl

theorem uniformOn_pointBound [Fintype α] [DecidableEq α]
    (A : Finset α) (hA : A.Nonempty) :
    (uniformOn A hA).PointBound A.card := by
  intro a
  by_cases ha : a ∈ A
  · simp [uniformOn, ha]
  · simp [uniformOn, ha, inv_nonneg]

/-- A pushed-forward uniform-on-`A` distribution is supported on `f '' A`. -/
theorem map_uniformOn_mass_eq_zero_of_notMem_image
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : Finset α) (hA : A.Nonempty) (f : α → β) {b : β}
    (hb : b ∉ A.image f) :
    ((uniformOn A hA).map f).mass b = 0 := by
  rw [map_mass]
  apply Finset.sum_eq_zero
  intro a ha
  have hfa : f a = b := (Finset.mem_filter.mp ha).2
  have haA : a ∉ A := by
    intro haA
    exact hb (Finset.mem_image.mpr ⟨a, haA, hfa⟩)
  simp [uniformOn, haA]

theorem pointBound_mono [Fintype α] {P : FinDist α} {K L : ℕ}
    (hLpos : 0 < L) (hLK : L ≤ K) (hK : P.PointBound K) :
    P.PointBound L := by
  intro a
  refine (hK a).trans ?_
  exact inv_anti₀ (by exact_mod_cast hLpos) (by exact_mod_cast hLK)

end FinDist

end Erdos788
