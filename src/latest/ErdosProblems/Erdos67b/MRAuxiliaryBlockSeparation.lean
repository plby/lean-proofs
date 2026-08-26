import ErdosProblems.Erdos67b.MRCofactorScheduledBlocks
import ErdosProblems.Erdos67b.MRCofactorRectangleIdentity

/-!
# Separation of the auxiliary interval from the scheduled blocks

The source auxiliary lower logarithmic endpoint exceeds `sqrt (log X)`.
Both prime disjointness and absence of the rounded interval from the
original block family follow with the integer endpoints retained.
-/

namespace Erdos67b

noncomputable section

theorem mrLogPrimeInterval_disjoint_of_gap {a b c d : ℝ} (hgap : b < c) :
    Disjoint (primesInBlock (mrLogPrimeInterval a b))
      (primesInBlock (mrLogPrimeInterval c d)) := by
  apply Finset.disjoint_left.mpr
  intro p hp hq
  have hlow := (mem_primesInBlock_mrLogPrimeInterval_bounds hq).1
  have hupp := (mem_primesInBlock_mrLogPrimeInterval_bounds hp).2
  linarith

theorem mrAuxiliaryInterval_disjoint_scheduled
    {eta p₁ q₁ a b : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {J X : ℕ}
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    (hgap : Real.sqrt (Real.log (X : ℝ)) < a) :
    ∀ I ∈ mrScheduledBlocks p₁ q₁ J,
      Disjoint (primesInBlock (mrLogPrimeInterval a b)) (primesInBlock I) := by
  intro I hI
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hI
  have hi := Finset.mem_Icc.mp hj
  have hmono := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget hi.1 hi.2
  exact (mrLogPrimeInterval_disjoint_of_gap ((hmono.trans hupper).trans_lt hgap)).symm

theorem mrAuxiliaryInterval_not_mem_scheduled
    {eta p₁ q₁ a b : ℝ} (heta : eta ≤ 1 / 12) (hp : 2 ≤ p₁)
    (hq : 1 ≤ q₁) (hpq : p₁ ≤ q₁) (hlogq : 1 ≤ Real.log q₁)
    (hbudget : 4096 * Real.log q₁ ≤ eta * p₁) {J X : ℕ}
    (hupper : mrLogScheduleUpper q₁ J ≤ Real.sqrt (Real.log (X : ℝ)))
    (hgap : Real.sqrt (Real.log (X : ℝ)) < a) (ha : 2 ≤ a) (hab : 2 * a ≤ b) :
    mrLogPrimeInterval a b ∉ mrScheduledBlocks p₁ q₁ J := by
  intro hI
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hI
  have hi := Finset.mem_Icc.mp hj
  have hmono := mrLogScheduleUpper_mono_positive heta hp hq hpq hlogq hbudget hi.1 hi.2
  have hu : ((mrScheduledPrimeInterval p₁ q₁ j).2 : ℝ) ≤
      Real.exp (Real.sqrt (Real.log (X : ℝ))) := by
    calc
      _ ≤ Real.exp (mrLogScheduleUpper q₁ j) := Nat.floor_le (Real.exp_pos _).le
      _ ≤ _ := Real.exp_le_exp.mpr (hmono.trans hupper)
  rw [heq] at hu
  have he := Real.exp_lt_exp.mpr hgap
  have hl : Real.exp a ≤ ((mrLogPrimeInterval a b).1 : ℝ) := Nat.le_ceil _
  have horder : ((mrLogPrimeInterval a b).1 : ℝ) ≤ (mrLogPrimeInterval a b).2 := by
    exact_mod_cast (mrLogPrimeInterval_endpoint_bounds ha hab).2.1
  linarith

open Classical in
theorem mrTypicalCofactorRectangle_eq_full_of_not_mem
    {blocks : Finset (ℕ × ℕ)} {I : ℕ × ℕ} (hI : I ∉ blocks)
    (K : ℕ × ℕ) (X : ℕ) :
    mrTypicalCofactorRectangle blocks I K X =
      (mrDyadicCofactorRectangle K X).filter (HasTypicalFactorization blocks) := by
  unfold mrTypicalCofactorRectangle
  rw [Finset.erase_eq_of_notMem hI]

end

end Erdos67b
