import ErdosProblems.Erdos421.LogarithmicDivisorMass
import ErdosProblems.Erdos421.LogarithmicPrimeCofactors
import ErdosProblems.Erdos421.RoughCutoffError

/-! # Positive divisor windows bound a changing sieve cutoff -/

namespace Erdos421

open MeasureTheory

theorem logarithmicRoughWindow_integrable (B z : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (logarithmicRoughWindow B z δ) := by
  change Integrable (fun y ↦ logarithmicRoughWindow B z δ y)
  simp_rw [logarithmicRoughWindow_real_sum]
  exact integrable_finsetSum _ (fun n _ ↦
    (logarithmicIntegerWeight_re_integrable hδ n).const_mul (roughIndicator n z))

theorem logarithmicPrimeCofactorWindow_integrable (P : Finset ℕ) (B z : ℕ)
    {δ : ℝ} (hδ : 0 < δ) : Integrable (logarithmicPrimeCofactorWindow P B z δ) := by
  exact integrable_finsetSum _ (fun p _ ↦
    ((logarithmicRoughWindow_integrable (B / p) z hδ).comp_sub_right (Real.log p)).const_mul
      (p : ℝ)⁻¹)

theorem logarithmicRoughWindow_cutoff_error (B : ℕ) {w z : ℕ} (hwz : w ≤ z)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    logarithmicRoughWindow B w δ y - logarithmicRoughWindow B z δ y ≤
      ∑ p ∈ sievePrimes w z, logarithmicDivisorWindow B p δ y := by
  rw [logarithmicRoughWindow_real_sum, logarithmicRoughWindow_real_sum,
    ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 B, (∑ p ∈ sievePrimes w z,
        if p ∣ n then (1 : ℝ) else 0) * (logarithmicIntegerWeight δ y n).re := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← sub_mul]
      exact mul_le_mul_of_nonneg_right (roughIndicator_difference_le n hwz)
        (logarithmicIntegerWeight_real_nonneg hδ y n)
    _ = _ := by
      simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      rfl

theorem logarithmicPrimeCofactorWindow_antitone (P : Finset ℕ) (B : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    Antitone (fun z ↦ logarithmicPrimeCofactorWindow P B z δ y) := by
  intro w z hwz
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (logarithmicRoughWindow_antitone _ hδ _ hwz)
    (inv_nonneg.mpr (Nat.cast_nonneg p))

theorem logarithmicPrimeCofactorWindow_cutoff_error (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (B : ℕ) {w z : ℕ} (hwz : w ≤ z)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    logarithmicPrimeCofactorWindow P B w δ y -
        logarithmicPrimeCofactorWindow P B z δ y ≤
      ∑ p ∈ P, ∑ q ∈ sievePrimes w z, logarithmicDivisorWindow B (p * q) δ y := by
  rw [logarithmicPrimeCofactorWindow_merge P hP,
    logarithmicPrimeCofactorWindow_merge P hP, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 B, (∑ p ∈ P, ∑ q ∈ sievePrimes w z,
        if p * q ∣ n then (1 : ℝ) else 0) * (logarithmicIntegerWeight δ y n).re := by
      apply Finset.sum_le_sum
      intro n hn
      rw [← sub_mul]
      exact mul_le_mul_of_nonneg_right (primeCofactorWeight_difference_le P n hwz)
        (logarithmicIntegerWeight_real_nonneg hδ y n)
    _ = _ := by
      simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.sum_comm]
      rfl

end Erdos421
