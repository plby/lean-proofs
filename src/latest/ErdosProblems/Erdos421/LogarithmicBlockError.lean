import ErdosProblems.Erdos421.LogarithmicCutoffError

/-! # Errors from freezing the cutoff on one prime block -/

namespace Erdos421

open MeasureTheory

noncomputable def logarithmicRoughBlockError (B w z : ℕ) (δ y : ℝ) : ℝ :=
  ∑ q ∈ sievePrimes w z, (q : ℝ)⁻¹ *
    (logarithmicRoughWindow (B / q) w δ (y - Real.log q) -
      logarithmicRoughWindow (B / q) q δ (y - Real.log q))

noncomputable def logarithmicCofactorBlockError (P : Finset ℕ) (B w z : ℕ)
    (δ y : ℝ) : ℝ :=
  ∑ q ∈ sievePrimes w z, (q : ℝ)⁻¹ *
    (logarithmicPrimeCofactorWindow P (B / q) w δ (y - Real.log q) -
      logarithmicPrimeCofactorWindow P (B / q) q δ (y - Real.log q))

theorem logarithmicRoughBlockError_integrable (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (logarithmicRoughBlockError B w z δ) := by
  exact integrable_finsetSum _ (fun q _ ↦
    (((logarithmicRoughWindow_integrable (B / q) w hδ).sub
      (logarithmicRoughWindow_integrable (B / q) q hδ)).comp_sub_right
        (Real.log q)).const_mul (q : ℝ)⁻¹)

theorem logarithmicCofactorBlockError_integrable (P : Finset ℕ) (B w z : ℕ)
    {δ : ℝ} (hδ : 0 < δ) : Integrable (logarithmicCofactorBlockError P B w z δ) := by
  exact integrable_finsetSum _ (fun q _ ↦
    (((logarithmicPrimeCofactorWindow_integrable P (B / q) w hδ).sub
      (logarithmicPrimeCofactorWindow_integrable P (B / q) q hδ)).comp_sub_right
        (Real.log q)).const_mul (q : ℝ)⁻¹)

theorem logarithmicRoughBlockError_nonneg (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ logarithmicRoughBlockError B w z δ y := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q)) (sub_nonneg.mpr
    (logarithmicRoughWindow_antitone _ hδ _
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1))

theorem logarithmicCofactorBlockError_nonneg (P : Finset ℕ) (B w z : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    0 ≤ logarithmicCofactorBlockError P B w z δ y := by
  apply Finset.sum_nonneg
  intro q hq
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q)) (sub_nonneg.mpr
    (logarithmicPrimeCofactorWindow_antitone P _ hδ _
      (Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1).1))

theorem logarithmicRoughBlockError_le (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    logarithmicRoughBlockError B w z δ y ≤
      ∑ q ∈ sievePrimes w z, ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow B (q * r) δ y := by
  apply Finset.sum_le_sum
  intro q hq
  obtain ⟨hwq, hqz⟩ := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
  have hqp := (Finset.mem_filter.mp hq).2
  have hcut := logarithmicRoughWindow_cutoff_error (B / q) (hwq.trans hqz.le) hδ
    (y - Real.log q)
  have hmono := logarithmicRoughWindow_antitone (B / q) hδ (y - Real.log q) hqz.le
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow (B / q) r δ (y - Real.log q) :=
      mul_le_mul_of_nonneg_left (le_trans (sub_le_sub_left hmono _) hcut)
        (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact logarithmicDivisorWindow_mul B r hqp.pos δ y

theorem logarithmicCofactorBlockError_le (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p)
    (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) (y : ℝ) :
    logarithmicCofactorBlockError P B w z δ y ≤
      ∑ q ∈ sievePrimes w z, ∑ p ∈ P, ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow B (q * (p * r)) δ y := by
  apply Finset.sum_le_sum
  intro q hq
  have hbounds := Finset.mem_Ico.mp (Finset.mem_filter.mp hq).1
  have hqp := (Finset.mem_filter.mp hq).2
  have hcut := logarithmicPrimeCofactorWindow_cutoff_error P hP (B / q)
    (hbounds.1.trans hbounds.2.le) hδ (y - Real.log q)
  have hmono := logarithmicPrimeCofactorWindow_antitone P (B / q) hδ
    (y - Real.log q) hbounds.2.le
  calc
    _ ≤ (q : ℝ)⁻¹ * ∑ p ∈ P, ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow (B / q) (p * r) δ (y - Real.log q) :=
      mul_le_mul_of_nonneg_left (le_trans (sub_le_sub_left hmono _) hcut)
        (inv_nonneg.mpr (Nat.cast_nonneg q))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro r hr
      exact logarithmicDivisorWindow_mul B (p * r) hqp.pos δ y

end Erdos421
