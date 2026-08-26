import ErdosProblems.Erdos421.TimeReciprocal
import ErdosProblems.Erdos421.LogarithmicBounds

/-! # Gram-row sums at separated real sampling points -/

namespace Erdos421

open MeasureTheory

theorem separated_inverseDistance_sum_le (S : Finset ℕ) (t : ℕ → ℝ) {A B c : ℝ}
    (hc : A ≤ c ∧ c ≤ B) (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|) :
    (∑ i ∈ S, inverseDistance c (t i)) ≤ 4 * Real.log (B - A + 2) := by
  have hAB : A ≤ B := hc.1.trans hc.2
  let U := B - A + 1
  have hU : 0 ≤ U := by dsimp only [U]; linarith
  have hcont := inverseDistance_continuous c
  have hint : (∫ x in A..B + 1, inverseDistance c x) ≤ 2 * Real.log (B - A + 2) := by
    have h := intervalIntegral.integral_mono_interval (μ := volume)
      (show c - U ≤ A by dsimp only [U]; linarith [hc.2])
      (show A ≤ B + 1 by linarith)
      (show B + 1 ≤ c + U by dsimp only [U]; linarith [hc.1])
      (Filter.Eventually.of_forall (inverseDistance_nonneg c))
      (hcont.intervalIntegrable (c - U) (c + U))
    rw [integral_inverseDistance_centered c hU] at h
    have heq : 1 + U = B - A + 2 := by dsimp only [U]; ring
    rwa [heq] at h
  calc
    _ ≤ ∑ i ∈ S, 2 * ∫ x in t i..t i + 1, inverseDistance c x :=
      Finset.sum_le_sum (fun i _ ↦ inverseDistance_unit_evaluation c (t i))
    _ = 2 * ∑ i ∈ S, ∫ x in t i..t i + 1, inverseDistance c x := (Finset.mul_sum ..).symm
    _ ≤ 2 * ∫ x in A..B + 1, inverseDistance c x :=
      mul_le_mul_of_nonneg_left (sum_unit_integrals_le S t hAB ht hsep hcont
        (inverseDistance_nonneg c)) (by norm_num)
    _ ≤ 2 * (2 * Real.log (B - A + 2)) := mul_le_mul_of_nonneg_left hint (by norm_num)
    _ = _ := by ring

theorem separated_inverse_distance_row_le (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    {i : ℕ} (hi : i ∈ S) :
    (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) ≤ 4 * Real.log (B - A + 2) := by
  simpa only [inverseDistance, abs_sub_comm] using
    separated_inverseDistance_sum_le S t (ht i hi) ht hsep

theorem logarithmic_kernel_row_bound {M N : ℕ} (hM : 0 < M) (hN : N ≤ M)
    (S : Finset ℕ) (t : ℕ → ℝ) {A B : ℝ}
    (ht : ∀ i ∈ S, A ≤ t i ∧ t i ≤ B)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → 1 ≤ |t i - t j|)
    {i : ℕ} (hi : i ∈ S) :
    (∑ j ∈ S, ‖logarithmicSum M N (t i - t j)‖) ≤
      2560 * M * Real.log (B - A + 2) + 640 * S.card * Real.sqrt (B - A) := by
  have htime := ht i hi
  have hpoint : ∀ j ∈ S, ‖logarithmicSum M N (t i - t j)‖ ≤
      640 * ((M : ℝ) / (1 + |t i - t j|) + Real.sqrt (B - A)) := by
    intro j hj
    have hjtime := ht j hj
    have hdist : |t i - t j| ≤ B - A := abs_le.mpr ⟨by linarith, by linarith⟩
    have hsqrt := Real.sqrt_le_sqrt hdist
    exact (logarithmicSum_kernel_bound hM hN (t i - t j)).trans
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsqrt) (by norm_num))
  calc
    _ ≤ ∑ j ∈ S, 640 * ((M : ℝ) / (1 + |t i - t j|) + Real.sqrt (B - A)) :=
      Finset.sum_le_sum hpoint
    _ = ∑ j ∈ S, ((640 * M : ℝ) * (1 / (1 + |t i - t j|)) +
        640 * Real.sqrt (B - A)) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 640 * M * (∑ j ∈ S, (1 : ℝ) / (1 + |t i - t j|)) +
        640 * S.card * Real.sqrt (B - A) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ 640 * M * (4 * Real.log (B - A + 2)) +
        640 * S.card * Real.sqrt (B - A) :=
      add_le_add (mul_le_mul_of_nonneg_left (separated_inverse_distance_row_le S t ht hsep hi)
        (by positivity)) le_rfl
    _ = _ := by ring

end Erdos421
