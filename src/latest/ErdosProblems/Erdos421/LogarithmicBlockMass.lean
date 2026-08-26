import ErdosProblems.Erdos421.LogarithmicBlockError

/-! # A reciprocal-square bound for the total cutoff error on a prime block -/

namespace Erdos421

open MeasureTheory

theorem logarithmicRoughBlockError_integral_le (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, logarithmicRoughBlockError B w z δ y) ≤
      (harmonic B : ℝ) * (∑ q ∈ sievePrimes w z, (q : ℝ)⁻¹) ^ 2 := by
  calc
    _ ≤ ∫ y : ℝ, ∑ q ∈ sievePrimes w z, ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow B (q * r) δ y :=
      integral_mono (logarithmicRoughBlockError_integrable B w z hδ)
        (integrable_finsetSum _ (fun q _ ↦ integrable_finsetSum _ (fun r _ ↦
          logarithmicDivisorWindow_integrable B (q * r) hδ)))
        (logarithmicRoughBlockError_le B w z hδ)
    _ = ∑ q ∈ sievePrimes w z, ∑ r ∈ sievePrimes w z,
        ∫ y : ℝ, logarithmicDivisorWindow B (q * r) δ y := by
      rw [integral_finsetSum _ (fun q _ ↦ integrable_finsetSum _ (fun r _ ↦
        logarithmicDivisorWindow_integrable B (q * r) hδ))]
      apply Finset.sum_congr rfl
      intro q hq
      exact integral_finsetSum _ (fun r _ ↦ logarithmicDivisorWindow_integrable B (q * r) hδ)
    _ ≤ ∑ q ∈ sievePrimes w z, ∑ r ∈ sievePrimes w z, (harmonic B : ℝ) / (q * r : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      exact logarithmicDivisorWindow_integral_le B
        (Nat.mul_pos (Finset.mem_filter.mp hq).2.pos (Finset.mem_filter.mp hr).2.pos) hδ
    _ = _ := by
      simp only [Nat.cast_mul, mul_inv, div_eq_mul_inv, pow_two,
        Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      ring

theorem logarithmicCofactorBlockError_integral_le (P : Finset ℕ)
    (hP : ∀ p ∈ P, 0 < p) (B w z : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (∫ y : ℝ, logarithmicCofactorBlockError P B w z δ y) ≤
      (harmonic B : ℝ) * (∑ p ∈ P, (p : ℝ)⁻¹) *
        (∑ q ∈ sievePrimes w z, (q : ℝ)⁻¹) ^ 2 := by
  calc
    _ ≤ ∫ y : ℝ, ∑ q ∈ sievePrimes w z, ∑ p ∈ P, ∑ r ∈ sievePrimes w z,
        logarithmicDivisorWindow B (q * (p * r)) δ y :=
      integral_mono (logarithmicCofactorBlockError_integrable P B w z hδ)
        (integrable_finsetSum _ (fun q _ ↦ integrable_finsetSum _ (fun p _ ↦
          integrable_finsetSum _ (fun r _ ↦
            logarithmicDivisorWindow_integrable B (q * (p * r)) hδ))))
        (logarithmicCofactorBlockError_le P hP B w z hδ)
    _ = ∑ q ∈ sievePrimes w z, ∑ p ∈ P, ∑ r ∈ sievePrimes w z,
        ∫ y : ℝ, logarithmicDivisorWindow B (q * (p * r)) δ y := by
      rw [integral_finsetSum _ (fun q _ ↦ integrable_finsetSum _ (fun p _ ↦
        integrable_finsetSum _ (fun r _ ↦
          logarithmicDivisorWindow_integrable B (q * (p * r)) hδ)))]
      apply Finset.sum_congr rfl
      intro q hq
      rw [integral_finsetSum _ (fun p _ ↦ integrable_finsetSum _ (fun r _ ↦
        logarithmicDivisorWindow_integrable B (q * (p * r)) hδ))]
      apply Finset.sum_congr rfl
      intro p hp
      exact integral_finsetSum _
        (fun r _ ↦ logarithmicDivisorWindow_integrable B (q * (p * r)) hδ)
    _ ≤ ∑ q ∈ sievePrimes w z, ∑ p ∈ P, ∑ r ∈ sievePrimes w z,
        (harmonic B : ℝ) / (q * (p * r) : ℕ) := by
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      exact logarithmicDivisorWindow_integral_le B
        (Nat.mul_pos (Finset.mem_filter.mp hq).2.pos
          (Nat.mul_pos (hP p hp) (Finset.mem_filter.mp hr).2.pos)) hδ
    _ = _ := by
      simp only [Nat.cast_mul, mul_inv, div_eq_mul_inv, mul_assoc,
        ← Finset.mul_sum, ← Finset.sum_mul]
      ring

end Erdos421
