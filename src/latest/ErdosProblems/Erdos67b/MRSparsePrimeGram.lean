import ErdosProblems.Erdos67b.MRSmoothPrimePowerCutoff
import ErdosProblems.Erdos67b.MRSeparatedCauchyKernel

/-! # Separated Gram rows of the actual positive prime kernel -/

open scoped BigOperators

namespace Erdos67b

noncomputable section

def mrSparsePrimeGramBudget (R : ℕ) (P : ℝ) (N : ℕ) : ℝ :=
  20000 * P / (mrPrimeSieveExponent R * Real.log P) +
    mrPrimeKernelErrorConstant R * N * P ^ (1 - mrPrimeKernelSaving R)

theorem mrSparsePrimeGramBudget_nonneg (R : ℕ) {P : ℝ} (hP : 1 ≤ P) (N : ℕ) :
    0 ≤ mrSparsePrimeGramBudget R P N := by
  have := mrPrimeSieveExponent_pos R
  have := mrPrimeKernelErrorConstant_pos R
  have := Real.log_nonneg hP
  unfold mrSparsePrimeGramBudget
  positivity

theorem mrSmoothPrimeSelberg_row_sum_le {R : ℕ} {P h : ℝ} (hP : 1 < P)
    (hD : 1 ≤ mrPrimePowerCutoff R P)
    (hkernel : ∀ t : ℝ, |t| ≤ P ^ h →
      ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P t‖ ≤
        4000 * P / (mrPrimeSieveExponent R * Real.log P * (1 + t ^ 2)) +
          mrPrimeKernelErrorConstant R * P ^ (1 - mrPrimeKernelSaving R))
    (S : Finset ℝ) (hsep : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|)
    (hdiam : ∀ s ∈ S, ∀ t ∈ S, |t - s| ≤ P ^ h)
    {s : ℝ} (hs : s ∈ S) :
    (∑ t ∈ S, ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P (t - s)‖) ≤
      mrSparsePrimeGramBudget R P S.card := by
  have hcauchy := mrSeparated_cauchy_kernel_sum_le S hsep hs
  have hcoeff : 0 ≤ 4000 * P / (mrPrimeSieveExponent R * Real.log P) := by
    have := mrPrimeSieveExponent_pos R
    have := Real.log_pos hP
    positivity
  calc
    _ ≤ ∑ t ∈ S, (4000 * P /
        (mrPrimeSieveExponent R * Real.log P * (1 + (t - s) ^ 2)) +
          mrPrimeKernelErrorConstant R * P ^ (1 - mrPrimeKernelSaving R)) :=
      Finset.sum_le_sum (fun t ht ↦ hkernel (t - s) (hdiam s hs t ht))
    _ = (4000 * P / (mrPrimeSieveExponent R * Real.log P)) *
        (∑ t ∈ S, 1 / (1 + (t - s) ^ 2)) +
          mrPrimeKernelErrorConstant R * S.card * P ^ (1 - mrPrimeKernelSaving R) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, nsmul_eq_mul]
      congr 1
      · apply Finset.sum_congr rfl
        intro t ht
        rw [← div_div]
        ring
      · ring
    _ ≤ (4000 * P / (mrPrimeSieveExponent R * Real.log P)) * 5 +
        mrPrimeKernelErrorConstant R * S.card * P ^ (1 - mrPrimeKernelSaving R) := by
      gcongr
    _ = _ := by unfold mrSparsePrimeGramBudget; ring

theorem mrExists_sparsePrime_gram_row_bound (R : ℕ) (hR : 2 ≤ R)
    {h : ℝ} (hhR : 2 * h ≤ (R : ℝ)) :
    ∃ P₀ : ℝ, 1 < P₀ ∧ ∀ P ≥ P₀,
      2 ≤ mrPrimePowerCutoff R P ∧
      ∀ hD : 1 ≤ mrPrimePowerCutoff R P, ∀ S : Finset ℝ,
        (∀ s ∈ S, ∀ t ∈ S, s ≠ t → 1 ≤ |s - t|) →
        (∀ s ∈ S, ∀ t ∈ S, |t - s| ≤ P ^ h) →
        ∀ s ∈ S,
          (∑ t ∈ S, ‖mrSmoothPrimeSelbergKernel (mrPrimePowerCutoff R P) hD P (t - s)‖) ≤
            mrSparsePrimeGramBudget R P S.card := by
  obtain ⟨P₀, hP₀one, hP₀⟩ := mrExists_smoothPrime_powerCutoff_kernel_bound R hR hhR
  refine ⟨P₀, hP₀one, ?_⟩
  intro P hP
  obtain ⟨hDtwo, hkernel⟩ := hP₀ P hP
  refine ⟨hDtwo, ?_⟩
  intro hD S hsep hdiam s hs
  exact mrSmoothPrimeSelberg_row_sum_le (hP₀one.trans_le hP) hD
    (hkernel hD) S hsep hdiam hs

end

end Erdos67b
