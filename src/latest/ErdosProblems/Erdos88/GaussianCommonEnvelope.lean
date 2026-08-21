import ErdosProblems.Erdos88.GaussianPartialUniform

open MeasureTheory ProbabilityTheory Set Complex
open scoped ENNReal NNReal BigOperators

namespace Erdos88.GaussianQuadratic

lemma holderEnvelope_le_threeSpectralEnvelope
    {s : ℝ} (hs : 0 ≤ s) (hsle : s ≤ 1 / 16) (t : ℝ) :
    holderEnvelope t ≤ threeSpectralEnvelope s t := by
  have hbase : 1 + 4 * s * t ^ 2 ≤ 1 + t ^ 2 / 2 := by
    have ht := sq_nonneg t
    nlinarith
  have hsmallBase : 0 < 1 + 4 * s * t ^ 2 := by positivity
  have hlargeBase : 1 ≤ 1 + t ^ 2 / 2 := by nlinarith [sq_nonneg t]
  unfold holderEnvelope threeSpectralEnvelope
  calc
    (1 + t ^ 2 / 2)⁻¹ = (1 + t ^ 2 / 2) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
    _ ≤ (1 + t ^ 2 / 2) ^ (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hlargeBase (by norm_num)
    _ ≤ (1 + 4 * s * t ^ 2) ^ (-3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hsmallBase hbase (by norm_num)

theorem diagonalCharModulus_le_relative_rankTwoEnvelope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a lam : ι → ℝ) (hsum : totalVariance a lam = 1)
    {rho : ℝ} (hrho : 0 < rho)
    (htail : ∀ S : Finset ι, S.card ≤ 2 →
      rho * (∑ i, (lam i) ^ 2) ≤ ∑ i with i ∉ S, (lam i) ^ 2)
    (t : ℝ) :
    diagonalCharModulus a lam t ≤
      threeSpectralEnvelope (min rho 1 / 192) t := by
  have htheta : 0 < min rho 1 := lt_min hrho zero_lt_one
  by_cases hsmall : ∀ i, coordinateVariance (a i) (lam i) ≤ 1 / 4
  · exact (diagonalCharModulus_le_holderEnvelope a lam hsum hsmall t).trans
      (holderEnvelope_le_threeSpectralEnvelope
        (by positivity) (by have := min_le_right rho 1; nlinarith) t)
  · push_neg at hsmall
    obtain ⟨j, hj⟩ := hsmall
    have hraw := diagonalCharModulus_le_influential_rankTwoEnvelope
      a lam j hrho htail t
    have hscale : min rho 1 / 192 ≤
        min rho 1 * coordinateVariance (a j) (lam j) / 48 := by
      have := mul_lt_mul_of_pos_left hj htheta
      nlinarith
    exact hraw.trans (by
      unfold threeSpectralEnvelope
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
      have hm := mul_le_mul_of_nonneg_right hscale (sq_nonneg t)
      nlinarith)

end Erdos88.GaussianQuadratic
