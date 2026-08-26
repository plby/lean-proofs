/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedSmallSingularRatios

/-!
# The combined local coverage ratio at every prime

The lower comparison has the exact factor one half at two, the residual
cofactor correction at odd cofactor primes, and one elsewhere.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

def pinnedCombinedLocalRatio {K : ℕ} (h : Fin K) (w m p₀ : ℕ) (p : Nat.Primes) : ℝ :=
  if p.val ≤ w then
    pinnedLocalFactor h w m p₀ p / largeGapLocalFactor (preSievedShifts K w) m 1 p
  else
    pinnedLocalFactor h w m p₀ p *
      (if p.val ∣ m then ((p : ℝ) - 2 * K) / ((p : ℝ) - K) else 1) /
        genericLargeGapLocalFactor K p

def pinnedResidualLocalComparison (m p : ℕ) : ℝ :=
  if p = 2 then 1 / 2 else if p ∣ m then ((p : ℝ) - 2) / ((p : ℝ) - 1) else 1

theorem pinnedResidualLocalComparison_nonneg (m : ℕ) {p : ℕ} (hp : p.Prime) :
    0 ≤ pinnedResidualLocalComparison m p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold pinnedResidualLocalComparison
  split_ifs
  · norm_num
  · exact div_nonneg (by linarith) (by linarith)
  · norm_num

theorem pinnedResidualLocalComparison_le_combined
    {K w m p₀ Y : ℕ} (h : Fin K) (p : Nat.Primes)
    (hfour : 4 * K ≤ w) (hm : 0 < m) (hmeven : Even m) (hp₀ : p₀.Prime)
    (hYp₀ : Y < p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) (hpY : p.val ≤ Y) :
    pinnedResidualLocalComparison m p ≤ pinnedCombinedLocalRatio h w m p₀ p := by
  have hKpos := h.pos
  have hKw : K ≤ w := by omega
  have hw2 : 2 ≤ w := by omega
  have hnot := pinnedResidual_not_dvd_prime hp₀ hYp₀ p hpY
  have hnum := pinnedResidual_companion_numerator_ne_zero hm hp₀.pos hcop p hpY
  by_cases hpw : p.val ≤ w
  · rw [pinnedCombinedLocalRatio, if_pos hpw]
    by_cases hpm : p.val ∣ m
    · rw [pinnedSmallLocalRatio_eq_of_cofactor h p hpw hnot hnum hpm]
      by_cases hp2 : p.val = 2
      · simp only [pinnedResidualLocalComparison, hp2, if_true, Nat.cast_ofNat]
        norm_num
      · simp only [pinnedResidualLocalComparison, if_neg hp2, if_pos hpm]
        exact cofactor_residual_factor_le_one_sub_inv (by exact_mod_cast p.property.one_lt)
    · have hp2 : p.val ≠ 2 := fun he ↦ hpm (he ▸ hmeven.two_dvd)
      have hp2lt : 2 < p.val := lt_of_le_of_ne p.property.two_le (Ne.symm hp2)
      simp only [pinnedResidualLocalComparison, if_neg hp2, if_neg hpm]
      exact one_le_pinnedSmallLocalRatio_of_not_cofactor h p hpw hp2lt hnot hnum hpm
  · have hwp : w < p.val := Nat.lt_of_not_ge hpw
    have hp2 : p.val ≠ 2 := by omega
    have hpK : 2 * K < p.val := by omega
    rw [pinnedCombinedLocalRatio, if_neg hpw]
    by_cases hpm : p.val ∣ m
    · simp only [pinnedResidualLocalComparison, if_neg hp2, if_pos hpm]
      exact cofactor_residual_factor_le_pinnedLocal_combined_ratio h p hKw hwp hpK hnot hnum hpm
    · simp only [pinnedResidualLocalComparison, if_neg hp2, if_neg hpm, mul_one]
      exact one_le_pinnedLocalFactor_div_generic h p hKw hwp hpK hnot hnum

theorem prod_pinnedResidualLocalComparison_le_combined
    {K w m p₀ Y : ℕ} (h : Fin K)
    (hfour : 4 * K ≤ w) (hm : 0 < m) (hmeven : Even m) (hp₀ : p₀.Prime)
    (hYp₀ : Y < p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (∏ p ∈ boundedFourierPrimes Y, pinnedResidualLocalComparison m p) ≤
      ∏ p ∈ boundedFourierPrimes Y, pinnedCombinedLocalRatio h w m p₀ p := by
  apply Finset.prod_le_prod
  · intro p hp
    exact pinnedResidualLocalComparison_nonneg m p.property
  · intro p hp
    exact pinnedResidualLocalComparison_le_combined h p hfour hm hmeven hp₀ hYp₀ hcop
      ((mem_boundedFourierPrimes Y p).mp hp)

end

end Erdos4b
