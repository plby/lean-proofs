/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPinnedResidualProduct
import ErdosProblems.Erdos4b.GeneralFourierPrimeCutoffProducts
import ErdosProblems.Erdos4b.SingularSeriesAverage

/-!
# Exact finite singular-factor cancellation for pinned coverage

The combined product dominates one half of the residual cofactor local
product. This is the same cofactor correction appearing reciprocally in
the residual prime-fibre sieve bound.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem prod_pinnedCombinedLocalRatio_eq
    {K w m p₀ Y : ℕ} (h : Fin K) (hwy : w ≤ Y) :
    (∏ p ∈ boundedFourierPrimes Y, pinnedCombinedLocalRatio h w m p₀ p) =
      pinnedSingularSeries h w m p₀ Y * fixedSingularInverseFactor K w Y m /
        (largeGapSingularSeries (preSievedShifts K w) m 1 w *
          genericRoughSingularProduct K w Y) := by
  have hlocal (p : Nat.Primes) : pinnedCombinedLocalRatio h w m p₀ p =
      pinnedLocalFactor h w m p₀ p *
        (if w < p.val ∧ p.val ∣ m then ((p : ℝ) - 2 * K) / ((p : ℝ) - K) else 1) /
          ((if p.val ≤ w then largeGapLocalFactor (preSievedShifts K w) m 1 p else 1) *
            (if w < p.val then genericLargeGapLocalFactor K p else 1)) := by
    by_cases hpw : p.val ≤ w
    · simp only [pinnedCombinedLocalRatio, if_pos hpw,
        Nat.not_lt.mpr hpw, false_and, if_false, mul_one]
    · have hwp : w < p.val := Nat.lt_of_not_ge hpw
      simp only [pinnedCombinedLocalRatio, if_neg hpw, hwp, true_and, one_mul, if_true]
  simp_rw [hlocal, Finset.prod_div_distrib, Finset.prod_mul_distrib]
  exact congrArg₂ (fun x y : ℝ ↦ x / y)
    (congrArg₂ (fun x y : ℝ ↦ x * y) rfl
      (prod_boundedFourierPrimes_fixed w Y m (fun p ↦ ((p : ℝ) - 2 * K) / ((p : ℝ) - K))))
    (congrArg₂ (fun x y : ℝ ↦ x * y)
      (prod_boundedFourierPrimes_small hwy (fun p ↦
        largeGapLocalFactor (preSievedShifts K w) m 1 p))
      (prod_boundedFourierPrimes_rough w Y (genericLargeGapLocalFactor K)))

theorem half_residualCofactorLocalProduct_le_pinnedCombinedSingularRatio
    {K w m p₀ Y : ℕ} (h : Fin K)
    (hfour : 4 * K ≤ w) (hm : 0 < m) (hmeven : Even m) (hp₀ : p₀.Prime)
    (hwy : w ≤ Y) (hYp₀ : Y < p₀) (hcop : (m * p₀ - 1).Coprime (primorial Y)) :
    (1 / 2 : ℝ) * residualCofactorLocalProduct Y m ≤
      pinnedSingularSeries h w m p₀ Y * fixedSingularInverseFactor K w Y m /
        (largeGapSingularSeries (preSievedShifts K w) m 1 w *
          genericRoughSingularProduct K w Y) := by
  have hY2 : 2 ≤ Y := by have := h.pos; omega
  calc
    _ = ∏ p ∈ boundedFourierPrimes Y, pinnedResidualLocalComparison m p :=
      (prod_pinnedResidualLocalComparison_eq_half_mul_cofactor m hY2).symm
    _ ≤ ∏ p ∈ boundedFourierPrimes Y, pinnedCombinedLocalRatio h w m p₀ p :=
      prod_pinnedResidualLocalComparison_le_combined h hfour hm hmeven hp₀ hYp₀ hcop
    _ = _ := prod_pinnedCombinedLocalRatio_eq h hwy

end

end Erdos4b
