import ErdosProblems.Erdos67b.MRGSA10SecondSecondaryIntegral
import ErdosProblems.Erdos67b.MRGSA9SourceRadius
import ErdosProblems.Erdos67b.MRGSA9SmallPrimeDeletion
import ErdosProblems.Erdos67b.MRGSA9A14FullSeries
import ErdosProblems.Erdos67b.MRGlobalExpWeightedPrimeTail

/-!
# Finite Euler masses in the second GS A.10 secondary

This file scalarizes the two finite norm-Dirichlet masses left by the
distinguished-prime Chebyshev reduction.  The low mass is shifted as one
whole finite Euler product; the high mass uses the exponentially shifted
prime tail.  Both positive majorants are cut off at the actual finite
prefix, avoiding a false infinite-support Euler identity.
-/

open scoped BigOperators LSeries.notation ComplexOrder

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.PrimeEstimates Erdos67b.EulerQuantitative

/-- A finite norm mass coefficientwise dominated by a nonnegative
absolutely convergent Dirichlet series is bounded by its norm. -/
theorem gsFiniteNormDirichletMass_le_norm_LSeries_of_major
    {b : ArithmeticFunction ℂ} {a : ℕ → ℂ} {X : ℕ} {sigma : ℝ}
    (hsum : LSeriesSummable a (sigma : ℂ))
    (haNonneg : ∀ n, 0 ≤ a n)
    (hmajor : ∀ n ∈ Finset.Icc 1 X, ‖b n‖ ≤ ‖a n‖) :
    gsFiniteNormDirichletMass b X sigma ≤
      ‖LSeries a (sigma : ℂ)‖ := by
  have hterm (n : ℕ) :
      ‖LSeries.term a (sigma : ℂ) n‖ =
        (LSeries.term a (sigma : ℂ) n).re := by
    have hn := LSeries.term_nonneg (haNonneg n) sigma
    rw [Complex.nonneg_iff] at hn
    have heq : LSeries.term a (sigma : ℂ) n =
        ((LSeries.term a (sigma : ℂ) n).re : ℂ) := by
      apply Complex.ext
      · rfl
      · simpa using hn.2.symm
    calc
      ‖LSeries.term a (sigma : ℂ) n‖ =
          ‖((LSeries.term a (sigma : ℂ) n).re : ℂ)‖ := congrArg norm heq
      _ = (LSeries.term a (sigma : ℂ) n).re := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn.1]
  have hmass :
      (∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖) =
        (LSeries a (sigma : ℂ)).re := by
    unfold LSeries
    rw [Complex.re_tsum hsum]
    exact tsum_congr hterm
  unfold gsFiniteNormDirichletMass
  calc
    (∑ n ∈ Finset.Icc 1 X, ‖b n‖ * (n : ℝ) ^ (-sigma)) ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖LSeries.term a (sigma : ℂ) n‖ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [LSeries.norm_term_eq, if_neg hnpos.ne']
      rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ n), div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hmajor n hn) (by positivity)
    _ ≤ ∑' n : ℕ, ‖LSeries.term a (sigma : ℂ) n‖ :=
      hsum.norm.sum_le_tsum (Finset.Icc 1 X) (fun _ _ ↦ norm_nonneg _)
    _ = (LSeries a (sigma : ℂ)).re := hmass
    _ ≤ ‖LSeries a (sigma : ℂ)‖ := Complex.re_le_norm _

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.gsFiniteNormDirichletMass_le_norm_LSeries_of_major
