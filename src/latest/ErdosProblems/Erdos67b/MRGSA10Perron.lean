import ErdosProblems.Erdos67b.MRGSA10TailoredCoefficient
import ErdosProblems.Erdos67b.MRHalaszPerron

/-!
# Quantitative Perron projection for the tailored A.10 coefficient

This is the first analytic step of source equation (A.10).  It applies the
already formalized countable truncated Perron theorem to the exact four-fold
coefficient and exposes, without an interface proposition, both Perron error
terms.
-/

open scoped BigOperators
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The standard Perron integral after the source change of variable
`z = s - α - β`. -/
def gsA10TailoredPerronIntegral
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (c alpha beta T : ℝ) : ℂ :=
  dirichletPerronIntegral
    (gsA10TailoredCoefficient low high lambda y X alpha beta)
    X (c - alpha - beta) T

/-- Exact expansion of the tailored Perron integral into the four source
Dirichlet factors. -/
theorem gsA10TailoredPerronIntegral_eq_fourFactors
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (c alpha beta T : ℝ)
    (hT : 0 ≤ T)
    (hlow : ∀ t : ℝ, |t| ≤ T →
      LSeriesSummable low
        (((c - alpha - beta : ℝ) : ℂ) + t * I))
    (hhigh : ∀ t : ℝ, |t| ≤ T →
      LSeriesSummable high
        ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
          ((alpha + 2 * beta : ℝ) : ℂ))) :
    gsA10TailoredPerronIntegral low high lambda y X c alpha beta T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          ((LSeries low
              (((c - alpha - beta : ℝ) : ℂ) + t * I) *
            LSeries high
              ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                ((alpha + 2 * beta : ℝ) : ℂ))) *
            (LSeries (gsA10LambdaWindow lambda y X)
                ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                  (alpha : ℂ)) *
              LSeries (gsA10LambdaWindow lambda y X)
                ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                  ((alpha + 2 * beta : ℝ) : ℂ)))) *
            (X : ℂ) ^
              (((c - alpha - beta : ℝ) : ℂ) + t * I) /
            (((c - alpha - beta : ℝ) : ℂ) + t * I) := by
  unfold gsA10TailoredPerronIntegral dirichletPerronIntegral
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  dsimp only
  rw [LSeries_gsA10TailoredCoefficient
    low high lambda y X alpha beta
    (((c - alpha - beta : ℝ) : ℂ) + t * I)]
  · rfl
  · exact hlow t (by
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact abs_le.mpr ⟨ht.1, ht.2⟩)
  · exact hhigh t (by
      rw [Set.uIcc_of_le (by linarith)] at ht
      exact abs_le.mpr ⟨ht.1, ht.2⟩)

/-- The explicit truncated-Perron error for one pair `(α,β)`. -/
theorem norm_gsA10TailoredStarredSum_sub_perron_le
    (low high lambda : ArithmeticFunction ℂ)
    (y X : ℕ) (c alpha beta T : ℝ)
    (hX : 0 < X)
    (hsigma : 0 < c - alpha - beta)
    (hsigmaUpper : c - alpha - beta ≤ 2)
    (hT : 0 < T)
    (hlow : LSeriesSummable low (c - alpha - beta : ℝ))
    (hhigh : LSeriesSummable high
      (((c - alpha - beta : ℝ) : ℂ) +
        ((alpha + 2 * beta : ℝ) : ℂ))) :
    ‖dirichletPerronStarredSum
          (gsA10TailoredCoefficient low high lambda y X alpha beta) X -
        gsA10TailoredPerronIntegral
          low high lambda y X c alpha beta T‖ ≤
      dirichletPerronNearMass
          (gsA10TailoredCoefficient low high lambda y X alpha beta) X T +
        (32 * (X : ℝ) ^ (c - alpha - beta) / T) *
          dirichletPerronCoefficientMass
            (gsA10TailoredCoefficient low high lambda y X alpha beta)
            (c - alpha - beta) := by
  apply norm_dirichletPerronStarredSum_sub_integral_le
  · exact gsA10TailoredCoefficient_LSeriesSummable
      low high lambda y X alpha beta (c - alpha - beta : ℝ)
      hlow hhigh
  · exact hX
  · exact hsigma
  · exact hsigmaUpper
  · exact hT

end

end Erdos67b.MRHalaszBands
