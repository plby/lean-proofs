import ErdosProblems.Erdos67b.MRGSA10PositiveLine

/-!
# The specialized two-block A.10 Perron input

This file instantiates the generic four-fold Perron coefficient with the
actual alternating low factor, common high-prime factor, and its generalized
Mangoldt coefficient.  All convergence hypotheses are discharged from the
natural inequalities on the shifted contour.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The high-prime arithmetic wrapper is absolutely summable on `re s > 1`. -/
theorem gsA9HighArithmetic_LSeriesSummable
    {f : ℕ → ℂ} (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (y : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (gsA9HighArithmetic f y) s := by
  have hbase : LSeriesSummable (gsA9High f y) s :=
    primeBandCoefficient_LSeriesSummable hbound _ hs
  exact (LSeriesSummable_congr s
    (f := gsA9HighArithmetic f y) (g := gsA9High f y)
    (fun {n} hn ↦ gsA9HighArithmetic_apply_of_ne_zero f y hn)).2 hbase

/-- The arithmetic wrapper does not change the high-prime L-series. -/
theorem LSeries_gsA9HighArithmetic
    (f : ℕ → ℂ) (y : ℕ) (s : ℂ) :
    LSeries (gsA9HighArithmetic f y) s = LSeries (gsA9High f y) s := by
  apply LSeries_congr
  intro n hn
  exact gsA9HighArithmetic_apply_of_ne_zero f y hn

/-- The actual four-fold arithmetic coefficient in the two-block A.10
integral. -/
def gsA10TwoBlockTailoredCoefficient
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) : ArithmeticFunction ℂ :=
  gsA10TailoredCoefficient
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y)
    y X alpha beta

/-- Absolute convergence of the actual A.10 coefficient at its shifted
Perron line. -/
theorem gsA10TwoBlockTailoredCoefficient_LSeriesSummable
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) {s : ℂ}
    (hlow : 0 < s.re)
    (hhigh : 1 < (s + ((alpha + 2 * beta : ℝ) : ℂ)).re) :
    LSeriesSummable
      (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) s := by
  apply gsA10TailoredCoefficient_LSeriesSummable
  · exact gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y hlow
  · exact gsA9HighArithmetic_LSeriesSummable hbound y hhigh

/-- The explicit Perron error for the actual two-block A.10 coefficient.
The high factor is evaluated at real part `c + beta`, while the finite low
factor only needs `c - alpha - beta > 0`. -/
theorem norm_gsA10TwoBlockTailoredStarredSum_sub_perron_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (c alpha beta T : ℝ)
    (hX : 0 < X)
    (hlow : 0 < c - alpha - beta)
    (hlowUpper : c - alpha - beta ≤ 2)
    (hhigh : 1 < c + beta)
    (hT : 0 < T) :
    ‖dirichletPerronStarredSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X c alpha beta T‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T +
        (32 * (X : ℝ) ^ (c - alpha - beta) / T) *
          dirichletPerronCoefficientMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta)
            (c - alpha - beta) := by
  apply norm_gsA10TailoredStarredSum_sub_perron_le
  · exact hX
  · exact hlow
  · exact hlowUpper
  · exact hT
  · exact gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by simpa using hlow)
  · apply gsA9HighArithmetic_LSeriesSummable hbound y
    norm_num at ⊢
    linarith

/-- Exact four-factor contour expansion for the specialized A.10 Perron
integral.  The conclusion is kept in the generic four-factor form so that
the later maximum-modulus estimates can rewrite each factor independently. -/
theorem gsA10TwoBlockTailoredPerronIntegral_eq_fourFactors
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (c alpha beta T : ℝ)
    (hT : 0 ≤ T)
    (hlow : 0 < c - alpha - beta)
    (hhigh : 1 < c + beta) :
    gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X c alpha beta T =
      (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
        ∫ t in -T..T,
          ((LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
              (((c - alpha - beta : ℝ) : ℂ) + t * I) *
            LSeries (gsA9HighArithmetic f y)
              ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                ((alpha + 2 * beta : ℝ) : ℂ))) *
            (LSeries (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
                ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                  (alpha : ℂ)) *
              LSeries (gsA10LambdaWindow
                (gsA9HighGeneralizedMangoldt hmul y) y X)
                ((((c - alpha - beta : ℝ) : ℂ) + t * I) +
                  ((alpha + 2 * beta : ℝ) : ℂ)))) *
            (X : ℂ) ^
              (((c - alpha - beta : ℝ) : ℂ) + t * I) /
            (((c - alpha - beta : ℝ) : ℂ) + t * I) := by
  apply gsA10TailoredPerronIntegral_eq_fourFactors
  · exact hT
  · intro t ht
    apply gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y
    simpa using hlow
  · intro t ht
    apply gsA9HighArithmetic_LSeriesSummable hbound y
    norm_num at ⊢
    linarith

end

end Erdos67b.MRHalaszBands
