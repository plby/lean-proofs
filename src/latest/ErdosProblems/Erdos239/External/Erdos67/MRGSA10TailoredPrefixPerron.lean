import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SpecializedPerron

/-!
# From the inclusive A.10 prefix to its tailored Perron integral

The countable Perron theorem is naturally stated for the starred partial
sum, whereas the finite A.10 reconstruction uses the inclusive positive
prefix.  This file records the exact half-endpoint correction and then
specializes it to the two-block tailored coefficient.  In particular, no
prefix estimate or desired contour bound is assumed.
-/

open scoped BigOperators
open Complex Finset

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The inclusive positive prefix differs from the Perron starred sum by
exactly half of its endpoint coefficient. -/
theorem positivePrefixSum_eq_dirichletPerronStarredSum_add_half
    (a : ℕ → ℂ) {X : ℕ} (hX : 0 < X) :
    positivePrefixSum a X =
      dirichletPerronStarredSum a X + (1 / 2 : ℂ) * a X := by
  unfold positivePrefixSum dirichletPerronStarredSum
  rw [show a 0 = ∑ k ∈ Finset.range 1, a k by simp]
  rw [← Finset.sum_Ico_eq_sub a (by omega : 1 ≤ X + 1)]
  rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ X)]
  ring

/-- A starred-sum Perron error immediately gives the corresponding bound
for the inclusive positive prefix, with the exact half-endpoint term. -/
theorem norm_positivePrefixSum_sub_le_of_starred_sub_le
    {a : ℕ → ℂ} {X : ℕ} {P : ℂ} {E : ℝ}
    (hX : 0 < X)
    (hstar : ‖dirichletPerronStarredSum a X - P‖ ≤ E) :
    ‖positivePrefixSum a X - P‖ ≤ E + (1 / 2 : ℝ) * ‖a X‖ := by
  rw [positivePrefixSum_eq_dirichletPerronStarredSum_add_half a hX]
  have hdecomp :
      dirichletPerronStarredSum a X + (1 / 2 : ℂ) * a X - P =
        (dirichletPerronStarredSum a X - P) + (1 / 2 : ℂ) * a X := by
    ring
  rw [hdecomp]
  calc
    ‖(dirichletPerronStarredSum a X - P) + (1 / 2 : ℂ) * a X‖ ≤
        ‖dirichletPerronStarredSum a X - P‖ +
          ‖(1 / 2 : ℂ) * a X‖ := norm_add_le _ _
    _ ≤ E + (1 / 2 : ℝ) * ‖a X‖ := by
      gcongr
      rw [norm_mul]
      norm_num

/-- Pointwise Perron projection for the exact two-block coefficient which
occurs under the A.10 alpha--beta rectangle.  Both truncation errors and the
half-endpoint correction are explicit. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (c alpha beta T : ℝ)
    (hX : 0 < X)
    (hlow : 0 < c - alpha - beta)
    (hlowUpper : c - alpha - beta ≤ 2)
    (hhigh : 1 < c + beta)
    (hT : 0 < T) :
    ‖positivePrefixSum
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
            (c - alpha - beta) +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  apply norm_positivePrefixSum_sub_le_of_starred_sub_le hX
  exact norm_gsA10TwoBlockTailoredStarredSum_sub_perron_le
    hmul hbound P₁ P₂ y X c alpha beta T
      hX hlow hlowUpper hhigh hT

/-- The preceding projection on the exact A.10 source rectangle.  The
Perron line is `1 + 1 / log X`; all line-location hypotheses are discharged
from `alpha,beta ≤ 1 / log y` and the two logarithmic lower bounds. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceWindow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 0 < X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta T : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT : 0 < T) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X T +
        (32 * (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) / T) *
          dirichletPerronCoefficientMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta)
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hlogypos : 0 < Real.log (y : ℝ) := by linarith
  have hetaQuarter : eta ≤ 1 / 4 := by
    dsimp only [eta]
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hcOne : 1 ≤ c := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogXpos).le
  have hcTwo : c ≤ 2 := by
    dsimp only [c, Erdos67.EulerResidue.taoExponent]
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogXpos).2 hlogX
    linarith
  have hab : alpha + beta ≤ 1 / 2 := by
    have ha : alpha ≤ eta := halpha
    have hb : beta ≤ eta := hbeta
    linarith
  have hlow : 0 < c - alpha - beta := by linarith
  have hlowUpper : c - alpha - beta ≤ 2 := by linarith
  have hhigh : 1 < c + beta := by
    have hcStrict : 1 < c := by
      dsimp only [c, Erdos67.EulerResidue.taoExponent]
      linarith [inv_pos.mpr hlogXpos]
    linarith
  exact norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le
    hmul hbound P₁ P₂ y X c alpha beta T hX hlow hlowUpper hhigh hT

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.positivePrefixSum_eq_dirichletPerronStarredSum_add_half
#print axioms Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceWindow
