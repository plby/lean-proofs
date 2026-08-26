import ErdosProblems.Erdos67b.MRGSA9SourceHalaszPointWide
import ErdosProblems.Erdos67b.MRGSA10TailoredPerronWindow

/-!
# Fixing the A.10 high factor by moving the Perron line

The norm of a complex Dirichlet series is not monotone when its real part
is increased, so the beta-shifted high charge cannot be deduced from its
value at beta zero.  The source-correct contour instead chooses the Perron
parameter `c beta = taoExponent X - beta`.  Then the high factor is exactly
at the Halasz point, while the finite low factor is evaluated at
`taoExponent X - alpha - 2 * beta`.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

/-- Pointwise A.9 control on the beta-dependent Perron line.  There is no
beta-shifted full L-series on the right-hand side. -/
theorem norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_fixedHalasz
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (ht : |t| ≤ X) :
    let g := gsA10SourceDeleted f
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ :=
      ((c₀ - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (c₀ : ℂ) + Complex.I * (t : ℂ)
    ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh‖ ≤
      gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
        Real.exp
          ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
            3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2) := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - 2 * beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (c₀ : ℂ) + Complex.I * (t : ℂ)
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False := by
    intro p hp h2 h3
    exact h3.2 h2.2
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hab : alpha + 2 * beta ≤
      3 * (Real.log (y : ℝ))⁻¹ := by linarith
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaPos : 0 < sigmaLow :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hsigmaWide : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow := by
    dsimp only [sigmaLow]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hle : sigmaLow ≤ c₀ := by
    dsimp only [sigmaLow]
    linarith
  have hgap : c₀ - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    dsimp only [sigmaLow]
    rw [show 3 / Real.log (y : ℝ) =
      3 * (Real.log (y : ℝ))⁻¹ by field_simp]
    linarith
  have hlowEq :
      LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow =
        LSeries (gsA9Low g y) sLow -
          LSeries (gsA9LowDeletion g Q₂ y) sLow -
          LSeries (gsA9LowDeletion g Q₃ y) sLow +
          LSeries (gsA9LowDeletion g (fun p ↦ Q₂ p ∨ Q₃ p) y) sLow := by
    simpa only [Q₂, Q₃] using
      LSeries_gsA10TwoBlockAlternatingLow_of_pos_re
        hmulG hboundG P₁ P₂ y (by simpa [sLow] using hsigmaPos)
  have hmain :=
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_wideHalaszPoint
      hmul hbound Q₂ Q₃ hy hdisj hX hnonpret hle hsigmaWide hgap ht
      (hhalf := hsigmaHalf)
  rw [hlowEq, LSeries_gsA9HighArithmetic]
  simpa only [g, gsA10SourceDeleted, c₀, sigmaLow, sLow, sHigh, Q₂, Q₃,
    Erdos67b.MRHalaszEuler.halaszPoint] using hmain

/-- Exact four-factor identity on the beta-dependent Perron line.  The high
factor and the upper Mangoldt window are on the fixed Halasz line; the
lower Mangoldt window is at `c₀ - 2 beta`. -/
theorem LSeries_gsA10SourceTailoredCoefficient_eq_fourFactors_fixedHalasz
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ :=
      ((c₀ - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := (c₀ : ℂ) + Complex.I * (t : ℂ)
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) sLow =
      (LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh) *
      (LSeries W
          (((c₀ - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries W sHigh) := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - 2 * beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (c₀ : ℂ) + Complex.I * (t : ℂ)
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hsigmaPos : 0 < sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hhigh : 1 < (sLow + ((alpha + 2 * beta : ℝ) : ℂ)).re := by
    have heq : (sLow + ((alpha + 2 * beta : ℝ) : ℂ)).re = c₀ := by
      simp only [sLow, sigmaLow, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, one_mul, sub_zero]
      ring
    rw [heq]
    exact Erdos67b.EulerResidue.one_lt_taoExponent hX
  have hfour := LSeries_gsA10TailoredCoefficient
    (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
    (gsA9HighArithmetic g y)
    (gsA9HighGeneralizedMangoldt hmulG y)
    y X alpha beta sLow
    (gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmulG hboundG P₁ P₂ y (by simpa [sLow] using hsigmaPos))
    (gsA9HighArithmetic_LSeriesSummable hboundG y hhigh)
  have hHighEq : sLow + ((alpha + 2 * beta : ℝ) : ℂ) = sHigh := by
    apply Complex.ext <;>
      simp only [sLow, sHigh, sigmaLow, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, zero_add,
        add_zero] <;> ring
  have hWindowLowEq : sLow + (alpha : ℂ) =
      (((c₀ - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) := by
    apply Complex.ext <;>
      simp only [sLow, sigmaLow, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im, zero_mul, one_mul, sub_zero, zero_add,
        add_zero] <;> ring
  rw [hHighEq, hWindowLowEq] at hfour
  simpa only [g, hmulG, c₀, sigmaLow, sLow, sHigh, W,
    gsA10SourceTailoredCoefficient, gsA10TwoBlockTailoredCoefficient,
    gsA10SourceDeleted] using hfour

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_fixedHalasz
#print axioms
  Erdos67b.MRHalaszBands.LSeries_gsA10SourceTailoredCoefficient_eq_fourFactors_fixedHalasz
