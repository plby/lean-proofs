import ErdosProblems.Erdos67b.MRGSA9A10Window
import ErdosProblems.Erdos67b.MRGSA10TailoredPrefixPerron

/-!
# The A.9 source window inside the tailored A.10 Perron line

This file identifies, pointwise in all three contour variables, the exact
A.9 product occurring in the four-factor tailored Perron series.  The two
finite generalized-Mangoldt factors are bounded by their explicit Perron
coefficient masses.  No supremum, prefix estimate, or desired contour bound
is assumed.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- On a vertical line, an absolutely convergent Dirichlet series is
bounded by its real-line coefficient mass. -/
theorem norm_LSeries_le_dirichletPerronCoefficientMass
    {a : ℕ → ℂ} {sigma t : ℝ}
    (hsum : LSeriesSummable a ((sigma : ℂ) + t * I)) :
    ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤
      dirichletPerronCoefficientMass a sigma := by
  calc
    ‖LSeries a ((sigma : ℂ) + t * I)‖ ≤
        ∑' n : ℕ, ‖LSeries.term a ((sigma : ℂ) + t * I) n‖ :=
      norm_tsum_le_tsum_norm hsum.norm
    _ = dirichletPerronCoefficientMass a sigma := by
      unfold dirichletPerronCoefficientMass
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp

/-- The finite A.10 generalized-Mangoldt window is bounded on every vertical
line by its absolute coefficient mass. -/
theorem norm_LSeries_gsA10LambdaWindow_le_coefficientMass
    (lambda : ArithmeticFunction ℂ) (y X : ℕ) (sigma t : ℝ) :
    ‖LSeries (gsA10LambdaWindow lambda y X)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      dirichletPerronCoefficientMass
        (gsA10LambdaWindow lambda y X) sigma := by
  rw [mul_comm Complex.I (t : ℂ)]
  exact norm_LSeries_le_dirichletPerronCoefficientMass
    (sigma := sigma) (t := t)
    (gsA10LambdaWindow_LSeriesSummable lambda y X _)

/-- The fixed small-prime deletion used on the A.10 source contour. -/
def gsA10SourceDeleted (f : ℕ → ℂ) : ℕ → ℂ :=
  gsDeletePrimeBand f gsA9SmallPrime

/-- The exact tailored coefficient after the fixed small-prime deletion. -/
def gsA10SourceTailoredCoefficient
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) : ArithmeticFunction ℂ :=
  gsA10TwoBlockTailoredCoefficient
    (gsA10SourceDeleted f)
    (gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime)
    P₁ P₂ y X alpha beta

/-- The joined alternating-low/high A.9 factor on the shifted source line. -/
def gsA10SourceWindowCoreBudget
    (f : ℕ → ℂ) (y X : ℕ) (beta t : ℝ) : ℝ :=
  let g := gsA10SourceDeleted f
  let c₀ := Erdos67b.EulerResidue.taoExponent X
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  Real.exp
      (28 * Real.exp 4 *
          Erdos67b.EulerQuantitative.primeQuadraticConstant +
        36 * gsA9SourceShiftConstant) *
    Real.sqrt ‖LSeries g sHigh‖ *
    Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖

/-- The exact pointwise majorant left by the lossless A.9 product, retaining
the two finite generalized-Mangoldt Dirichlet-series norms. -/
def gsA10SourceWindowVerticalBudget
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta t : ℝ) : ℝ :=
  let g := gsA10SourceDeleted f
  let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
    hmul gsA9SmallPrime
  let c₀ := Erdos67b.EulerResidue.taoExponent X
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  gsA10SourceWindowCoreBudget f y X beta t *
  ‖LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ *
  ‖LSeries W sHigh‖

/-- The absolute coefficient-mass envelope for the exact vertical budget. -/
def gsA10SourceWindowMassBudget
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta t : ℝ) : ℝ :=
  let g := gsA10SourceDeleted f
  let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
    hmul gsA9SmallPrime
  let c₀ := Erdos67b.EulerResidue.taoExponent X
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  gsA10SourceWindowCoreBudget f y X beta t *
  dirichletPerronCoefficientMass W (c₀ - beta) *
  dirichletPerronCoefficientMass W (c₀ + beta)

/-- The lossless A.9 estimate for the joined alternating-low and high pair,
before the two finite Mangoldt windows are inserted. -/
theorem norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_sourceWindow
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ := ((c₀ - alpha - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh‖ ≤
      Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let Q₂ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ P₂ p
  let Q₃ : ℕ → Prop := fun p ↦ ¬ P₁ p ∧ ¬ P₂ p
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hdisj : ∀ p ∈ primesUpTo y, Q₂ p → Q₃ p → False := by
    intro p hp h2 h3
    exact h3.2 h2.2
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by
      linarith
    linarith
  have hsigmaPos : 0 < sigmaLow := lt_of_lt_of_le (by norm_num) hsigmaHalf
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
    norm_twoBlock_alternatingLow_deleteSmallPrimes_mul_high_le_A10Window
      hmul hbound Q₂ Q₃ hy hdisj hX hlogy
        halpha0 halpha hbeta0 hbeta (t := t)
  rw [hlowEq, LSeries_gsA9HighArithmetic]
  simpa only [g, gsA10SourceDeleted, c₀, sigmaLow, sLow, sHigh, Q₂, Q₃]
    using hmain

/-- Exact four-factor expansion on the A.10 source window, with all
summability checks internal. -/
theorem LSeries_gsA10SourceTailoredCoefficient_eq_fourFactors
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ := ((c₀ - alpha - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) sLow =
      (LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
        LSeries (gsA9HighArithmetic g y) sHigh) *
      (LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)) *
        LSeries W sHigh) := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hetaQuarter : (Real.log (y : ℝ))⁻¹ ≤ 1 / 4 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 4) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hsigmaHalf : 1 / 2 ≤ sigmaLow := by
    dsimp only [sigmaLow]
    have hab : alpha + beta ≤ 2 * (Real.log (y : ℝ))⁻¹ := by
      linarith
    linarith
  have hsigmaPos : 0 < sigmaLow := lt_of_lt_of_le (by norm_num) hsigmaHalf
  have hhigh : 1 < c₀ + beta := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast hX)
    have hi : 0 < (Real.log (X : ℝ))⁻¹ := inv_pos.mpr hlogX
    linarith
  have hseries := LSeries_gsA10TailoredCoefficient
    (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
    (gsA9HighArithmetic g y)
    (gsA9HighGeneralizedMangoldt hmulG y)
    y X alpha beta sLow
    (gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmulG hboundG P₁ P₂ y (by simpa [sLow] using hsigmaPos))
    (gsA9HighArithmetic_LSeriesSummable hboundG y (by
      simp only [sLow, sigmaLow, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        zero_mul, one_mul, sub_zero, add_zero]
      linarith))
  have hsLowAlpha : sLow + (alpha : ℂ) =
      ((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ) := by
    simp only [sLow, sigmaLow]
    push_cast
    ring
  have hsLowAlphaBeta : sLow + ((alpha + 2 * beta : ℝ) : ℂ) =
      sHigh := by
    simp only [sLow, sigmaLow, sHigh]
    push_cast
    ring
  change LSeries
      (gsA10TailoredCoefficient
        (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
        (gsA9HighArithmetic g y)
        (gsA9HighGeneralizedMangoldt hmulG y)
        y X alpha beta) sLow = _
  rw [hseries, hsLowAlpha, hsLowAlphaBeta]
  rfl

/-- A small norm bookkeeping lemma used after the exact four-factor
Dirichlet-series expansion. -/
theorem norm_mul_pair_le_mul_three
    {z₁₂ z₃ z₄ : ℂ} {B₁₂ B₃ B₄ : ℝ}
    (h₁₂ : ‖z₁₂‖ ≤ B₁₂) (h₃ : ‖z₃‖ ≤ B₃) (h₄ : ‖z₄‖ ≤ B₄)
    (hB₁₂ : 0 ≤ B₁₂) (hB₃ : 0 ≤ B₃) :
    ‖z₁₂ * (z₃ * z₄)‖ ≤ B₁₂ * B₃ * B₄ := by
  rw [norm_mul, norm_mul]
  calc
    ‖z₁₂‖ * (‖z₃‖ * ‖z₄‖) ≤
        B₁₂ * (‖z₃‖ * ‖z₄‖) :=
      mul_le_mul_of_nonneg_right h₁₂ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ B₁₂ * (B₃ * ‖z₄‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right h₃ (norm_nonneg _)) hB₁₂
    _ ≤ B₁₂ * (B₃ * B₄) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h₄ hB₃) hB₁₂
    _ = B₁₂ * B₃ * B₄ := by ring

/-- Monotonicity of a product of three nonnegative real factors. -/
theorem mul_three_le_mul_three
    {a b c A B C : ℝ}
    (ha : a ≤ A) (hb : b ≤ B) (hc : c ≤ C)
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) :
    a * b * c ≤ A * B * C := by
  calc
    a * b * c ≤ A * b * c := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ha hb0) hc0
    _ ≤ A * B * c := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb hA0) hc0
    _ ≤ A * B * C := by
      exact mul_le_mul_of_nonneg_left hc (mul_nonneg hA0 hB0)

/-- The exact four-factor identity and lossless A.9 estimate, retaining the
norms of the two finite Mangoldt windows. -/
theorem norm_LSeries_gsA10SourceTailored_le_A9_mul_windowNorms
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ := ((c₀ - alpha - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    ‖LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) sLow‖ ≤
      (Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖) *
      ‖LSeries W (((c₀ - beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ *
      ‖LSeries W sHigh‖ := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sLow : ℂ := ((c₀ - alpha - beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := ((c₀ + beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
  have hseries := LSeries_gsA10SourceTailoredCoefficient_eq_fourFactors
    hmul hbound P₁ P₂ hX hlogy halpha hbeta0 hbeta (t := t)
  have hmain :
      ‖LSeries (gsA10TwoBlockAlternatingLow g P₁ P₂ y) sLow *
          LSeries (gsA9HighArithmetic g y) sHigh‖ ≤
        Real.exp
            (28 * Real.exp 4 *
                Erdos67b.EulerQuantitative.primeQuadraticConstant +
              36 * gsA9SourceShiftConstant) *
          Real.sqrt ‖LSeries g sHigh‖ *
          Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ := by
    simpa only [g, c₀, sLow, sHigh] using
      norm_LSeries_gsA10TwoBlockAlternatingLow_mul_high_le_sourceWindow
        hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta (t := t)
  have hA9nonneg :
      0 ≤ Real.exp
          (28 * Real.exp 4 *
              Erdos67b.EulerQuantitative.primeQuadraticConstant +
            36 * gsA9SourceShiftConstant) *
        Real.sqrt ‖LSeries g sHigh‖ *
        Real.sqrt ‖riemannZeta ((c₀ + beta : ℝ) : ℂ)‖ := by positivity
  rw [hseries]
  exact norm_mul_pair_le_mul_three hmain le_rfl le_rfl
    hA9nonneg (norm_nonneg _)

/-- Pointwise four-factor A.10 bound on the source rectangle.  The first
two factors stay joined and receive the lossless A.13--A.14 estimate. -/
theorem norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_A10Window
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta)
        (((Erdos67b.EulerResidue.taoExponent X - alpha - beta : ℝ) : ℂ) +
          Complex.I * (t : ℂ))‖ ≤
      gsA10SourceWindowVerticalBudget f hmul y X beta t := by
  simpa only [gsA10SourceWindowVerticalBudget, gsA10SourceWindowCoreBudget]
    using
    norm_LSeries_gsA10SourceTailored_le_A9_mul_windowNorms
      hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta (t := t)

/-- The exact vertical A.10 budget is bounded by its two explicit finite
coefficient masses. -/
theorem gsA10SourceWindowVerticalBudget_le_massBudget
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (y X : ℕ) (beta t : ℝ) :
    gsA10SourceWindowVerticalBudget f hmul y X beta t ≤
      gsA10SourceWindowMassBudget f hmul y X beta t := by
  unfold gsA10SourceWindowVerticalBudget gsA10SourceWindowMassBudget
  dsimp only
  apply mul_three_le_mul_three le_rfl
  · exact norm_LSeries_gsA10LambdaWindow_le_coefficientMass _ _ _ _ _
  · exact norm_LSeries_gsA10LambdaWindow_le_coefficientMass _ _ _ _ _
  · unfold gsA10SourceWindowCoreBudget
    positivity
  · exact norm_nonneg _
  · exact norm_nonneg _
  · unfold gsA10SourceWindowCoreBudget
    positivity
  · unfold dirichletPerronCoefficientMass
    positivity

/-- Fully explicit coefficient-mass version of the pointwise four-factor
A.10 source-window estimate. -/
theorem norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_A10WindowMass
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 1 < X)
    {alpha beta t : ℝ} (hlogy : 4 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖LSeries (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta)
        (((Erdos67b.EulerResidue.taoExponent X - alpha - beta : ℝ) : ℂ) +
          Complex.I * (t : ℂ))‖ ≤
      gsA10SourceWindowMassBudget f hmul y X beta t := by
  exact (norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_A10Window
    hmul hbound P₁ P₂ hy hX hlogy halpha0 halpha hbeta0 hbeta (t := t)).trans
      (gsA10SourceWindowVerticalBudget_le_massBudget hmul y X beta t)

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_A10Window
