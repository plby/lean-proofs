import ErdosProblems.Erdos239.External.Erdos67.MRGSA10TailoredPrefixPerron
import ErdosProblems.Erdos239.External.Erdos67.MRPerronProjectionErrorBound

/-!
# The source-height Perron error in GS A.10

The A.10 contour is truncated at `T₀ = (log X)²`.  This file makes that
choice in the exact two-block tailored Perron theorem and normalizes by
`X`.  The near-diagonal mass, absolute coefficient mass, and endpoint
coefficient remain concrete; the only scalar simplification is the uniform
bound

`X ^ (taoExponent X - alpha - beta) ≤ exp 2 * X`.

Thus this module does not replace the two generalized-Mangoldt window
factors by pointwise absolute masses in the contour integral.
-/

open scoped BigOperators
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- On the source rectangle, the power of the Perron base costs only an
absolute factor beyond `X`. -/
theorem rpow_sourcePerronLine_le_exp_two_mul
    {X : ℕ} (hX : 2 ≤ X) {alpha beta : ℝ}
    (halpha : 0 ≤ alpha) (hbeta : 0 ≤ beta) :
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
      Real.exp 2 * X := by
  have hXpos : 0 < X := by omega
  have hXR : (0 : ℝ) < X := by exact_mod_cast hXpos
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hmono :
      (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
        (X : ℝ) ^ Erdos67.EulerResidue.taoExponent X := by
    apply Real.rpow_le_rpow_of_exponent_le hXone
    linarith
  have hsmall :
      (X : ℝ) ^ (Erdos67.EulerResidue.taoExponent X - 1) ≤
        Real.exp 2 :=
    Erdos67.MRPerronProjectionErrorBound.rpow_taoExponent_sub_one_le_exp_two
      hXpos (by omega) hX
  calc
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) ≤
        (X : ℝ) ^ Erdos67.EulerResidue.taoExponent X := hmono
    _ = (X : ℝ) ^
          ((Erdos67.EulerResidue.taoExponent X - 1) + 1) := by
      congr 1
      ring
    _ = (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - 1) * X := by
      rw [Real.rpow_add hXR, Real.rpow_one]
    _ ≤ Real.exp 2 * X :=
      mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg X)

/-- The exact pointwise Perron projection error after choosing the source
height `T₀ = (log X)²`.  All coefficient-dependent quantities remain
visible, while the Perron power is replaced by an absolute multiple of
`X`. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X (Erdos67.EulerResidue.taoExponent X) alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2) +
        (32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2) *
          dirichletPerronCoefficientMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta)
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  let a : ArithmeticFunction ℂ :=
    gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta
  let T : ℝ := (Real.log (X : ℝ)) ^ 2
  let sigma : ℝ :=
    Erdos67.EulerResidue.taoExponent X - alpha - beta
  have hXpos : 0 < X := by omega
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hT : 0 < T := by dsimp only [T]; positivity
  have hmass : 0 ≤ dirichletPerronCoefficientMass a sigma := by
    unfold dirichletPerronCoefficientMass
    exact tsum_nonneg fun _ ↦ norm_nonneg _
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma]
    exact rpow_sourcePerronLine_le_exp_two_mul hX halpha0 hbeta0
  have hfactor :
      32 * (X : ℝ) ^ sigma / T ≤
        32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2 := by
    dsimp only [T]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hlogXpos)).2
    have hnum := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 32 by norm_num)
    simpa only [mul_assoc] using hnum
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceWindow
      hmul hbound P₁ P₂ (hX := hXpos) hlogX hlogy
      halpha0 halpha hbeta0 hbeta (T := T) hT
  have htail := hbase.trans <| add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactor hmass)) le_rfl
  simpa only [a, T, sigma, pow_two] using htail

/-- Normalized source-height Perron error.  This is the form used after the
two auxiliary `alpha,beta` integrations: the coefficient mass has the
source factor `1 / log(X)^2`, and the other two exact errors are divided by
`X`. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_div_le_sourceHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
          (gsA9HighArithmetic f y)
          (gsA9HighGeneralizedMangoldt hmul y)
          y X (Erdos67.EulerResidue.taoExponent X) alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ / X ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2) / X +
        (32 * Real.exp 2 / (Real.log (X : ℝ)) ^ 2) *
          dirichletPerronCoefficientMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta)
            (Erdos67.EulerResidue.taoExponent X - alpha - beta) +
        ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ / (2 * X) := by
  have hXpos : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceHeight
      hmul hbound P₁ P₂ hX hlogX hlogy
      halpha0 halpha hbeta0 hbeta
  have hdiv := div_le_div_of_nonneg_right hbase hXpos.le
  apply hdiv.trans_eq
  field_simp [ne_of_gt hXpos]

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.rpow_sourcePerronLine_le_exp_two_mul
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceHeight
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_div_le_sourceHeight
