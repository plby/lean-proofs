import ErdosProblems.Erdos239.External.Erdos67.MRGSA10LambdaWindowMass

/-!
# Scalar source-line bound for the A.10 Mangoldt windows

The joint absolute-mass estimate for the two finite generalized-Mangoldt
windows contains the exponent

`1 - min (taoExponent X - beta) 1`.

On the source rectangle this is at most `beta`, and hence at most
`1 / log y`.  This file records that scalar simplification, including the
small-prime-deleted specialization used in the A.10 contour.
-/

open scoped BigOperators
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The residual power in the joint source-line window mass is bounded by
the width of the source rectangle. -/
theorem one_sub_min_taoExponent_sub_le_inv_log
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1 ≤
      (Real.log (y : ℝ))⁻¹ := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hmin : 1 - beta ≤
      min (Erdos67.EulerResidue.taoExponent X - beta) 1 := by
    apply le_min
    · linarith
    · linarith
  linarith

/-- Joint source-line mass with the remaining power replaced by the
uniform rectangle-width cost `X^(1/log y)`. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le_rpow_inv_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (Real.log (y : ℝ))⁻¹ := by
  dsimp only
  have hbase :=
    mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le
      hmul hcomp hbound hX hlogy hbeta0 hbeta
  have hexp := one_sub_min_taoExponent_sub_le_inv_log
    hX hlogy hbeta0 hbeta
  have hXone : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hpow :
      (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - beta) 1) ≤
        (X : ℝ) ^ (Real.log (y : ℝ))⁻¹ :=
    Real.rpow_le_rpow_of_exponent_le hXone hexp
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))

/-- Source-deleted specialization of the scalar joint window-mass bound. -/
theorem mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_sourceLines_le_rpow_inv_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let c := Erdos67.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    dirichletPerronCoefficientMass W (c - beta) *
        dirichletPerronCoefficientMass W (c + beta) ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (Real.log (y : ℝ))⁻¹ := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hcompG : IsCompletelyMultiplicativeOnPositive g :=
    gsDeletePrimeBand_isCompletelyMultiplicativeOnPositive hcomp gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  simpa only [g, hmulG] using
    (mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le_rpow_inv_log
      hmulG hcompG hboundG hX hlogy hbeta0 hbeta)

/-- Product bound for two arbitrary Perron lines, provided the first is in
`[0,1]` and the second is to the right of `1`.  This is the form needed when
the A.10 contour line itself depends on the rectangle variable. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_lines_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    {sigma tau : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (htau : 1 ≤ tau) :
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W sigma *
        dirichletPerronCoefficientMass W tau ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (1 - sigma) := by
  dsimp only
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let B : ℝ := 2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)
  have hlow := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX hsigma0 hsigma1
  have hone := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 1)
  have hhigh : dirichletPerronCoefficientMass W tau ≤ B := by
    refine (dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      (gsA9HighGeneralizedMangoldt hmul y) y X htau).trans ?_
    simpa only [W, B, sub_self, Real.rpow_zero, mul_one] using hone
  have hmass0 : 0 ≤ dirichletPerronCoefficientMass W tau := by
    unfold dirichletPerronCoefficientMass
    positivity
  have hpow0 : 0 ≤ (X : ℝ) ^ (1 - sigma) :=
    Real.rpow_nonneg (by positivity) _
  have hB0 : 0 ≤ B := by
    dsimp only [B]
    positivity
  calc
    dirichletPerronCoefficientMass W sigma *
        dirichletPerronCoefficientMass W tau ≤
      (B * (X : ℝ) ^ (1 - sigma)) * B :=
        mul_le_mul hlow hhigh hmass0 (mul_nonneg hB0 hpow0)
    _ = B ^ 2 * (X : ℝ) ^ (1 - sigma) := by ring

/-- Source-deleted arbitrary-line form with the widened `3 / log y` cost
forced by the beta-dependent A.10 Perron line. -/
theorem mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_lines_le_rpow_three_inv_log
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    {sigma tau : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1)
    (hsigma : 1 - 3 * (Real.log (y : ℝ))⁻¹ ≤ sigma)
    (htau : 1 ≤ tau) :
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmulG y) y X
    dirichletPerronCoefficientMass W sigma *
        dirichletPerronCoefficientMass W tau ≤
      (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
        (X : ℝ) ^ (3 * (Real.log (y : ℝ))⁻¹) := by
  dsimp only
  let g : ℕ → ℂ := gsDeletePrimeBand f gsA9SmallPrime
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hcompG : IsCompletelyMultiplicativeOnPositive g :=
    gsDeletePrimeBand_isCompletelyMultiplicativeOnPositive hcomp gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hbase :=
    mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_lines_le
      hmulG hcompG hboundG (y := y) (X := X) hX
        hsigma0 hsigma1 htau
  have hexp : 1 - sigma ≤ 3 * (Real.log (y : ℝ))⁻¹ := by
    linarith
  have hXone : (1 : ℝ) ≤ X := by
    exact_mod_cast (show 1 ≤ X by omega)
  have hpow : (X : ℝ) ^ (1 - sigma) ≤
      (X : ℝ) ^ (3 * (Real.log (y : ℝ))⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexp
  exact hbase.trans (mul_le_mul_of_nonneg_left hpow (sq_nonneg _))

end

end Erdos67.MRHalaszBands

#print axioms Erdos67.MRHalaszBands.one_sub_min_taoExponent_sub_le_inv_log
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_sourceLines_le_rpow_inv_log
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_sourceLines_le_rpow_inv_log
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_lines_le
#print axioms
  Erdos67.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10SourceDeleted_lines_le_rpow_three_inv_log
