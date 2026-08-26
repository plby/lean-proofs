import ErdosProblems.Erdos67b.MRGSA9SmallPrimeRestore
import ErdosProblems.Erdos67b.MRGSA10LambdaWindowMass

/-!
# The undeleted A.10 contour on the beta-dependent Perron line
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- Scalar mass of the two generalized-Mangoldt windows when their lines
are `c₀ - 2 beta` and `c₀`. -/
def gsA10MovingLambdaMassScalar (y X : ℕ) : ℝ :=
  (2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)) ^ 2 *
    (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹)

/-- Complete pointwise scalar for the undeleted four-factor contour. -/
def gsA10MovingVerticalScalar (y A X : ℕ) : ℝ :=
  gsA9SmallPrimeEulerBound *
    (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
      Real.exp
        ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
          3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) *
    gsA10MovingLambdaMassScalar y X

private theorem norm_LSeries_gsA10LambdaWindow_le_movingMass
    (lambda : ArithmeticFunction ℂ) (y X : ℕ) (sigma t : ℝ) :
    ‖LSeries (gsA10LambdaWindow lambda y X)
        ((sigma : ℂ) + Complex.I * (t : ℂ))‖ ≤
      dirichletPerronCoefficientMass
        (gsA10LambdaWindow lambda y X) sigma := by
  rw [mul_comm Complex.I (t : ℂ)]
  calc
    ‖LSeries (gsA10LambdaWindow lambda y X)
        ((sigma : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        ∑' n : ℕ, ‖LSeries.term (gsA10LambdaWindow lambda y X)
          ((sigma : ℂ) + (t : ℂ) * Complex.I) n‖ :=
      norm_tsum_le_tsum_norm
        (gsA10LambdaWindow_LSeriesSummable lambda y X _).norm
    _ = dirichletPerronCoefficientMass
        (gsA10LambdaWindow lambda y X) sigma := by
      unfold dirichletPerronCoefficientMass
      apply tsum_congr
      intro n
      rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
      simp

/-- The two window masses on the moving contour have a uniform scalar
bound. -/
theorem mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_moving_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {beta : ℝ} (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let W := gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
    dirichletPerronCoefficientMass W (c₀ - 2 * beta) *
        dirichletPerronCoefficientMass W c₀ ≤
      gsA10MovingLambdaMassScalar y X := by
  dsimp only
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let rho : ℝ := min (c₀ - 2 * beta) 1
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  let B : ℝ := 2 * (Real.log 4 + 4) * (Nat.log 2 X : ℝ)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hlineLow : 0 ≤ c₀ - 2 * beta := by linarith
  have hrho0 : 0 ≤ rho := le_min hlineLow (by norm_num)
  have hrhoOne : rho ≤ 1 := min_le_right _ _
  have hrhoLine : rho ≤ c₀ - 2 * beta := min_le_left _ _
  have hlowBase := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX hrho0 hrhoOne
  have hhighBase := dirichletPerronCoefficientMass_gsA10LambdaWindow_le
    hmul hcomp hbound (y := y) (X := X) hX
      (show (0 : ℝ) ≤ 1 by norm_num) (le_refl 1)
  have hlow : dirichletPerronCoefficientMass W (c₀ - 2 * beta) ≤
      B * (X : ℝ) ^ (1 - rho) :=
    (dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      (gsA9HighGeneralizedMangoldt hmul y) y X hrhoLine).trans
      (by simpa only [W, B] using hlowBase)
  have hhigh : dirichletPerronCoefficientMass W c₀ ≤ B := by
    have hanti := dirichletPerronCoefficientMass_gsA10LambdaWindow_anti
      (gsA9HighGeneralizedMangoldt hmul y) y X hcOne
    exact hanti.trans (by
      simpa only [W, B, sub_self, Real.rpow_zero, mul_one] using hhighBase)
  have hexponent : 1 - rho ≤ 2 * (Real.log (y : ℝ))⁻¹ := by
    have hmin : 1 - 2 * beta ≤ rho := by
      apply le_min
      · linarith
      · linarith
    linarith
  have hXone : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpow : (X : ℝ) ^ (1 - rho) ≤
      (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hXone hexponent
  have hB0 : 0 ≤ B := by dsimp only [B]; positivity
  have hmassHigh0 : 0 ≤ dirichletPerronCoefficientMass W c₀ := by
    unfold dirichletPerronCoefficientMass
    positivity
  calc
    dirichletPerronCoefficientMass W (c₀ - 2 * beta) *
        dirichletPerronCoefficientMass W c₀ ≤
      (B * (X : ℝ) ^ (1 - rho)) * B := by
        exact mul_le_mul hlow hhigh hmassHigh0
          (mul_nonneg hB0 (Real.rpow_nonneg (by positivity) _))
    _ = B ^ 2 * (X : ℝ) ^ (1 - rho) := by ring
    _ ≤ B ^ 2 * (X : ℝ) ^ (2 * (Real.log (y : ℝ))⁻¹) := by
      gcongr
    _ = gsA10MovingLambdaMassScalar y X := rfl

/-- Uniform pointwise norm bound for the exact undeleted tailored
coefficient on the beta-dependent line. -/
theorem norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    (hlarge₂ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ P₂ p) → 23 ≤ p)
    (hlarge₃ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ ¬ P₂ p) → 23 ≤ p)
    {alpha beta t : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (ht : |t| ≤ X) :
    let c₀ := Erdos67b.EulerResidue.taoExponent X
    let sLow : ℂ :=
      ((c₀ - alpha - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ)
    ‖LSeries (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) sLow‖ ≤
      gsA10MovingVerticalScalar y A X := by
  dsimp only
  let c₀ : ℝ := Erdos67b.EulerResidue.taoExponent X
  let sigmaLow : ℝ := c₀ - alpha - 2 * beta
  let sLow : ℂ := (sigmaLow : ℂ) + Complex.I * (t : ℂ)
  let sHigh : ℂ := (c₀ : ℂ) + Complex.I * (t : ℂ)
  let W : ArithmeticFunction ℂ :=
    gsA10LambdaWindow (gsA9HighGeneralizedMangoldt hmul y) y X
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67b.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
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
    exact Erdos67b.EulerResidue.one_lt_taoExponent (show 1 < X by omega)
  have hfour := LSeries_gsA10TailoredCoefficient
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y)
    y X alpha beta sLow
    (gsA10TwoBlockAlternatingLow_LSeriesSummable_of_pos_re
      hmul hbound P₁ P₂ y (by simpa [sLow] using hsigmaPos))
    (gsA9HighArithmetic_LSeriesSummable hbound y hhigh)
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
  have hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p := by
    intro p hp
    by_contra hp₁
    have hpData := Finset.mem_filter.mp hp
    have hp23 : p < 23 := Finset.mem_range.mp hpData.1
    have hpPrime : Nat.Prime p := hpData.2
    have hpY : p ∈ primesUpTo y := by
      exact mem_primesUpTo.mpr ⟨hpPrime,
        Nat.le_of_lt (hp23.trans_le hy)⟩
    by_cases hp₂ : P₂ p
    · have hpLarge := hlarge₂ p hpY ⟨hp₁, hp₂⟩
      omega
    · have hpLarge := hlarge₃ p hpY ⟨hp₁, hp₂⟩
      omega
  have hhalf : (1 : ℝ) / 2 ≤ sigmaLow := by
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hle : sigmaLow ≤ c₀ := by
    dsimp only [sigmaLow]
    linarith
  have hsigmaLow : 1 - 3 / Real.log (y : ℝ) ≤ sigmaLow := by
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    have hdiv : 3 / Real.log (y : ℝ) =
        3 * (Real.log (y : ℝ))⁻¹ := by
      rw [div_eq_mul_inv]
    rw [hdiv]
    dsimp only [sigmaLow]
    linarith
  have hgap : c₀ - sigmaLow ≤ 3 / Real.log (y : ℝ) := by
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    dsimp only [sigmaLow]
    rw [div_eq_mul_inv]
    linarith
  have hcore :=
    norm_twoBlock_alternatingLow_mul_high_le_wideHalaszPoint
      hmul hbound P₁ P₂ hy hsmallOutside (show 1 < X by omega)
      hnonpret hhalf hle hsigmaLow hgap ht
  have hcore' :
      ‖LSeries (gsA10TwoBlockAlternatingLow f P₁ P₂ y) sLow‖ *
          ‖LSeries (gsA9HighArithmetic f y) sHigh‖ ≤
        gsA9SmallPrimeEulerBound *
          (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
            Real.exp
              ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
                3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) := by
    rw [LSeries_gsA9HighArithmetic, ← norm_mul]
    simpa only [c₀, sigmaLow, sLow, sHigh,
      Erdos67b.MRHalaszEuler.halaszPoint] using hcore
  have hWlow := norm_LSeries_gsA10LambdaWindow_le_movingMass
    (gsA9HighGeneralizedMangoldt hmul y) y X (c₀ - 2 * beta) t
  have hWhigh := norm_LSeries_gsA10LambdaWindow_le_movingMass
    (gsA9HighGeneralizedMangoldt hmul y) y X c₀ t
  have hmass := mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_moving_le
    hmul hcomp hbound hX hlogy hbeta0 hbeta
  have hwindow :
      ‖LSeries W
          (((c₀ - 2 * beta : ℝ) : ℂ) + Complex.I * (t : ℂ))‖ *
        ‖LSeries W sHigh‖ ≤ gsA10MovingLambdaMassScalar y X := by
    exact (mul_le_mul hWlow hWhigh (norm_nonneg _)
      (by unfold dirichletPerronCoefficientMass; positivity)).trans
      (by simpa only [W, c₀, sHigh] using hmass)
  change ‖LSeries
      (gsA10TailoredCoefficient
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X alpha beta) sLow‖ ≤
    gsA10MovingVerticalScalar y A X
  rw [hfour, norm_mul, norm_mul, norm_mul]
  unfold gsA10MovingVerticalScalar
  have hcoreScalar0 : 0 ≤
      gsA9SmallPrimeEulerBound *
        (gsA9WideSourceEulerConstant * (1 + Real.log (X : ℝ)) *
          Real.exp
            ((-Real.exp (-1) * ((A / 2 : ℕ) : ℝ) +
              3 * Erdos67b.EulerQuantitative.primeQuadraticConstant) / 2)) :=
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)).trans hcore'
  exact mul_le_mul
    hcore'
    hwindow (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    hcoreScalar0

/-- Nonnegativity of the explicit moving-contour scalar, obtained from its
pointwise majorant rather than by reopening the fixed Euler constants. -/
theorem gsA10MovingVerticalScalar_nonneg
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    (hlarge₂ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ P₂ p) → 23 ≤ p)
    (hlarge₃ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ ¬ P₂ p) → 23 ≤ p)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    0 ≤ gsA10MovingVerticalScalar y A X := by
  have hpoint :=
    norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar
      hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
      hlogy halpha0 halpha hbeta0 hbeta
      (show |(0 : ℝ)| ≤ X by simp)
  exact (norm_nonneg _).trans hpoint

/-- Uniform moving-line bound over a finite vertical interval. -/
theorem norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar_of_abs_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y A X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hnonpret : MRArchimedeanNonpretentious f A X)
    (hlarge₂ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ P₂ p) → 23 ≤ p)
    (hlarge₃ : ∀ p ∈ primesUpTo y,
      (¬ P₁ p ∧ ¬ P₂ p) → 23 ≤ p)
    {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hTX : T ≤ X) :
    ∀ t : ℝ, |t| ≤ T →
      ‖LSeries (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta)
          (((Erdos67b.EulerResidue.taoExponent X - alpha - 2 * beta : ℝ) : ℂ) +
            (t : ℂ) * Complex.I)‖ ≤
        gsA10MovingVerticalScalar y A X := by
  intro t ht
  rw [mul_comm (t : ℂ) Complex.I]
  exact norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar
    hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
    hlogy halpha0 halpha hbeta0 hbeta (ht.trans hTX)

end

end Erdos67b.MRHalaszBands

#print axioms
  Erdos67b.MRHalaszBands.mul_dirichletPerronCoefficientMass_gsA10LambdaWindow_moving_le
#print axioms
  Erdos67b.MRHalaszBands.norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar
#print axioms
  Erdos67b.MRHalaszBands.gsA10MovingVerticalScalar_nonneg
#print axioms
  Erdos67b.MRHalaszBands.norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar_of_abs_le
