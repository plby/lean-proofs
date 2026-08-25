import ErdosProblems.Erdos67.MRGSA10MovingPerronCanonicalBlocks
import ErdosProblems.Erdos67.MRGSA10CoefficientMassSourceScalar
import ErdosProblems.Erdos67.MRGSA10CoefficientMassBaseScalar
import ErdosProblems.Erdos67.MRGSA10PerronMassAverage

/-!
# Projection onto the moving A.10 Perron line

The beta-dependent Perron parameter `c = taoExponent X - beta` keeps the
high Euler factor at the fixed Halasz point.  This file records the exact
prefix projection at height `log(X)^2` and scalarizes only the complete
coefficient-mass term.  The genuinely local near-diagonal mass and the
half-endpoint correction remain explicit.
-/

open scoped BigOperators LSeries.notation
open Complex Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The raw moving-line projection error.  In contrast to the convenient
pointwise envelope below, this keeps the Perron power next to the
coefficient mass so that their beta growth cancels under the source
rectangle average. -/
def gsA10MovingPerronRawProjectionError
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  let a := gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta
  let sigma := Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta
  dirichletPerronNearMass a X ((Real.log (X : ℝ)) ^ 2) +
    (32 * (X : ℝ) ^ sigma / (Real.log (X : ℝ)) ^ 2) *
      dirichletPerronCoefficientMass a sigma +
    (1 / 2 : ℝ) * ‖a X‖

/-- Exact source-height projection on the beta-dependent Perron line,
before any pointwise flattening of its moving power. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_rawError
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      gsA10MovingPerronRawProjectionError
        f hmul P₁ P₂ y X alpha beta := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X - beta
  let sigma : ℝ :=
    Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta
  let T : ℝ := (Real.log (X : ℝ)) ^ 2
  have hXpos : 0 < X := by omega
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    exact le_add_of_nonneg_right (inv_pos.mpr hlogXpos).le
  have hcTwo : Erdos67.EulerResidue.taoExponent X ≤ 2 := by
    unfold Erdos67.EulerResidue.taoExponent
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogXpos).2 hlogX
    linarith
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hline : c - alpha - beta = sigma := by
    dsimp only [c, sigma]
    ring
  have hlow : 0 < c - alpha - beta := by
    rw [hline]
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hlowUpper : c - alpha - beta ≤ 2 := by
    dsimp only [c]
    linarith
  have hhigh : 1 < c + beta := by
    rw [show c + beta = Erdos67.EulerResidue.taoExponent X by
      dsimp only [c]; ring]
    unfold Erdos67.EulerResidue.taoExponent
    linarith [inv_pos.mpr hlogXpos]
  have hT : 0 < T := by dsimp only [T]; positivity
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le
      hmul hbound P₁ P₂ y X c alpha beta T
        hXpos hlow hlowUpper hhigh hT
  rw [hline] at hbase
  simpa only [gsA10TwoBlockMovingPerronIntegral,
    gsA10MovingPerronRawProjectionError, c, sigma, T, pow_two] using hbase

/-- The exact error in projecting a tailored A.10 prefix onto the moving
Perron line. -/
def gsA10MovingPerronProjectionError
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  let a := gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta
  let sigma := Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta
  dirichletPerronNearMass a X ((Real.log (X : ℝ)) ^ 2) +
    (32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2) *
      dirichletPerronCoefficientMass a sigma +
    (1 / 2 : ℝ) * ‖a X‖

/-- The beta-dependent source-height projection, with no analytic bound
assumed for the local near-diagonal mass. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_error
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      gsA10MovingPerronProjectionError
        f hmul P₁ P₂ y X alpha beta := by
  let c : ℝ := Erdos67.EulerResidue.taoExponent X - beta
  let sigma : ℝ :=
    Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta
  let T : ℝ := (Real.log (X : ℝ)) ^ 2
  let a : ArithmeticFunction ℂ :=
    gsA10TwoBlockTailoredCoefficient f hmul P₁ P₂ y X alpha beta
  have hXpos : 0 < X := by omega
  have hlogXpos : 0 < Real.log (X : ℝ) := zero_lt_one.trans_le hlogX
  have hlogypos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    exact le_add_of_nonneg_right (inv_pos.mpr hlogXpos).le
  have hcTwo : Erdos67.EulerResidue.taoExponent X ≤ 2 := by
    unfold Erdos67.EulerResidue.taoExponent
    have hinv : (Real.log (X : ℝ))⁻¹ ≤ 1 :=
      (inv_le_one₀ hlogXpos).2 hlogX
    linarith
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hlow : 0 < c - alpha - beta := by
    rw [show c - alpha - beta = sigma by dsimp only [c, sigma]; ring]
    exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hlowUpper : c - alpha - beta ≤ 2 := by
    dsimp only [c]
    linarith
  have hhigh : 1 < c + beta := by
    rw [show c + beta = Erdos67.EulerResidue.taoExponent X by
      dsimp only [c]; ring]
    unfold Erdos67.EulerResidue.taoExponent
    linarith [inv_pos.mpr hlogXpos]
  have hT : 0 < T := by dsimp only [T]; positivity
  have hmass : 0 ≤ dirichletPerronCoefficientMass a sigma := by
    unfold dirichletPerronCoefficientMass
    exact tsum_nonneg fun _ ↦ norm_nonneg _
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma]
    simpa only [sub_sub] using
      (rpow_sourcePerronLine_le_exp_two_mul hX halpha0
        (mul_nonneg (by norm_num) hbeta0 : 0 ≤ 2 * beta))
  have hfactor :
      32 * (X : ℝ) ^ sigma / T ≤
        32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2 := by
    dsimp only [T]
    apply (div_le_div_iff_of_pos_right (sq_pos_of_pos hlogXpos)).2
    have hnum := mul_le_mul_of_nonneg_left hpow
      (show (0 : ℝ) ≤ 32 by norm_num)
    simpa only [mul_assoc] using hnum
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le
      hmul hbound P₁ P₂ y X c alpha beta T
        hXpos hlow hlowUpper hhigh hT
  have hline : c - alpha - beta = sigma := by
    dsimp only [c, sigma]
    ring
  have hmass' : 0 ≤
      dirichletPerronCoefficientMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta) (c - alpha - beta) := by
    rw [hline]
    simpa only [a] using hmass
  have hfactor' :
      32 * (X : ℝ) ^ (c - alpha - beta) / T ≤
        32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2 := by
    simpa only [hline] using hfactor
  have htail := hbase.trans <| add_le_add
    (add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactor' hmass')) le_rfl
  rw [hline] at htail
  simpa only [gsA10TwoBlockMovingPerronIntegral,
    gsA10MovingPerronProjectionError, a, c, sigma, T, pow_two] using htail

/-- The already-controlled coefficient-mass contribution to the moving
projection error. -/
def gsA10MovingPerronCoefficientErrorScalar
    (y X : ℕ) (beta : ℝ) : ℝ :=
  (32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2) *
    ((gsA10SourceCoefficientMassConstant *
        (1 + Real.log (X : ℝ))) *
      ((gsA10OrdinaryLambdaWindowMassBase y X) ^ 2 *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))

/-- The alpha--beta independent coefficient in the source mass envelope.
The two moving powers are deliberately not included. -/
def gsA10MovingPerronMassConstant (y X : ℕ) : ℝ :=
  (gsA10SourceCoefficientMassConstant *
      (1 + Real.log (X : ℝ))) *
    (gsA10OrdinaryLambdaWindowMassBase y X) ^ 2

theorem dirichletPerronCoefficientMass_twoBlockTailored_le_movingEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    dirichletPerronCoefficientMass
        (gsA10TwoBlockTailoredCoefficient
          f hmul P₁ P₂ y X alpha beta)
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) ≤
      gsA10MovingPerronMassConstant y X *
        (X : ℝ) ^
          (1 - min (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1) := by
  have hmass :=
    dirichletPerronCoefficientMass_twoBlockTailored_fixedTao_le
      hmul hbound P₁ P₂ hy (by omega : 1 < X) hQ₂ hQ₃
        hlogy halpha0 halpha hbeta0 hbeta
  simpa only [gsA10MovingPerronMassConstant, mul_assoc] using hmass

/-- Source projection with the coefficient mass replaced by the continuous
fixed-high moving-power envelope.  This is the pointwise input for
`doubleIntervalIntegral_sourcePerron_fixedHigh_massEnvelope_le`. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_massEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2) +
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))) +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_rawError
      hmul hbound P₁ P₂ hX hlogX hlogy
        halpha0 halpha hbeta0 hbeta
  have hmass :=
    dirichletPerronCoefficientMass_twoBlockTailored_le_movingEnvelope
      hmul hbound P₁ P₂ hy hX hQ₂ hQ₃ hlogy
        halpha0 halpha hbeta0 hbeta
  have hfactor : 0 ≤
      32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) /
        (Real.log (X : ℝ)) ^ 2 := by positivity
  apply hbase.trans
  unfold gsA10MovingPerronRawProjectionError
  dsimp only
  have hterm :
      (32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) /
        (Real.log (X : ℝ)) ^ 2) *
          dirichletPerronCoefficientMass
            (gsA10TwoBlockTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta)
            (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) ≤
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))) := by
    calc
    _ ≤ (32 * (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) /
        (Real.log (X : ℝ)) ^ 2) *
        (gsA10MovingPerronMassConstant y X *
          (X : ℝ) ^
            (1 - min
              (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = _ := by ring
  exact add_le_add (add_le_add le_rfl hterm) le_rfl

/-- The moving coefficient-mass envelope averaged over the complete source
rectangle. -/
theorem doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_le
    {X : ℕ} (hX : 1 < X) (y : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))) ≤
      (32 / (Real.log (X : ℝ)) ^ 2) *
        (gsA10MovingPerronMassConstant y X * Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ))) := by
  let C : ℝ := 32 / (Real.log (X : ℝ)) ^ 2
  let F : ℝ → ℝ → ℝ := fun alpha beta ↦
    gsA10MovingPerronMassConstant y X *
      ((X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
        (X : ℝ) ^
          (1 - min
            (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hK : 0 ≤ gsA10MovingPerronMassConstant y X := by
    unfold gsA10MovingPerronMassConstant
    exact mul_nonneg
      (mul_nonneg gsA10SourceCoefficientMassConstant_nonneg
        (by positivity)) (sq_nonneg _)
  have hbase :=
    doubleIntervalIntegral_sourcePerron_fixedHigh_massEnvelope_le
      hX heta hK
  change (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, C * F alpha beta) ≤ _
  rw [show (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta, C * F alpha beta) =
        C * (∫ alpha : ℝ in 0..eta,
          ∫ beta : ℝ in 0..eta, F alpha beta) by
    simp only [intervalIntegral.integral_const_mul]]
  exact mul_le_mul_of_nonneg_left hbase hC

/-- Normalized contribution of the coefficient-mass projection error to
the reconstructed positive prefix. -/
theorem two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le
    {X : ℕ} (hX : 1 < X) (y : ℕ) {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))) /
        (X : ℝ) ≤
      64 * Real.exp 1 * gsA10MovingPerronMassConstant y X * eta /
        (Real.log (X : ℝ)) ^ 3 := by
  let I : ℝ :=
    ∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast hX)
  have hbase : I ≤
      (32 / (Real.log (X : ℝ)) ^ 2) *
        (gsA10MovingPerronMassConstant y X * Real.exp 1 * eta *
          ((X : ℝ) / Real.log (X : ℝ))) := by
    simpa only [I] using
      (doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_le hX y heta)
  have hscale : 0 ≤ (2 : ℝ) / X := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hbase hscale
  change 2 * I / (X : ℝ) ≤ _
  calc
    2 * I / (X : ℝ) = ((2 : ℝ) / X) * I := by ring
    _ ≤ ((2 : ℝ) / X) *
        ((32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X * Real.exp 1 * eta *
            ((X : ℝ) / Real.log (X : ℝ)))) := hscaled
    _ = 64 * Real.exp 1 * gsA10MovingPerronMassConstant y X * eta /
        (Real.log (X : ℝ)) ^ 3 := by
      field_simp [ne_of_gt hXR, ne_of_gt hlogX]
      ring

/-- Universal coefficient left after the source `log(X)^4 ≤ y` bound
is applied to both Mangoldt-window masses. -/
def gsA10MovingPerronAveragedMassConstant : ℝ :=
  128 * Real.exp 1 * gsA10SourceCoefficientMassConstant *
    gsA10OrdinaryLambdaWindowMassLogConstant ^ 2

theorem gsA10MovingPerronAveragedMassConstant_nonneg :
    0 ≤ gsA10MovingPerronAveragedMassConstant := by
  unfold gsA10MovingPerronAveragedMassConstant
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by norm_num) (Real.exp_nonneg 1))
      gsA10SourceCoefficientMassConstant_nonneg)
    (sq_nonneg _)

/-- After the source cutoff scalar is inserted, the complete normalized
coefficient-mass rectangle costs only its beta width `eta`. -/
theorem two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le_eta
    {X y : ℕ} (hX : 2 ≤ X) (hy3 : 3 ≤ y)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hy : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) :
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))) /
        (X : ℝ) ≤
      gsA10MovingPerronAveragedMassConstant * eta := by
  let logXval : ℝ := Real.log (X : ℝ)
  let massCoef : ℝ := gsA10OrdinaryLambdaWindowMassLogConstant
  let massBase : ℝ := gsA10OrdinaryLambdaWindowMassBase y X
  have hLogXval : 0 < logXval := zero_lt_one.trans_le hlogX
  have hMassCoef : 0 ≤ massCoef :=
    gsA10OrdinaryLambdaWindowMassLogConstant_nonneg
  have hMassBase0 : 0 ≤ massBase :=
    gsA10OrdinaryLambdaWindowMassBase_nonneg y X
  have hMassBase : massBase ≤ massCoef * logXval := by
    simpa only [massBase, massCoef, logXval] using
      (gsA10OrdinaryLambdaWindowMassBase_le_log
        (X := X) (y := y) (by omega) hy3 hlogX hprimeMass hy)
  have hMassCoefLog : 0 ≤ massCoef * logXval :=
    mul_nonneg hMassCoef hLogXval.le
  have hMassBaseSq : massBase ^ 2 ≤ (massCoef * logXval) ^ 2 := by
    nlinarith [sq_nonneg (massBase - massCoef * logXval)]
  have hOne : 1 + logXval ≤ 2 * logXval := by linarith
  have hsource : 0 ≤ gsA10SourceCoefficientMassConstant :=
    gsA10SourceCoefficientMassConstant_nonneg
  have hfront :
      gsA10SourceCoefficientMassConstant * (1 + logXval) ≤
        gsA10SourceCoefficientMassConstant * (2 * logXval) :=
    mul_le_mul_of_nonneg_left hOne hsource
  have hmass : gsA10MovingPerronMassConstant y X ≤
      2 * gsA10SourceCoefficientMassConstant * massCoef ^ 2 *
        logXval ^ 3 := by
    unfold gsA10MovingPerronMassConstant
    change (gsA10SourceCoefficientMassConstant * (1 + logXval)) *
      massBase ^ 2 ≤ _
    calc
      _ ≤ (gsA10SourceCoefficientMassConstant * (2 * logXval)) *
          (massCoef * logXval) ^ 2 :=
        mul_le_mul hfront hMassBaseSq (sq_nonneg massBase)
          (mul_nonneg hsource (by positivity))
      _ = 2 * gsA10SourceCoefficientMassConstant * massCoef ^ 2 *
          logXval ^ 3 := by
        ring
  have hbase :=
    two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le
      (X := X) (by omega) y heta
  have hfactor : 0 ≤ 64 * Real.exp 1 * eta / logXval ^ 3 := by positivity
  calc
    2 * (∫ alpha : ℝ in 0..eta,
      ∫ beta : ℝ in 0..eta,
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))) /
        (X : ℝ) ≤
      64 * Real.exp 1 * gsA10MovingPerronMassConstant y X * eta /
        logXval ^ 3 := by
        simpa only [logXval] using hbase
    _ = (64 * Real.exp 1 * eta / logXval ^ 3) *
        gsA10MovingPerronMassConstant y X := by ring
    _ ≤ (64 * Real.exp 1 * eta / logXval ^ 3) *
        (2 * gsA10SourceCoefficientMassConstant * massCoef ^ 2 *
          logXval ^ 3) :=
      mul_le_mul_of_nonneg_left hmass hfactor
    _ = gsA10MovingPerronAveragedMassConstant * eta := by
      unfold gsA10MovingPerronAveragedMassConstant
      dsimp only [massCoef]
      field_simp [ne_of_gt hLogXval]
      ring

/-- Normalized coefficient-mass part of the moving source rectangle. -/
def gsA10MovingPerronMassRectangle (y X : ℕ) (eta : ℝ) : ℝ :=
  2 * (∫ alpha : ℝ in 0..eta,
    ∫ beta : ℝ in 0..eta,
      (32 / (Real.log (X : ℝ)) ^ 2) *
        (gsA10MovingPerronMassConstant y X *
          ((X : ℝ) ^
              (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
            (X : ℝ) ^
              (1 - min
                (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1)))) /
      (X : ℝ)

theorem gsA10MovingPerronMassRectangle_le_eta
    {X y : ℕ} (hX : 2 ≤ X) (hy3 : 3 ≤ y)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hy : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ))
    {eta : ℝ} (heta : 0 ≤ eta) :
    gsA10MovingPerronMassRectangle y X eta ≤
      gsA10MovingPerronAveragedMassConstant * eta := by
  unfold gsA10MovingPerronMassRectangle
  exact
    two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le_eta
      hX hy3 hlogX hprimeMass hy heta

/-- Fixed negative-log source bound for the complete coefficient-mass
part of the A.10 rectangle. -/
theorem gsA10MovingPerronMassRectangle_le_sourceLog
    {X y : ℕ} (hX : 2 ≤ X) (hy3 : 3 ≤ y)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hprimeMass : Erdos67.PrimeEstimates.primeReciprocals X ≤
      Real.log (X : ℝ))
    (hy : (Real.log (X : ℝ)) ^ 4 ≤ (y : ℝ)) :
    gsA10MovingPerronMassRectangle y X (Real.log (y : ℝ))⁻¹ ≤
      gsA10MovingPerronAveragedMassConstant *
        (Real.log (y : ℝ))⁻¹ := by
  apply gsA10MovingPerronMassRectangle_le_eta
    hX hy3 hlogX hprimeMass hy
  have hyOne : (1 : ℝ) < y := by exact_mod_cast (show 1 < y by omega)
  exact (inv_pos.mpr (Real.log_pos hyOne)).le

/-- After the source Euler estimates, only the local near-diagonal mass
and endpoint coefficient remain coefficient-dependent. -/
theorem norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_sourceScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral
          f hmul P₁ P₂ y X alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X
          ((Real.log (X : ℝ)) ^ 2) +
        gsA10MovingPerronCoefficientErrorScalar y X beta +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta X‖ := by
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_error
      hmul hbound P₁ P₂ hX hlogX hlogy
        halpha0 halpha hbeta0 hbeta
  have hmass :=
    dirichletPerronCoefficientMass_twoBlockTailored_fixedTao_le
      hmul hbound P₁ P₂ hy (by omega : 1 < X) hQ₂ hQ₃
        hlogy halpha0 halpha hbeta0 hbeta
  have hfactor : 0 ≤
      32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2 := by positivity
  exact hbase.trans <| by
    unfold gsA10MovingPerronProjectionError
      gsA10MovingPerronCoefficientErrorScalar
    dsimp only
    gcongr

private theorem mrTwoBlock_selected_le_of_block_uppers
    (I₁ I₂ : ℕ × ℕ) {y : ℕ}
    (hI₁ : I₁.2 ≤ y) (hI₂ : I₂.2 ≤ y) :
    (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧ mrTwoBlockFirst I₁ p) →
      p ≤ y) ∧
    (∀ p, (¬ mrTwoBlockOutside I₁ I₂ p ∧ ¬ mrTwoBlockFirst I₁ p) →
      p ≤ y) := by
  constructor
  · intro p hp
    exact (mem_primesInBlock.mp hp.2).2.2.trans hI₁
  · intro p hp
    have hpI₂ : p ∈ primesInBlock I₂ := by
      by_contra hpI₂
      exact hp.1 ⟨hp.2, hpI₂⟩
    exact (mem_primesInBlock.mp hpI₂).2.2.trans hI₂

/-- Fixed-high moving-power envelope on the repaired canonical large
blocks. -/
theorem norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_le_massEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K)
    {y X : ℕ} (hy : 23 ≤ y) (hBlocks : 2 ^ (K ^ 2) ≤ y)
    (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral f hmul
          (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
            (gsA10CanonicalLargeSecondBlock K))
          (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
          y X alpha beta ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X ((Real.log (X : ℝ)) ^ 2) +
        (32 / (Real.log (X : ℝ)) ^ 2) *
          (gsA10MovingPerronMassConstant y X *
            ((X : ℝ) ^
                (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) *
              (X : ℝ) ^
                (1 - min
                  (Erdos67.EulerResidue.taoExponent X - 2 * beta) 1))) +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta X‖ := by
  obtain ⟨hI₁, hI₂⟩ := gsA10CanonicalLargeBlock_uppers_le hK
  obtain ⟨hQ₂, hQ₃⟩ := mrTwoBlock_selected_le_of_block_uppers
    (gsA10CanonicalLargeFirstBlock K)
    (gsA10CanonicalLargeSecondBlock K)
    (hI₁.trans hBlocks) (hI₂.trans hBlocks)
  exact
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_massEnvelope
      hmul hbound
      (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
        (gsA10CanonicalLargeSecondBlock K))
      (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
      hy hX hlogX hlogy hQ₂ hQ₃ halpha0 halpha hbeta0 hbeta

/-- The source-scaled moving projection on the repaired canonical large
blocks.  The selected-prime cutoff hypotheses are discharged from the
canonical block endpoints. -/
theorem norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_le_sourceScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K)
    {y X : ℕ} (hy : 23 ≤ y) (hBlocks : 2 ^ (K ^ 2) ≤ y)
    (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral f hmul
          (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
            (gsA10CanonicalLargeSecondBlock K))
          (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
          y X alpha beta ((Real.log (X : ℝ)) ^ 2)‖ ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X ((Real.log (X : ℝ)) ^ 2) +
        gsA10MovingPerronCoefficientErrorScalar y X beta +
        (1 / 2 : ℝ) *
          ‖gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta X‖ := by
  obtain ⟨hI₁, hI₂⟩ := gsA10CanonicalLargeBlock_uppers_le hK
  obtain ⟨hQ₂, hQ₃⟩ := mrTwoBlock_selected_le_of_block_uppers
    (gsA10CanonicalLargeFirstBlock K)
    (gsA10CanonicalLargeSecondBlock K)
    (hI₁.trans hBlocks) (hI₂.trans hBlocks)
  exact
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_sourceScalar
      hmul hbound
      (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
        (gsA10CanonicalLargeSecondBlock K))
      (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
      hy hX hlogX hlogy hQ₂ hQ₃ halpha0 halpha hbeta0 hbeta

/-- Normalized canonical-large moving projection.  This is the form used
after the alpha--beta rectangle is inserted into a positive prefix mean. -/
theorem norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_div_le_sourceScalar
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    {K : ℕ} (hK : 5 ≤ K)
    {y X : ℕ} (hy : 23 ≤ y) (hBlocks : 2 ^ (K ^ 2) ≤ y)
    (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 6 ≤ Real.log (y : ℝ))
    {alpha beta : ℝ}
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹) :
    ‖positivePrefixSum
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X -
        gsA10TwoBlockMovingPerronIntegral f hmul
          (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
            (gsA10CanonicalLargeSecondBlock K))
          (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
          y X alpha beta ((Real.log (X : ℝ)) ^ 2)‖ / X ≤
      dirichletPerronNearMass
          (gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta) X ((Real.log (X : ℝ)) ^ 2) / X +
        gsA10MovingPerronCoefficientErrorScalar y X beta / X +
        ‖gsA10TwoBlockTailoredCoefficient f hmul
            (mrTwoBlockOutside (gsA10CanonicalLargeFirstBlock K)
              (gsA10CanonicalLargeSecondBlock K))
            (mrTwoBlockFirst (gsA10CanonicalLargeFirstBlock K))
            y X alpha beta X‖ / (2 * X) := by
  have hbase :=
    norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_le_sourceScalar
      hmul hbound hK hy hBlocks hX hlogX hlogy
        halpha0 halpha hbeta0 hbeta
  have hXR : (0 : ℝ) < X := by
    exact_mod_cast (show 0 < X by omega)
  have hdiv := div_le_div_of_nonneg_right hbase hXR.le
  apply hdiv.trans_eq
  field_simp [ne_of_gt hXR]

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_rawError
#print axioms
  Erdos67.MRHalaszBands.dirichletPerronCoefficientMass_twoBlockTailored_le_movingEnvelope
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_massEnvelope
#print axioms
  Erdos67.MRHalaszBands.doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_le
#print axioms
  Erdos67.MRHalaszBands.two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le
#print axioms
  Erdos67.MRHalaszBands.two_mul_doubleIntervalIntegral_gsA10MovingPerronMassEnvelope_div_le_eta
#print axioms
  Erdos67.MRHalaszBands.gsA10MovingPerronMassRectangle_le_eta
#print axioms
  Erdos67.MRHalaszBands.gsA10MovingPerronMassRectangle_le_sourceLog
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_le_massEnvelope
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_error
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10TwoBlockTailored_sub_movingPerron_le_sourceScalar
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_le_sourceScalar
#print axioms
  Erdos67.MRHalaszBands.norm_positivePrefixSum_gsA10CanonicalLargeTailored_sub_movingPerron_div_le_sourceScalar
