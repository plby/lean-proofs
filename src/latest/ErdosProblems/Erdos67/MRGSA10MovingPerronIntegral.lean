import ErdosProblems.Erdos67.MRGSA10MovingPerronContour
import ErdosProblems.Erdos67.MRHalaszPerron
import ErdosProblems.Erdos67.MRGSA10PerronErrorSchedule

/-!
# The A.10 Perron integral on the beta-dependent line

The Perron parameter is moved from `c₀` to `c₀ - beta`.  Consequently
the common high-prime factor remains exactly at the Halasz point `c₀ + it`,
while the actual Perron line is `c₀ - alpha - 2 beta`.
-/

open scoped BigOperators LSeries.notation
open Complex

namespace Erdos67.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- The actual two-block A.10 Perron integral with the beta-dependent
choice of the Perron parameter. -/
def gsA10TwoBlockMovingPerronIntegral
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta T : ℝ) : ℂ :=
  gsA10TailoredPerronIntegral
    (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
    (gsA9HighArithmetic f y)
    (gsA9HighGeneralizedMangoldt hmul y)
    y X (Erdos67.EulerResidue.taoExponent X - beta) alpha beta T

/-- A rectangle-uniform scalar for the moving Perron integral. -/
def gsA10MovingPerronScalar (y A X : ℕ) (T : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ((gsA10MovingVerticalScalar y A X * (Real.exp 2 * X) /
      (1 / 2 : ℝ)) * (2 * T))

/-- The generic Perron majorant on every source moving line is bounded by
the explicit rectangle-uniform scalar. -/
theorem perronVerticalMajorant_le_gsA10MovingPerronScalar
    {y A X : ℕ} (hX : 2 ≤ X)
    {alpha beta T : ℝ} (hlogy : 6 ≤ Real.log (y : ℝ))
    (halpha0 : 0 ≤ alpha)
    (halpha : alpha ≤ (Real.log (y : ℝ))⁻¹)
    (hbeta0 : 0 ≤ beta)
    (hbeta : beta ≤ (Real.log (y : ℝ))⁻¹)
    (hT0 : 0 ≤ T) (hM : 0 ≤ gsA10MovingVerticalScalar y A X) :
    Erdos67.MRHalaszPerron.perronVerticalMajorant
        (gsA10MovingVerticalScalar y A X) X
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) T ≤
      gsA10MovingPerronScalar y A X T := by
  let sigma : ℝ :=
    Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ Erdos67.EulerResidue.taoExponent X := by
    unfold Erdos67.EulerResidue.taoExponent
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hsigmaHalf : 1 / 2 ≤ sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hsigma : 0 < sigma :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le hsigmaHalf
  have hpow : (X : ℝ) ^ sigma ≤ Real.exp 2 * X := by
    dsimp only [sigma]
    simpa only [sub_sub] using
      (rpow_sourcePerronLine_le_exp_two_mul hX halpha0
        (mul_nonneg (by norm_num) hbeta0 : 0 ≤ 2 * beta))
  have hnum : gsA10MovingVerticalScalar y A X * (X : ℝ) ^ sigma ≤
      gsA10MovingVerticalScalar y A X * (Real.exp 2 * X) :=
    mul_le_mul_of_nonneg_left hpow hM
  have hfrac :
      gsA10MovingVerticalScalar y A X * (X : ℝ) ^ sigma / sigma ≤
        gsA10MovingVerticalScalar y A X * (Real.exp 2 * X) /
          (1 / 2 : ℝ) := by
    calc
      _ ≤ gsA10MovingVerticalScalar y A X * (Real.exp 2 * X) / sigma :=
        div_le_div_of_nonneg_right hnum hsigma.le
      _ ≤ gsA10MovingVerticalScalar y A X * (Real.exp 2 * X) /
          (1 / 2 : ℝ) :=
        div_le_div_of_nonneg_left
          (mul_nonneg hM (by positivity)) (by norm_num) hsigmaHalf
  unfold Erdos67.MRHalaszPerron.perronVerticalMajorant
  unfold gsA10MovingPerronScalar
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hfrac (by positivity))
    (inv_nonneg.mpr (by positivity))

/-- Exact vertical-majorant form of the undeleted moving-line contour. -/
theorem norm_gsA10TwoBlockTailoredPerronIntegral_le_moving
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
    (hT0 : 0 ≤ T) (hTX : T ≤ X) :
    ‖gsA10TwoBlockMovingPerronIntegral
        f hmul P₁ P₂ y X alpha beta T‖ ≤
      Erdos67.MRHalaszPerron.perronVerticalMajorant
        (gsA10MovingVerticalScalar y A X) X
        (Erdos67.EulerResidue.taoExponent X - alpha - 2 * beta) T := by
  let c₀ : ℝ := Erdos67.EulerResidue.taoExponent X
  let sigma : ℝ := c₀ - alpha - 2 * beta
  have hlogyPos : 0 < Real.log (y : ℝ) := by linarith
  have hetaSixth : (Real.log (y : ℝ))⁻¹ ≤ 1 / 6 := by
    simpa only [one_div] using
      inv_anti₀ (by norm_num : (0 : ℝ) < 6) hlogy
  have hcOne : 1 ≤ c₀ := by
    dsimp only [c₀, Erdos67.EulerResidue.taoExponent]
    have hlogX : 0 < Real.log (X : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < X by omega))
    exact le_add_of_nonneg_right (inv_pos.mpr hlogX).le
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    have hab : alpha + 2 * beta ≤
        3 * (Real.log (y : ℝ))⁻¹ := by linarith
    linarith
  have hM : 0 ≤ gsA10MovingVerticalScalar y A X :=
    gsA10MovingVerticalScalar_nonneg
      hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
      hlogy halpha0 halpha hbeta0 hbeta
  have hL :=
    norm_LSeries_gsA10TwoBlockTailoredCoefficient_le_movingScalar_of_abs_le
      hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
      hlogy halpha0 halpha hbeta0 hbeta hTX
  have hmain :=
    Erdos67.MRHalaszPerron.norm_dirichletPerronIntegral_le_of_uniform
      (a := (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta : ℕ → ℂ))
      (y := (X : ℝ)) (sigma := sigma) (T := T)
      (M := gsA10MovingVerticalScalar y A X)
      (by exact_mod_cast (show 0 < X by omega)) hsigma hT0 hM hL
  unfold gsA10TwoBlockMovingPerronIntegral gsA10TailoredPerronIntegral
  change ‖dirichletPerronIntegral
      (gsA10TwoBlockTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) X
      ((Erdos67.EulerResidue.taoExponent X - beta) - alpha - beta) T‖ ≤ _
  convert hmain using 1 <;> dsimp only [c₀, sigma] <;> ring_nf

/-- Rectangle-uniform scalar form of the undeleted moving-line Perron
integral. -/
theorem norm_gsA10TwoBlockMovingPerronIntegral_le_scalar
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
    (hT0 : 0 ≤ T) (hTX : T ≤ X) :
    ‖gsA10TwoBlockMovingPerronIntegral
        f hmul P₁ P₂ y X alpha beta T‖ ≤
      gsA10MovingPerronScalar y A X T := by
  have hM : 0 ≤ gsA10MovingVerticalScalar y A X :=
    gsA10MovingVerticalScalar_nonneg
      hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
      hlogy halpha0 halpha hbeta0 hbeta
  exact (norm_gsA10TwoBlockTailoredPerronIntegral_le_moving
    hmul hcomp hbound P₁ P₂ hy hX hnonpret hlarge₂ hlarge₃
    hlogy halpha0 halpha hbeta0 hbeta hT0 hTX).trans
      (perronVerticalMajorant_le_gsA10MovingPerronScalar
        hX hlogy halpha0 halpha hbeta0 hbeta hT0 hM)

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10TwoBlockTailoredPerronIntegral_le_moving
#print axioms
  Erdos67.MRHalaszBands.norm_gsA10TwoBlockMovingPerronIntegral_le_scalar
