import ErdosProblems.Erdos67b.MRGSA10TailoredPerronContour
import ErdosProblems.Erdos67b.MRGSA10GlobalSecondaryShiu

/-!
# The complete tailored A.10 source rectangle

The pointwise source-window Perron bound is integrated over the auxiliary
alpha--beta square without continuity or cardinality loss.  The resulting
prefix-mean theorem exposes only the shifted-high-line charge and the exact
Perron near-mass/coefficient-mass/endpoint error.
-/

open scoped BigOperators
open Complex Set

namespace Erdos67b.MRHalaszBands

noncomputable section

open BoundedGaps.Maynard

/-- A uniform pointwise bound controls the two nested source interval
integrals.  This form uses the constant-bound integral theorem and therefore
does not require a separate continuity premise. -/
theorem norm_two_mul_doubleIntervalIntegral_le_two_mul_sq_mul_of_bound
    {F : ℝ → ℝ → ℂ} {eta B : ℝ}
    (heta : 0 ≤ eta)
    (hmajor : ∀ alpha ∈ Set.Icc (0 : ℝ) eta,
      ∀ beta ∈ Set.Icc (0 : ℝ) eta, ‖F alpha beta‖ ≤ B) :
    ‖2 * ∫ alpha in 0..eta, ∫ beta in 0..eta, F alpha beta‖ ≤
      2 * eta ^ 2 * B := by
  have hinner (alpha : ℝ) (halpha : alpha ∈ Set.Icc (0 : ℝ) eta) :
      ‖∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤ eta * B := by
    have hraw := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun beta : ℝ ↦ F alpha beta) (C := B)
      (a := (0 : ℝ)) (b := eta) (fun beta hbeta ↦ by
        rw [Set.uIoc_of_le heta] at hbeta
        exact hmajor alpha halpha beta ⟨hbeta.1.le, hbeta.2⟩)
    simpa [abs_of_nonneg heta, mul_comm] using hraw
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun alpha : ℝ ↦ ∫ beta in (0 : ℝ)..eta, F alpha beta)
    (C := eta * B) (a := (0 : ℝ)) (b := eta) (fun alpha halpha ↦ by
      rw [Set.uIoc_of_le heta] at halpha
      exact hinner alpha ⟨halpha.1.le, halpha.2⟩)
  rw [norm_mul]
  norm_num
  calc
    2 * ‖∫ alpha in (0 : ℝ)..eta,
          ∫ beta in (0 : ℝ)..eta, F alpha beta‖ ≤
        2 * ((eta * B) * |eta - 0|) :=
      mul_le_mul_of_nonneg_left houter (by norm_num)
    _ = 2 * eta ^ 2 * B := by
      rw [sub_zero, abs_of_nonneg heta]
      ring

/-- The exact pointwise Perron projection error at source height
`T = log(X)^2`. -/
def gsA10SourcePerronProjectionError
    (f : ℕ → ℂ) (hmul : IsMultiplicativeOnPositiveNat f)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (y X : ℕ) (alpha beta : ℝ) : ℝ :=
  let a := gsA10SourceTailoredCoefficient f hmul P₁ P₂ y X alpha beta
  let sigma := Erdos67b.EulerResidue.taoExponent X - alpha - beta
  dirichletPerronNearMass a X ((Real.log (X : ℝ)) ^ 2) +
    (32 * Real.exp 2 * X / (Real.log (X : ℝ)) ^ 2) *
      dirichletPerronCoefficientMass a sigma +
    (1 / 2 : ℝ) * ‖a X‖

/-- The source-facing normalized central-prefix budget after adding the
global Shiu secondary term. -/
def gsA10SourceCentralPrefixBudget
    (y X : ℕ) (B E : ℝ) : ℝ :=
  (2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
        (gsA10SourceUniformPerronScalar
          y X ((Real.log (X : ℝ)) ^ 2) B + E) +
      gsA10GlobalSecondaryShiuConstant *
        ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ)) /
    (X : ℝ)

/-- The source-height prefix projection theorem, specialized after the
fixed small-prime deletion. -/
theorem norm_positivePrefixSum_gsA10SourceTailored_sub_perron_le_error
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
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    ‖positivePrefixSum
          (gsA10SourceTailoredCoefficient
            f hmul P₁ P₂ y X alpha beta) X -
        gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
          (gsA9HighArithmetic g y)
          (gsA9HighGeneralizedMangoldt hmulG y)
          y X (Erdos67b.EulerResidue.taoExponent X) alpha beta
            ((Real.log (X : ℝ)) ^ 2)‖ ≤
      gsA10SourcePerronProjectionError
        f hmul P₁ P₂ y X alpha beta := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have hbase :=
    norm_positivePrefixSum_gsA10TwoBlockTailored_sub_perron_le_sourceHeight
      hmulG hboundG P₁ P₂ hX hlogX hlogy
        halpha0 halpha hbeta0 hbeta
  simpa only [g, hmulG, gsA10SourceTailoredCoefficient,
    gsA10SourceDeleted, gsA10SourcePerronProjectionError] using hbase

/-- The tailored rectangular prefix for the deleted source coefficient is
bounded by the uniform Perron contour scalar plus the exact projection
error scalar. -/
theorem norm_gsA10SourceTailoredIntegratedPrefix_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    {B E : ℝ} (hB : 0 ≤ B)
    (hcharge : ∀ beta ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
      ∀ t : ℝ, |t| ≤ (Real.log (X : ℝ)) ^ 2 →
        gsA10SourceShiftedHighCharge f X beta t ≤ B)
    (herror : ∀ alpha ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
      ∀ beta ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
        gsA10SourcePerronProjectionError
          f hmul P₁ P₂ y X alpha beta ≤ E) :
    let g := gsA10SourceDeleted f
    let hmulG := gsDeletePrimeBand_isMultiplicativeOnPositiveNat
      hmul gsA9SmallPrime
    ‖gsA10TwoBlockTailoredIntegratedPrefix
        g hmulG P₁ P₂ y X (Real.log (y : ℝ))⁻¹‖ ≤
      2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
        (gsA10SourceUniformPerronScalar
          y X ((Real.log (X : ℝ)) ^ 2) B + E) := by
  dsimp only
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  let eta : ℝ := (Real.log (y : ℝ))⁻¹
  let T : ℝ := (Real.log (X : ℝ)) ^ 2
  let P : ℝ := gsA10SourceUniformPerronScalar y X T B
  have heta : 0 ≤ eta := by
    dsimp only [eta]
    positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  unfold gsA10TwoBlockTailoredIntegratedPrefix
  unfold gsA10TailoredIntegratedPrefix
  apply norm_two_mul_doubleIntervalIntegral_le_two_mul_sq_mul_of_bound heta
  intro alpha halpha beta hbeta
  have hperron :
      ‖gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
          (gsA9HighArithmetic g y)
          (gsA9HighGeneralizedMangoldt hmulG y)
          y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ ≤ P := by
    convert norm_gsA10SourceTailoredPerronIntegral_le_sourceUniform
      hmul hcomp hbound P₁ P₂ hy hX hlogX hlogy
        halpha.1 halpha.2 hbeta.1 hbeta.2 hT hB
        (hcharge beta hbeta) using 1
    all_goals rfl
  have hproj :
      ‖positivePrefixSum
            (gsA10SourceTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta) X -
          gsA10TailoredPerronIntegral
            (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
            (gsA9HighArithmetic g y)
            (gsA9HighGeneralizedMangoldt hmulG y)
            y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ ≤
        gsA10SourcePerronProjectionError
          f hmul P₁ P₂ y X alpha beta := by
    convert norm_positivePrefixSum_gsA10SourceTailored_sub_perron_le_error
      hmul hbound P₁ P₂ hX hlogX hlogy
        halpha.1 halpha.2 hbeta.1 hbeta.2 using 1
    all_goals rfl
  have htriangle := norm_le_norm_add_norm_sub
    (gsA10TailoredPerronIntegral
      (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
      (gsA9HighArithmetic g y)
      (gsA9HighGeneralizedMangoldt hmulG y)
      y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T)
    (positivePrefixSum
      (gsA10SourceTailoredCoefficient
        f hmul P₁ P₂ y X alpha beta) X)
  rw [norm_sub_rev] at htriangle
  calc
    ‖positivePrefixSum
        (gsA10TailoredCoefficient
          (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
          (gsA9HighArithmetic g y)
          (gsA9HighGeneralizedMangoldt hmulG y)
          y X alpha beta) X‖ ≤
        ‖gsA10TailoredPerronIntegral
          (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
          (gsA9HighArithmetic g y)
          (gsA9HighGeneralizedMangoldt hmulG y)
          y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ +
        ‖positivePrefixSum
            (gsA10SourceTailoredCoefficient
              f hmul P₁ P₂ y X alpha beta) X -
          gsA10TailoredPerronIntegral
            (gsA10TwoBlockAlternatingLow g P₁ P₂ y)
            (gsA9HighArithmetic g y)
            (gsA9HighGeneralizedMangoldt hmulG y)
            y X (Erdos67b.EulerResidue.taoExponent X) alpha beta T‖ := by
      simpa only [g, hmulG, gsA10SourceTailoredCoefficient,
        gsA10TwoBlockTailoredCoefficient, gsA10SourceDeleted] using htriangle
    _ ≤ P + gsA10SourcePerronProjectionError
          f hmul P₁ P₂ y X alpha beta := by
      exact add_le_add hperron hproj
    _ ≤ P + E := add_le_add le_rfl (herror alpha halpha beta hbeta)

/-- Complete source-facing A.10 central prefix bound.  The reconstructed
coefficient is the fixed-small-prime-deleted source coefficient; all global
secondary and finite-window terms have been discharged. -/
theorem norm_positivePrefixMean_gsA10SourceDeleted_reconstructed_le
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hcomp : IsCompletelyMultiplicativeOnPositive f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hy : 23 ≤ y) (hX : 2 ≤ X) (hyX : y ≤ X)
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hlogy : 4 ≤ Real.log (y : ℝ))
    (hQ₂ : ∀ p, (¬ P₁ p ∧ P₂ p) → p ≤ y)
    (hQ₃ : ∀ p, (¬ P₁ p ∧ ¬ P₂ p) → p ≤ y)
    {B E : ℝ} (hB : 0 ≤ B)
    (hcharge : ∀ beta ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
      ∀ t : ℝ, |t| ≤ (Real.log (X : ℝ)) ^ 2 →
        gsA10SourceShiftedHighCharge f X beta t ≤ B)
    (herror : ∀ alpha ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
      ∀ beta ∈ Set.Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹,
        gsA10SourcePerronProjectionError
          f hmul P₁ P₂ y X alpha beta ≤ E) :
    ‖positivePrefixMean
        (gsA10TwoBlockReconstructedCoefficient
          (gsA10SourceDeleted f) P₁ P₂ y) X‖ ≤
      gsA10SourceCentralPrefixBudget y X B E := by
  let g : ℕ → ℂ := gsA10SourceDeleted f
  let hmulG : IsMultiplicativeOnPositiveNat g :=
    gsDeletePrimeBand_isMultiplicativeOnPositiveNat hmul gsA9SmallPrime
  have hcompG : IsCompletelyMultiplicativeOnPositive g :=
    gsDeletePrimeBand_isCompletelyMultiplicativeOnPositive
      hcomp gsA9SmallPrime
  have hboundG : ∀ n, 0 < n → ‖g n‖ ≤ 1 := by
    intro n hn
    exact norm_gsDeletePrimeBand_le_one hbound gsA9SmallPrime hn
  have htail := norm_gsA10SourceTailoredIntegratedPrefix_le
    hmul hcomp hbound P₁ P₂ hy hX hlogX hlogy hB hcharge herror
  have hsumBase :=
    norm_positivePrefixSum_gsA10TwoBlockReconstructed_le_tailored_add_log
      hmulG hcompG hboundG P₁ P₂ hy hyX hQ₂ hQ₃
  have hsum :
      ‖positivePrefixSum
          (gsA10TwoBlockReconstructedCoefficient g P₁ P₂ y) X‖ ≤
        2 * (Real.log (y : ℝ))⁻¹ ^ 2 *
            (gsA10SourceUniformPerronScalar
              y X ((Real.log (X : ℝ)) ^ 2) B + E) +
          gsA10GlobalSecondaryShiuConstant *
            ((X : ℝ) / Real.log (X : ℝ)) * Real.log (y : ℝ) := by
    exact hsumBase.trans (add_le_add
      (by simpa only [g, hmulG] using htail) le_rfl)
  have hXR : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  unfold positivePrefixMean
  rw [norm_div, Complex.norm_natCast]
  unfold gsA10SourceCentralPrefixBudget
  exact div_le_div_of_nonneg_right hsum hXR.le

end

end Erdos67b.MRHalaszBands

#print axioms Erdos67b.MRHalaszBands.norm_gsA10SourceTailoredIntegratedPrefix_le
#print axioms
  Erdos67b.MRHalaszBands.norm_positivePrefixMean_gsA10SourceDeleted_reconstructed_le
