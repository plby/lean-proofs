import ErdosProblems.Erdos239.External.Erdos67.MRGSA10SourceFullVerticalContour

/-!
# A continuous source-rectangle envelope for the fixed A.10 contour
-/

open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

def gsA10SourceContourBetaPoleEnvelope
    (A X y : ℕ) (alpha beta T Arow Brow : ℝ) : ℝ :=
  let L := Real.log (X : ℝ)
  let d := L⁻¹
  let power :=
    (X : ℝ) ^
        (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
      ((X / y : ℕ) : ℝ) ^ beta
  let K := Real.exp
    (28 * Real.exp 4 * Erdos67.EulerQuantitative.primeQuadraticConstant +
      36 * gsA9SourceShiftConstant)
  let C := (2 * Real.pi)⁻¹ * (3 * gsA9SmallPrimeEulerBound) * K *
    gsA10SourceMaximumModulusSqrtScalar A X
  let Q := Real.exp 1 * Real.sqrt Real.pi * (Arow + Brow * T)
  let D := 2 * gsA10PrimeLambdaSymmetricBetaScalarConstant
  let G :=
    2 * gsA10PrimeLambdaHarmonicBudget X *
        gsA10HigherPrimePowerGeometricMass y X +
      (gsA10HigherPrimePowerGeometricMass y X) ^ 2
  C *
    (Q * D *
        (power * (max (d + beta) (d / 2)) ^ (-3 / 2 : ℝ)) +
      4 * T * G *
        (power * Real.sqrt ((max (d + beta) (d / 2))⁻¹)))

theorem continuous_gsA10SourceContourBetaPoleEnvelope
    {X y : ℕ} (hX : 2 ≤ X) (hy : 0 < y) (hyX : y ≤ X)
    (A : ℕ) (T Arow Brow : ℝ) :
    Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      gsA10SourceContourBetaPoleEnvelope
        A X y alpha beta T Arow Brow)) := by
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹
  have hL : 0 < L := by
    dsimp only [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hd : 0 < d := by dsimp only [d]; positivity
  have hXne : (X : ℝ) ≠ 0 := by
    exact_mod_cast (show X ≠ 0 by omega)
  have hdivNat : X / y ≠ 0 := by
    exact Nat.ne_of_gt (Nat.div_pos hyX hy)
  have hpow : Continuous (Function.uncurry (fun alpha beta : ℝ ↦
      (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta) *
        ((X / y : ℕ) : ℝ) ^ beta)) := by
    exact ((Real.continuous_const_rpow hXne).comp (by fun_prop)).mul
      ((Real.continuous_const_rpow (by exact_mod_cast hdivNat)).comp
        (by fun_prop))
  have hpoleThree : Continuous (fun beta : ℝ ↦
      (max (d + beta) (d / 2)) ^ (-3 / 2 : ℝ)) := by
    apply Continuous.rpow_const
    · fun_prop
    · intro beta
      left
      exact ((half_pos hd).trans_le (le_max_right _ _)).ne'
  have hpoleHalf : Continuous (fun beta : ℝ ↦
      Real.sqrt ((max (d + beta) (d / 2))⁻¹)) := by
    apply Real.continuous_sqrt.comp
    apply Continuous.inv₀
    · fun_prop
    · intro beta hzero
      exact ((half_pos hd).trans_le (le_max_right _ _)).ne' hzero
  unfold gsA10SourceContourBetaPoleEnvelope
  dsimp only [L, d, Function.uncurry_apply_pair]
  exact continuous_const.mul
    ((continuous_const.mul
        (hpow.mul (hpoleThree.comp continuous_snd))).add
      (continuous_const.mul
        (hpow.mul (hpoleHalf.comp continuous_snd))))

theorem norm_gsA10SourceTailoredPerronIntegral_le_betaPoleEnvelope
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X y : ℕ} (hy23 : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
    (hN : 2 ≤ X / y) (hlogy : 4 ≤ Real.log (y : ℝ))
    (hlogX : 1 ≤ Real.log (X : ℝ))
    (hnonpret : MRArchimedeanNonpretentious f A X)
    {eta T Arow Brow : ℝ} (hetaY : eta ≤ (Real.log (y : ℝ))⁻¹)
    (hetaQuarter : eta ≤ 1 / 4)
    (hT0 : 0 < T) (hTX : T ≤ X)
    (hArow : 0 ≤ Arow) (hBrow : 0 ≤ Brow)
    (hrow : ∀ n ∈ gsA10PrimeWindow y X,
      (∑ m ∈ gsA10PrimeWindow y X,
          (Real.log (m : ℝ) / m) *
            finiteHalaszGaussianPairKernel (T⁻¹ ^ 2)
              (Real.log m - Real.log n)) ≤ Arow / T + Brow)
    {alpha beta : ℝ} (halpha : alpha ∈ Icc (0 : ℝ) eta)
    (hbeta : beta ∈ Icc (0 : ℝ) eta) :
    ‖gsA10TailoredPerronIntegral
        (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
        (gsA9HighArithmetic f y)
        (gsA9HighGeneralizedMangoldt hmul y)
        y X (Erdos67.EulerResidue.taoExponent X) alpha beta T‖ ≤
      gsA10SourceContourBetaPoleEnvelope
        A X y alpha beta T Arow Brow := by
  let L : ℝ := Real.log (X : ℝ)
  let d : ℝ := L⁻¹
  have hL : 0 < L := by dsimp only [L]; linarith
  have hd : 0 < d := by dsimp only [d]; positivity
  have hactual :=
    norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget
      hmul hbound P₁ P₂ hsmallOutside hy23 hyX hX hN hlogy hlogX
        hnonpret halpha.1 (halpha.2.trans hetaY) hbeta.1
        (hbeta.2.trans hetaY) (hbeta.2.trans hetaQuarter)
        hT0 hTX hArow hBrow hrow
  have hpole := gsA10SourceAffineVerticalBudget_le_betaPoleBudget
    (A := A) (y := y) hX hbeta.1 (hbeta.2.trans hetaQuarter)
      hT0.le hArow hBrow
  have hsmall0 : 0 ≤ gsA9SmallPrimeEulerBound := by
    have hsmall := norm_gsA9SmallPrimeEulerProduct_le hbound
      (sigma := (1 / 2 : ℝ)) (t := 0) le_rfl
    exact (norm_nonneg _).trans hsmall
  have hscale0 : 0 ≤ (2 * Real.pi)⁻¹ *
      (3 * gsA9SmallPrimeEulerBound *
        (X : ℝ) ^
          (Erdos67.EulerResidue.taoExponent X - alpha - beta)) := by
    positivity
  have hchain := hactual.trans
    (mul_le_mul_of_nonneg_left hpole hscale0)
  have hmax : max (d + beta) (d / 2) = d + beta := by
    rw [max_eq_left]
    linarith [hbeta.1, hd]
  calc
    _ ≤ (2 * Real.pi)⁻¹ *
        (3 * gsA9SmallPrimeEulerBound *
          (X : ℝ) ^
            (Erdos67.EulerResidue.taoExponent X - alpha - beta)) *
        gsA10SourceAffineVerticalBetaPoleBudget
          A X y beta T Arow Brow := hchain
    _ = gsA10SourceContourBetaPoleEnvelope
          A X y alpha beta T Arow Brow := by
      unfold gsA10SourceContourBetaPoleEnvelope
        gsA10SourceAffineVerticalBetaPoleBudget
      dsimp only [L, d]
      rw [hmax]
      ring

end


end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_betaPoleEnvelope
