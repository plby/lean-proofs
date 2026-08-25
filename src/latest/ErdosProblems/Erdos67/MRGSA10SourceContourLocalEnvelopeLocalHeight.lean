import ErdosProblems.Erdos67.MRGSA10SourceFullVerticalContourLocalHeight
import ErdosProblems.Erdos67.MRGSA10SourceContourLocalEnvelope

/-!
# Source contour envelope from local-height separation
-/

open Complex MeasureTheory Set

namespace Erdos67.MRHalaszBands

noncomputable section

theorem norm_gsA10SourceTailoredPerronIntegral_le_betaPoleEnvelope_of_localHeight
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    (hsmallOutside : ∀ p ∈ gsA9SmallPrimeFinset, P₁ p)
    {A X y : ℕ} (hy23 : 23 ≤ y) (hyX : y ≤ X) (hX : 2 ≤ X)
    (hN : 2 ≤ X / y) (hlogy : 4 ≤ Real.log (y : ℝ))
    (hlogX : 1 ≤ Real.log (X : ℝ))
    {eta T Arow Brow : ℝ} (hetaY : eta ≤ (Real.log (y : ℝ))⁻¹)
    (hetaQuarter : eta ≤ 1 / 4)
    (hT0 : 0 < T)
    (hlogT : 1 + Real.log (X : ℝ) ≤ T ^ 2)
    (hdist : ∀ u : ℝ, |u| ≤ T →
      (A : ℝ) ≤ pretentiousDistSq f (archimedeanTwist u) X)
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
    norm_gsA10SourceTailoredPerronIntegral_le_affineVerticalBudget_of_localHeight
      hmul hbound P₁ P₂ hsmallOutside hy23 hyX hX hN hlogy hlogX
        halpha.1 (halpha.2.trans hetaY) hbeta.1
        (hbeta.2.trans hetaY) (hbeta.2.trans hetaQuarter)
        hT0 hlogT hdist hArow hBrow hrow
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
  Erdos67.MRHalaszBands.norm_gsA10SourceTailoredPerronIntegral_le_betaPoleEnvelope_of_localHeight
