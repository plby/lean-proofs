import ErdosProblems.Erdos67.MRGSA10FixedSourceProjection
import ErdosProblems.Erdos67.MRGSA10DoubleIntegralMajorantOn
import ErdosProblems.Erdos67.MRGSA10SourceTailoredPerronContinuousOn

/-!
# Norm of the integrated fixed-source Perron contour

The analytic contour theorem controls the double integral of the pointwise
norm.  This module turns that bound into the norm of the actual integrated
Perron expression using only continuity on the source rectangle.
-/

open Set MeasureTheory

namespace Erdos67.MRHalaszBands

noncomputable section

theorem norm_gsA10TwoBlockSourcePerronIntegrated_le_doubleIntegral_norm
    {f : ℕ → ℂ} (hmul : IsMultiplicativeOnPositiveNat f)
    (hbound : ∀ n, 0 < n → ‖f n‖ ≤ 1)
    (P₁ P₂ : ℕ → Prop) [DecidablePred P₁] [DecidablePred P₂]
    {y X : ℕ} (hX : 2 ≤ X) (hlogy : 4 ≤ Real.log (y : ℝ))
    {eta T : ℝ} (heta0 : 0 ≤ eta)
    (heta : eta ≤ (Real.log (y : ℝ))⁻¹) (hT : 0 ≤ T) :
    ‖gsA10TwoBlockSourcePerronIntegrated f hmul P₁ P₂ y X eta T‖ ≤
      2 * ∫ alpha : ℝ in 0..eta,
        ∫ beta : ℝ in 0..eta,
          ‖gsA10TailoredPerronIntegral
              (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
              (gsA9HighArithmetic f y)
              (gsA9HighGeneralizedMangoldt hmul y)
              y X (Erdos67.EulerResidue.taoExponent X)
                alpha beta T‖ := by
  let P : ℝ → ℝ → ℂ := fun alpha beta ↦
    gsA10TailoredPerronIntegral
      (gsA10TwoBlockAlternatingLow f P₁ P₂ y)
      (gsA9HighArithmetic f y)
      (gsA9HighGeneralizedMangoldt hmul y)
      y X (Erdos67.EulerResidue.taoExponent X) alpha beta T
  let Q : ℝ → ℝ → ℂ := fun _ _ ↦ 0
  let G : ℝ → ℝ → ℝ := fun alpha beta ↦ ‖P alpha beta‖
  have hPwide : ContinuousOn (Function.uncurry P)
      (Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
        Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹) := by
    dsimp only [P]
    exact continuousOn_uncurry_gsA10SourceTailoredPerronIntegral_sourceRectangle
      hmul hbound P₁ P₂ hX hlogy hT
  have hsubset : Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta ⊆
      Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ ×ˢ
        Icc (0 : ℝ) (Real.log (y : ℝ))⁻¹ := by
    intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans heta⟩,
      ⟨hz.2.1, hz.2.2.trans heta⟩⟩
  have hP : ContinuousOn (Function.uncurry P)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) :=
    hPwide.mono hsubset
  have hQ : ContinuousOn (Function.uncurry Q)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    dsimp only [Q]
    fun_prop
  have hG : ContinuousOn (Function.uncurry G)
      (Icc (0 : ℝ) eta ×ˢ Icc (0 : ℝ) eta) := by
    dsimp only [G]
    exact hP.norm
  have hmajor : ∀ alpha ∈ Icc (0 : ℝ) eta,
      ∀ beta ∈ Icc (0 : ℝ) eta,
        ‖P alpha beta - Q alpha beta‖ ≤ G alpha beta := by
    intro alpha halpha beta hbeta
    simp only [Q, G, sub_zero, le_refl]
  have h :=
    norm_two_mul_doubleIntervalIntegral_sub_le_of_pointwise_continuousOn
      (P := P) (Q := Q) (G := G) heta0 hP hQ hG hmajor
  simpa only [gsA10TwoBlockSourcePerronIntegrated, P, Q, G,
    intervalIntegral.integral_zero, mul_zero, sub_zero] using h

end

end Erdos67.MRHalaszBands

#print axioms
  Erdos67.MRHalaszBands.norm_gsA10TwoBlockSourcePerronIntegrated_le_doubleIntegral_norm
