import ErdosProblems.Erdos421.WindowL1Bounds
import ErdosProblems.Erdos421.ClippedBuchstabWindows

/-! # Integral absolute-error transfer through the exact clipped Buchstab identity -/

namespace Erdos421

open MeasureTheory

theorem logarithmicRoughWindow_cutoff_l1 {W Z K N : ℕ} (hWZ : W ≤ Z)
    (hW : 2 ≤ W) (hZ : Z ≤ 2 ^ K + 1) (hN : 0 < N) (B : ℕ)
    {δ₁ δ₂ X : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hX : 0 < X) :
    (∫ y in Real.log X..Real.log (2 * X),
      |logarithmicRoughWindow B Z δ₁ y - logarithmicRoughWindow B Z δ₂ y|) ≤
      (∫ y in Real.log X..Real.log (2 * X),
        |logarithmicRoughWindow B W δ₁ y - logarithmicRoughWindow B W δ₂ y|) +
      (∫ y in Real.log X..Real.log (2 * X),
        |frozenRoughBuchstabWindow W Z K N B δ₁ y -
          frozenRoughBuchstabWindow W Z K N B δ₂ y|) +
      (∫ y : ℝ, clippedRoughError W Z K N B δ₁ y) +
      (∫ y : ℝ, clippedRoughError W Z K N B δ₂ y) := by
  apply interval_abs_integral_transfer
    ((logarithmicRoughWindow_continuous B Z δ₁).sub
      (logarithmicRoughWindow_continuous B Z δ₂))
    ((logarithmicRoughWindow_continuous B W δ₁).sub
      (logarithmicRoughWindow_continuous B W δ₂))
    ((frozenRoughBuchstabWindow_continuous W Z K N B δ₁).sub
      (frozenRoughBuchstabWindow_continuous W Z K N B δ₂))
    (clippedRoughError_integrable W Z K N B hδ₁)
    (clippedRoughError_integrable W Z K N B hδ₂)
    (clippedRoughError_nonneg W Z K N B hδ₁)
    (clippedRoughError_nonneg W Z K N B hδ₂)
    _ (Real.log_le_log hX (by linarith))
  intro y
  have h₁ := logarithmicRoughWindow_clipped_buchstab hWZ hW hZ hN B δ₁ y
  have h₂ := logarithmicRoughWindow_clipped_buchstab hWZ hW hZ hN B δ₂ y
  simp only [Pi.sub_apply]
  linarith

theorem logarithmicPrimeCofactorWindow_cutoff_l1 (P : Finset ℕ) {W Z K N : ℕ}
    (hWZ : W ≤ Z) (hW : 2 ≤ W) (hZ : Z ≤ 2 ^ K + 1) (hN : 0 < N) (B : ℕ)
    {δ₁ δ₂ X : ℝ} (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hX : 0 < X) :
    (∫ y in Real.log X..Real.log (2 * X),
      |logarithmicPrimeCofactorWindow P B Z δ₁ y -
        logarithmicPrimeCofactorWindow P B Z δ₂ y|) ≤
      (∫ y in Real.log X..Real.log (2 * X),
        |logarithmicPrimeCofactorWindow P B W δ₁ y -
          logarithmicPrimeCofactorWindow P B W δ₂ y|) +
      (∫ y in Real.log X..Real.log (2 * X),
        |frozenCofactorBuchstabWindow P W Z K N B δ₁ y -
          frozenCofactorBuchstabWindow P W Z K N B δ₂ y|) +
      (∫ y : ℝ, clippedCofactorError P W Z K N B δ₁ y) +
      (∫ y : ℝ, clippedCofactorError P W Z K N B δ₂ y) := by
  apply interval_abs_integral_transfer
    ((logarithmicPrimeCofactorWindow_continuous P B Z δ₁).sub
      (logarithmicPrimeCofactorWindow_continuous P B Z δ₂))
    ((logarithmicPrimeCofactorWindow_continuous P B W δ₁).sub
      (logarithmicPrimeCofactorWindow_continuous P B W δ₂))
    ((frozenCofactorBuchstabWindow_continuous P W Z K N B δ₁).sub
      (frozenCofactorBuchstabWindow_continuous P W Z K N B δ₂))
    (clippedCofactorError_integrable P W Z K N B hδ₁)
    (clippedCofactorError_integrable P W Z K N B hδ₂)
    (clippedCofactorError_nonneg P W Z K N B hδ₁)
    (clippedCofactorError_nonneg P W Z K N B hδ₂)
    _ (Real.log_le_log hX (by linarith))
  intro y
  have h₁ := logarithmicPrimeCofactorWindow_clipped_buchstab P hWZ hW hZ hN B δ₁ y
  have h₂ := logarithmicPrimeCofactorWindow_clipped_buchstab P hWZ hW hZ hN B δ₂ y
  simp only [Pi.sub_apply]
  linarith

end Erdos421
