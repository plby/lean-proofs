import ErdosProblems.Erdos556.CubeQuadratic

/-!
# Transferring weight between intersecting profiles

Along a transfer between intersecting profiles the quadratic term
vanishes, so the energy is affine. One of the two full transfers
therefore cannot increase the energy.
-/

namespace Erdos556

def cubeShift (w : CubeProfile → ℝ) (p q : CubeProfile) (t : ℝ) : CubeProfile → ℝ :=
  (w + Pi.single p t) + Pi.single q (-t)

def cubeTransfer (w : CubeProfile → ℝ) (p q : CubeProfile) : CubeProfile → ℝ :=
  cubeShift w p q (w q)

theorem cubeEnergy_shift (w : CubeProfile → ℝ) (p q : CubeProfile) (t : ℝ)
    (hpq : cubeOverlap p q = 1) :
    cubeEnergy (cubeShift w p q t) = cubeEnergy w + t * (cubeGradient w p - cubeGradient w q) := by
  rw [cubeShift, cubeEnergy_add_single, cubeEnergy_add_single, cubeGradient_add_single,
    cubeOverlap_symm q p, hpq]
  ring

theorem cubeGradient_shift_difference (w : CubeProfile → ℝ) (p q : CubeProfile) (t : ℝ)
    (hpq : cubeOverlap p q = 1) :
    cubeGradient (cubeShift w p q t) p - cubeGradient (cubeShift w p q t) q =
      cubeGradient w p - cubeGradient w q := by
  simp only [cubeShift, cubeGradient_add_single, cubeOverlap_self,
    cubeOverlap_symm q p, hpq]
  ring

theorem cubeTransfer_at_source (w : CubeProfile → ℝ) (p q : CubeProfile) (hpq : p ≠ q) :
    cubeTransfer w p q q = 0 := by
  classical
  simp [cubeTransfer, cubeShift, Pi.single_apply, hpq, Ne.symm hpq]

theorem cubeTransfer_at_target (w : CubeProfile → ℝ) (p q : CubeProfile) (hpq : p ≠ q) :
    cubeTransfer w p q p = w p + w q := by
  classical
  simp [cubeTransfer, cubeShift, Pi.single_apply, hpq, Ne.symm hpq]

theorem cubeTransfer_at_other (w : CubeProfile → ℝ) (p q r : CubeProfile)
    (hrp : r ≠ p) (hrq : r ≠ q) : cubeTransfer w p q r = w r := by
  classical
  simp [cubeTransfer, cubeShift, Pi.single_apply, hrp, hrq, Ne.symm hrp, Ne.symm hrq]

theorem cubeTransfer_nonincrease_or_reverse (w : CubeProfile → ℝ) (p q : CubeProfile)
    (hp : 0 ≤ w p) (hq : 0 ≤ w q) (hpq : cubeOverlap p q = 1) :
    cubeEnergy (cubeTransfer w p q) ≤ cubeEnergy w ∨
      cubeEnergy (cubeTransfer w q p) ≤ cubeEnergy w := by
  by_cases hgrad : cubeGradient w p ≤ cubeGradient w q
  · left
    rw [cubeTransfer, cubeEnergy_shift w p q (w q) hpq]
    have h := mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hgrad)
    linarith
  · right
    have hqp : cubeOverlap q p = 1 := (cubeOverlap_symm q p).trans hpq
    rw [cubeTransfer, cubeEnergy_shift w q p (w p) hqp]
    have h := mul_nonpos_of_nonneg_of_nonpos hp (by linarith : cubeGradient w q - cubeGradient w p ≤ 0)
    linarith

#print axioms cubeEnergy_shift
#print axioms cubeTransfer_nonincrease_or_reverse

end Erdos556
