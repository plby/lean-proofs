import Wikipedia.NoExoticSixSphere.SphereAxisDilation

/-! # Exact rational coordinates of the finite polynomial-pinch chart -/

noncomputable section

open Set Function Topology

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem pinchPole_head : pinchPole.val 0 = 1 := by simp [pinchPole, spherePole]

theorem pinchPole_succ (i : Fin 3) : pinchPole.val i.succ = 0 := by
  simp [pinchPole, spherePole]

theorem norm_capVector_sq (v : Vector 3) : ‖capVector v‖ ^ 2 = 1 + ‖v‖ ^ 2 := by
  simpa only [capVector, one_pow] using SphereCylinder.norm_join_sq 2 1 v

theorem capVector_inv_norm_sq (v : Vector 3) :
    ‖capVector v‖⁻¹ * ‖capVector v‖⁻¹ = (1 + ‖v‖ ^ 2)⁻¹ := by
  rw [← mul_inv, ← pow_two, norm_capVector_sq]

theorem gnomonicInverse_succ (v : Vector 3) (i : Fin 3) :
    (gnomonicInverse v).val i.succ = ‖capVector v‖⁻¹ * v i := by
  rw [gnomonicInverse_val]
  rfl

theorem pinchFiniteChart_head (v : Vector 3) :
    (pinchFiniteChart v).val 0 = (1 + ‖v‖ ^ 2)⁻¹ * (1 - ‖v‖ ^ 2) := by
  change (2 * SphereFold.height pinchPole (gnomonicInverse v)) *
    (gnomonicInverse v).val 0 - pinchPole.val 0 = _
  rw [pinchPole_height, gnomonicInverse_head, pinchPole_head, mul_assoc, capVector_inv_norm_sq]
  have hd : 1 + ‖v‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem pinchFiniteChart_succ (v : Vector 3) (i : Fin 3) :
    (pinchFiniteChart v).val i.succ = (1 + ‖v‖ ^ 2)⁻¹ * (2 * v i) := by
  change (2 * SphereFold.height pinchPole (gnomonicInverse v)) *
    (gnomonicInverse v).val i.succ - pinchPole.val i.succ = _
  rw [pinchPole_height, gnomonicInverse_head, gnomonicInverse_succ, pinchPole_succ, sub_zero]
  calc
    _ = (‖capVector v‖⁻¹ * ‖capVector v‖⁻¹) * (2 * v i) := by ring
    _ = _ := by rw [capVector_inv_norm_sq]

theorem pinchFiniteChart_val (v : Vector 3) :
    (pinchFiniteChart v).val =
      (1 + ‖v‖ ^ 2)⁻¹ • SphereCylinder.join 2 (1 - ‖v‖ ^ 2, (2 : ℝ) • v) := by
  ext i
  exact Fin.cases (pinchFiniteChart_head v) (pinchFiniteChart_succ v) i

theorem axisDenominator_finite (c r : ℝ) (hr : 0 ≤ r) :
    axisDenominator c ((1 + r)⁻¹ * (1 - r)) = (1 + r)⁻¹ * (2 * (r + c ^ 2)) := by
  have hd : 1 + r ≠ 0 := by positivity
  dsimp [axisDenominator]
  field_simp
  ring

theorem axisNumerator_finite (c r : ℝ) (hr : 0 ≤ r) :
    axisNumerator c ((1 + r)⁻¹ * (1 - r)) = (1 + r)⁻¹ * (2 * (c ^ 2 - r)) := by
  have hd : 1 + r ≠ 0 := by positivity
  dsimp [axisNumerator]
  field_simp
  ring

end NoExoticSixSphere.SphereSumNeck
