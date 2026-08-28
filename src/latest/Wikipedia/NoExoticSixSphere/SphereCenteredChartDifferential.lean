import Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # The derivative of the centered stereographic target chart -/

noncomputable section

namespace NoExoticSixSphere.SphereCenteredChartDifferential

open Wikipedia.HomotopyGroupsOfSpheres.SphereCenteredCoordinates

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_center (z : UnitSphere E) :
    (Tangent z).orthogonalProjectionOnto z.val = 0 := by
  have h := Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero
    (𝕜 := ℝ) (-z.val)
  simpa only [map_neg, neg_eq_zero] using h

theorem hasFDerivAt_chart (z : UnitSphere E) :
    HasFDerivAt (stereoToFun (-z.val)) (Tangent z).orthogonalProjectionOnto z.val := by
  have hz : ‖z.val‖ = 1 := mem_sphere_zero_iff_norm.mp z.property
  have hi : innerSL ℝ (-z.val) z.val = -1 := by
    simp [innerSL_apply_apply, real_inner_self_eq_norm_sq, hz]
  have hc : DifferentiableAt ℝ (fun y : E ↦ (2 : ℝ) / (1 - innerSL ℝ (-z.val) y))
      z.val := by
    simp only [div_eq_mul_inv]
    exact (differentiableAt_const (2 : ℝ)).mul
      (((differentiableAt_const (1 : ℝ)).sub (innerSL ℝ (-z.val)).differentiableAt).inv
        (by change 1 - innerSL ℝ (-z.val) z.val ≠ 0; rw [hi]; norm_num))
  have h := hc.hasFDerivAt.smul (Tangent z).orthogonalProjectionOnto.hasFDerivAt
  convert! h using 1 <;> try rfl
  ext v : 1
  norm_num [hi, projection_center]

end NoExoticSixSphere.SphereCenteredChartDifferential
