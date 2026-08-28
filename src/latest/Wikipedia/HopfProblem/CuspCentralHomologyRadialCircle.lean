import Wikipedia.HopfProblem.CuspCentralHomologyRadialGauge
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# The literal hexagonal frontier is a circle

The homeomorphism is constructed by the coordinate identification of the real
plane with `ℂ`, followed by normalization.  Its inverse uses the actual
hexagonal gauge; no disk or collar homeomorphism is assumed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspCentralHomology.Radial

open CuspHoneycombTiling

/-- The coordinate identification `x ↦ x₀ + i x₁`, with inverse given by real
and imaginary parts. -/
def circlePlaneComplexEquiv : Plane ≃L[ℝ] ℂ where
  toFun x := ⟨x 0, x 1⟩
  invFun z := ![z.re, z.im]
  left_inv x := by
    funext i
    fin_cases i <;> rfl
  right_inv z := by
    cases z
    rfl
  map_add' _ _ := rfl
  map_smul' c x := by
    apply Complex.ext <;> simp
  continuous_toFun := by
    simp only [Complex.mk_eq_add_mul_I]
    fun_prop
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> fun_prop

@[simp] theorem circlePlaneComplexEquiv_re (x : Plane) :
    (circlePlaneComplexEquiv x).re = x 0 := rfl

@[simp] theorem circlePlaneComplexEquiv_im (x : Plane) :
    (circlePlaneComplexEquiv x).im = x 1 := rfl

@[simp] theorem circlePlaneComplexEquiv_symm_apply (z : ℂ) :
    circlePlaneComplexEquiv.symm z = ![z.re, z.im] := rfl

theorem circleFrontier_ne_zero (x : frontier baseCell) : (x : Plane) ≠ 0 := by
  intro hx
  have hg := (mem_frontier_baseCell_iff (x : Plane)).mp x.property
  exact zero_ne_one (by simpa only [hx, cellGauge_zero] using hg)

theorem circleFrontierComplex_ne_zero (x : frontier baseCell) :
    circlePlaneComplexEquiv (x : Plane) ≠ 0 := by
  intro hx
  exact circleFrontier_ne_zero x (circlePlaneComplexEquiv.map_eq_zero_iff.mp hx)

/-- Radial normalization of the literal cell frontier in complex coordinates. -/
def frontierCircleForward (x : frontier baseCell) : Circle :=
  ⟨NormedSpace.normalize (circlePlaneComplexEquiv (x : Plane)),
    mem_sphere_zero_iff_norm.mpr
      (NormedSpace.norm_normalize (circleFrontierComplex_ne_zero x))⟩

@[simp] theorem frontierCircleForward_coe (x : frontier baseCell) :
    (frontierCircleForward x : ℂ) =
      ‖circlePlaneComplexEquiv (x : Plane)‖⁻¹ • circlePlaneComplexEquiv (x : Plane) := rfl

theorem frontierCircleForward_continuous : Continuous frontierCircleForward := by
  apply Continuous.subtype_mk
  have h : Continuous (fun x : frontier baseCell => circlePlaneComplexEquiv (x : Plane)) :=
    circlePlaneComplexEquiv.continuous.comp continuous_subtype_val
  exact (h.norm.inv₀ fun x => norm_ne_zero_iff.mpr
    (circleFrontierComplex_ne_zero x)).smul h

theorem circleComplexPlane_ne_zero (z : Circle) :
    circlePlaneComplexEquiv.symm (z : ℂ) ≠ 0 := by
  intro hz
  exact z.coe_ne_zero (circlePlaneComplexEquiv.symm.map_eq_zero_iff.mp hz)

theorem circleComplexPlaneGauge_pos (z : Circle) :
    0 < cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)) :=
  (cellGauge_pos_iff _).mpr (circleComplexPlane_ne_zero z)

/-- The point of the literal hexagonal frontier on the ray through a circle
point, obtained by division by the hexagonal gauge. -/
def frontierCircleInverse (z : Circle) : frontier baseCell :=
  ⟨(cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ •
      circlePlaneComplexEquiv.symm (z : ℂ),
    (mem_frontier_baseCell_iff _).mpr (by
      rw [cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (cellGauge_nonneg _)),
        inv_mul_cancel₀ (ne_of_gt (circleComplexPlaneGauge_pos z))])⟩

@[simp] theorem frontierCircleInverse_coe (z : Circle) :
    (frontierCircleInverse z : Plane) =
      (cellGauge (circlePlaneComplexEquiv.symm (z : ℂ)))⁻¹ •
        circlePlaneComplexEquiv.symm (z : ℂ) := rfl

theorem frontierCircleInverse_continuous : Continuous frontierCircleInverse := by
  apply Continuous.subtype_mk
  have h : Continuous (fun z : Circle => circlePlaneComplexEquiv.symm (z : ℂ)) :=
    circlePlaneComplexEquiv.symm.continuous.comp continuous_subtype_val
  exact ((cellGauge_continuous.comp h).inv₀ fun z =>
    ne_of_gt (circleComplexPlaneGauge_pos z)).smul h

@[simp] theorem frontierCircleInverse_forward (x : frontier baseCell) :
    frontierCircleInverse (frontierCircleForward x) = x := by
  apply Subtype.ext
  change (cellGauge (circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ)))⁻¹ •
    circlePlaneComplexEquiv.symm (frontierCircleForward x : ℂ) = (x : Plane)
  rw [frontierCircleForward_coe, map_smul,
    circlePlaneComplexEquiv.symm_apply_apply,
    cellGauge_smul_of_nonneg _ (inv_nonneg.mpr (norm_nonneg _)),
    (mem_frontier_baseCell_iff _).mp x.property, mul_one, inv_inv, smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr (circleFrontierComplex_ne_zero x)), one_smul]

@[simp] theorem frontierCircleForward_inverse (z : Circle) :
    frontierCircleForward (frontierCircleInverse z) = z := by
  apply Circle.ext
  change NormedSpace.normalize (circlePlaneComplexEquiv (frontierCircleInverse z : Plane)) =
    (z : ℂ)
  rw [frontierCircleInverse_coe, map_smul, circlePlaneComplexEquiv.apply_symm_apply,
    NormedSpace.normalize_smul_of_pos (inv_pos.mpr (circleComplexPlaneGauge_pos z))]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one z.norm_coe

/-- The literal frontier of the central honeycomb cell is homeomorphic to the
standard complex unit circle, by explicit radial formulas in both directions. -/
def frontierCellCircleHomeomorph : frontier baseCell ≃ₜ Circle where
  toFun := frontierCircleForward
  invFun := frontierCircleInverse
  left_inv := frontierCircleInverse_forward
  right_inv := frontierCircleForward_inverse
  continuous_toFun := frontierCircleForward_continuous
  continuous_invFun := frontierCircleInverse_continuous

@[simp] theorem frontierCellCircleHomeomorph_coe (x : frontier baseCell) :
    (frontierCellCircleHomeomorph x : ℂ) =
      ‖circlePlaneComplexEquiv (x : Plane)‖⁻¹ • circlePlaneComplexEquiv (x : Plane) := rfl

@[simp] theorem frontierCellCircleHomeomorph_symm_coe (z : Circle) :
    (frontierCellCircleHomeomorph.symm z : Plane) =
      (cellGauge ![(z : ℂ).re, (z : ℂ).im])⁻¹ • ![(z : ℂ).re, (z : ℂ).im] := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.Radial
