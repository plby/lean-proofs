import Wikipedia.HopfProblem.TriangleBoundaryCoordinates
import Wikipedia.HopfProblem.TriangleUniformizationGluingRemovableCharts
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Continuous removability of the actual geodesic curves

Vertical lines and unit circles with real centers are continuously
removable in the upper half-plane. The vertical coordinate is affine;
the circular coordinate is a real translate of the proved analytic
Möbius boundary chart. Its only source pole is real, so the chart contains
the whole upper half-plane without any boundary regularity assumption.
-/

noncomputable section

open Complex Set
open Wikipedia.HopfProblem.SpecialPeriods.Triangle

namespace Wikipedia.HopfProblem.TriangleUniformizationGluing

private def verticalLineChart (a : ℝ) : ℂ ≃ₜ ℂ where
  toFun z := I * (z - (a : ℂ))
  invFun w := -I * w + (a : ℂ)
  left_inv z := by ring_nf; simp
  right_inv w := by ring_nf; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem verticalLineChart_differentiable (a : ℝ) :
    Differentiable ℂ (verticalLineChart a) :=
  fun _ => (differentiableAt_const I).mul (differentiableAt_id.sub_const _)

private theorem verticalLineChart_symm_differentiable (a : ℝ) :
    Differentiable ℂ (verticalLineChart a).symm :=
  fun _ => ((differentiableAt_const (-I)).mul differentiableAt_id).add_const _

/-- The portion of any vertical line in the upper half-plane is
continuously removable there. -/
theorem continuousRemovable_verticalLine (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet {z : ℂ | z.re = a} := by
  have h := continuousRemovable_preimage_realAxis
    (verticalLineChart a).toOpenPartialHomeomorph UpperHalfPlane.upperHalfPlaneSet
    (fun z _ => mem_univ z)
    (verticalLineChart_differentiable a).differentiableOn
    (verticalLineChart_symm_differentiable a).differentiableOn
  apply h.mono_set
  intro z hz
  change (I * (z - (a : ℂ))).im = 0
  simpa using sub_eq_zero.mpr hz

private def translatedUnitCircleChart (a : ℝ) : OpenPartialHomeomorph ℂ ℂ :=
  (Homeomorph.subRight ((a : ℂ) + 1)).transOpenPartialHomeomorph circleBoundaryChart

private theorem upperHalfPlane_subset_translatedUnitCircleChart_source (a : ℝ) :
    UpperHalfPlane.upperHalfPlaneSet ⊆ (translatedUnitCircleChart a).source := by
  intro z hz
  change z - ((a : ℂ) + 1) + 2 ≠ 0
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_im, Complex.one_im,
    Complex.im_ofNat, add_zero, sub_zero, Complex.zero_im] at hi
  exact (show 0 < z.im from hz).ne' hi

private theorem translatedUnitCircleChart_differentiableOn (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart a)
      (translatedUnitCircleChart a).source := by
  intro z hz
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => circleStraighten (w - ((a : ℂ) + 1))) _ z
  exact ((circleStraighten_analyticOnNhd _ hz).differentiableAt.comp z
    (differentiableAt_id.sub_const _)).differentiableWithinAt

private theorem translatedUnitCircleChart_symm_differentiableOn (a : ℝ) :
    DifferentiableOn ℂ (translatedUnitCircleChart a).symm
      (translatedUnitCircleChart a).target := by
  intro z hz
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => circleUnstraighten w + ((a : ℂ) + 1)) _ z
  exact
    ((circleUnstraighten_analyticOnNhd z hz).differentiableAt.add_const _).differentiableWithinAt

private theorem translatedUnitCircleChart_im_eq_zero_iff (a : ℝ) {z : ℂ}
    (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) :
    (translatedUnitCircleChart a z).im = 0 ↔ ‖z - (a : ℂ)‖ = 1 := by
  change (circleStraighten (z - ((a : ℂ) + 1))).im = 0 ↔ _
  rw [circleStraighten_im_eq_zero_iff (z := z - ((a : ℂ) + 1))
    (upperHalfPlane_subset_translatedUnitCircleChart_source a hz)]
  rw [show z - ((a : ℂ) + 1) + 1 = z - (a : ℂ) by ring]

/-- The upper semicircle of any unit circle with real center is
continuously removable in the upper half-plane. -/
theorem continuousRemovable_unitCircle (a : ℝ) :
    ContinuousRemovable UpperHalfPlane.upperHalfPlaneSet
      {z : ℂ | ‖z - (a : ℂ)‖ = 1} := by
  have h := continuousRemovable_preimage_realAxis (translatedUnitCircleChart a)
    UpperHalfPlane.upperHalfPlaneSet
    (upperHalfPlane_subset_translatedUnitCircleChart_source a)
    (translatedUnitCircleChart_differentiableOn a)
    (translatedUnitCircleChart_symm_differentiableOn a)
  exact h.mono_set_on (fun z hz hnorm =>
    (translatedUnitCircleChart_im_eq_zero_iff a hz).mpr hnorm)

end Wikipedia.HopfProblem.TriangleUniformizationGluing
