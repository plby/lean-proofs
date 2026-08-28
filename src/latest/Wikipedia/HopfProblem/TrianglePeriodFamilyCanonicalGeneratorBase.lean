import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalAutomorphy
import Wikipedia.HopfProblem.SpecialPeriodsTriangleGeometry
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Base derivatives for the actual triangle generators

The source generators act by `-1 / (z + 1)` and `-1 - 1 / (z + width)`;
the clockwise cusp generator is the translation `z - width`.  This file
differentiates those actions in the installed upper-half-plane chart and
the inherited open-subspace charts of the actual regular triangle locus.
All chart expressions are identified on their open targets before taking
derivatives; no formula for a chart inverse outside its target is assumed.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane
open scoped ContDiff

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

open SpecialPeriods

section CoordinateFormula

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
    [MulAction TriangleGroup B]

/-- A proved formula for an actual group action gives its chart expression
on every source-chart target. -/
theorem baseActionCoordinate_eq_of_formula
    (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)
    (D : Data ℂ B) (g : TriangleGroup) (a : B) (F : ℂ → ℂ)
    (hF : ∀ x : B, coordinate (g • x) = F (coordinate x))
    {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    baseActionCoordinate coordinate D g a z = F z := by
  change coordinate (g • (chartAt ℂ a).symm z) = F z
  rw [hF, base_chart_inverse_coordinate coordinate hcoordinate a hz]

/-- The same exact chart formula holds on a neighborhood, so it can be
used to compute the genuine derivative of the coordinate expression. -/
theorem baseActionCoordinate_eventually_of_formula
    (coordinate : B → ℂ) (hcoordinate : ∀ a x : B, chartAt ℂ a x = coordinate x)
    (D : Data ℂ B) (g : TriangleGroup) (a : B) (F : ℂ → ℂ)
    (hF : ∀ x : B, coordinate (g • x) = F (coordinate x))
    {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    baseActionCoordinate coordinate D g a =ᶠ[𝓝 z] F := by
  filter_upwards [(chartAt ℂ a).open_target.mem_nhds hz] with w hw
  exact baseActionCoordinate_eq_of_formula coordinate hcoordinate D g a F hF hw

end CoordinateFormula

theorem upperHalfPlane_chart_target_im_pos (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) : 0 < z.im := by
  have he := base_chart_inverse_coordinate (fun x : ℍ => (x : ℂ))
    upperHalfPlane_chart_apply a hz
  rw [← he]
  exact ((chartAt ℂ a).symm z).im_pos

theorem regularPoint_chart_target_im_pos (a : TriangleRegularPoint) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) : 0 < z.im := by
  have he := base_chart_inverse_coordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
    regularPoint_chart_apply a hz
  rw [← he]
  exact ((chartAt ℂ a).symm z).val.im_pos

theorem coordinate_add_real_ne_zero {z : ℂ} (hz : 0 < z.im) (c : ℝ) :
    z + (c : ℂ) ≠ 0 := by
  intro h
  have hi : z.im = 0 := by simpa using congrArg Complex.im h
  exact (ne_of_gt hz) hi

theorem neg_inv_shift_hasDerivAt {z : ℂ} (c : ℂ) (hz : z + c ≠ 0) :
    HasDerivAt (fun w : ℂ => -(w + c)⁻¹) ((z + c) ^ 2)⁻¹ z := by
  simpa [neg_div, one_div] using
    (((hasDerivAt_id z).add_const c).inv hz).const_sub 0

theorem neg_one_sub_inv_shift_hasDerivAt {z : ℂ} (c : ℂ) (hz : z + c ≠ 0) :
    HasDerivAt (fun w : ℂ => -1 - (w + c)⁻¹) ((z + c) ^ 2)⁻¹ z := by
  simpa [neg_div, one_div] using
    (((hasDerivAt_id z).add_const c).inv hz).const_sub (-1)

section UpperHalfPlane

attribute [local instance] triangleGeometricAction

theorem upperHalfPlane_generator₁_hasDerivAt (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleGenerator₁ a)
      ((z + 1) ^ 2)⁻¹ z := by
  have hn : z + 1 ≠ 0 := by
    simpa using coordinate_add_real_ne_zero (upperHalfPlane_chart_target_im_pos a hz) 1
  apply (neg_inv_shift_hasDerivAt 1 hn).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : ℍ => (x : ℂ)) upperHalfPlane_chart_apply D triangleGenerator₁ a
    (fun w : ℂ => -(w + 1)⁻¹) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleGenerator₁ x : ℂ) = _
  rw [triangleGeometricRepresentation_generator₁_apply, Triangle.generatorOneSL_smul_coe]

theorem upperHalfPlane_generator₂_hasDerivAt (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleGenerator₂ a)
      ((z + (Triangle.width : ℂ)) ^ 2)⁻¹ z := by
  have hn := coordinate_add_real_ne_zero (upperHalfPlane_chart_target_im_pos a hz) Triangle.width
  apply (neg_one_sub_inv_shift_hasDerivAt (Triangle.width : ℂ) hn).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : ℍ => (x : ℂ)) upperHalfPlane_chart_apply D triangleGenerator₂ a
    (fun w : ℂ => -1 - (w + (Triangle.width : ℂ))⁻¹) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleGenerator₂ x : ℂ) = _
  rw [triangleGeometricRepresentation_generator₂_apply, Triangle.generatorTwoSL_smul_coe]

theorem upperHalfPlane_cusp_hasDerivAt (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleCuspGenerator a)
      1 z := by
  apply ((hasDerivAt_id z).sub_const (Triangle.width : ℂ)).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : ℍ => (x : ℂ)) upperHalfPlane_chart_apply D triangleCuspGenerator a
    (fun w : ℂ => w - (Triangle.width : ℂ)) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleCuspGenerator x : ℂ) = _
  exact triangleGeometricRepresentation_cusp_coe x

theorem upperHalfPlane_generator₁_deriv (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleGenerator₁ a) z =
      ((z + 1) ^ 2)⁻¹ :=
  (upperHalfPlane_generator₁_hasDerivAt D a hz).deriv

theorem upperHalfPlane_generator₂_deriv (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleGenerator₂ a) z =
      ((z + (Triangle.width : ℂ)) ^ 2)⁻¹ :=
  (upperHalfPlane_generator₂_hasDerivAt D a hz).deriv

theorem upperHalfPlane_cusp_deriv (D : Data ℂ ℍ) (a : ℍ) {z : ℂ}
    (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : ℍ => (x : ℂ)) D triangleCuspGenerator a) z = 1 :=
  (upperHalfPlane_cusp_hasDerivAt D a hz).deriv

end UpperHalfPlane

section RegularPoint

theorem regularPoint_generator₁_hasDerivAt (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleGenerator₁ a) ((z + 1) ^ 2)⁻¹ z := by
  have hn : z + 1 ≠ 0 := by
    simpa using coordinate_add_real_ne_zero (regularPoint_chart_target_im_pos a hz) 1
  apply (neg_inv_shift_hasDerivAt 1 hn).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : TriangleRegularPoint => (x.val : ℂ)) regularPoint_chart_apply
    D triangleGenerator₁ a (fun w : ℂ => -(w + 1)⁻¹) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleGenerator₁ x.val : ℂ) = _
  rw [triangleGeometricRepresentation_generator₁_apply, Triangle.generatorOneSL_smul_coe]

theorem regularPoint_generator₂_hasDerivAt (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleGenerator₂ a) ((z + (Triangle.width : ℂ)) ^ 2)⁻¹ z := by
  have hn := coordinate_add_real_ne_zero (regularPoint_chart_target_im_pos a hz) Triangle.width
  apply (neg_one_sub_inv_shift_hasDerivAt (Triangle.width : ℂ) hn).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : TriangleRegularPoint => (x.val : ℂ)) regularPoint_chart_apply
    D triangleGenerator₂ a (fun w : ℂ => -1 - (w + (Triangle.width : ℂ))⁻¹) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleGenerator₂ x.val : ℂ) = _
  rw [triangleGeometricRepresentation_generator₂_apply, Triangle.generatorTwoSL_smul_coe]

theorem regularPoint_cusp_hasDerivAt (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    HasDerivAt (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleCuspGenerator a) 1 z := by
  apply ((hasDerivAt_id z).sub_const (Triangle.width : ℂ)).congr_of_eventuallyEq
  apply baseActionCoordinate_eventually_of_formula
    (fun x : TriangleRegularPoint => (x.val : ℂ)) regularPoint_chart_apply
    D triangleCuspGenerator a (fun w : ℂ => w - (Triangle.width : ℂ)) ?_ hz
  intro x
  change (triangleGeometricRepresentation triangleCuspGenerator x.val : ℂ) = _
  exact triangleGeometricRepresentation_cusp_coe x.val

theorem regularPoint_generator₁_deriv (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleGenerator₁ a) z = ((z + 1) ^ 2)⁻¹ :=
  (regularPoint_generator₁_hasDerivAt D a hz).deriv

theorem regularPoint_generator₂_deriv (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleGenerator₂ a) z = ((z + (Triangle.width : ℂ)) ^ 2)⁻¹ :=
  (regularPoint_generator₂_hasDerivAt D a hz).deriv

theorem regularPoint_cusp_deriv (D : Data ℂ TriangleRegularPoint)
    (a : TriangleRegularPoint) {z : ℂ} (hz : z ∈ (chartAt ℂ a).target) :
    deriv (baseActionCoordinate (fun x : TriangleRegularPoint => (x.val : ℂ))
      D triangleCuspGenerator a) z = 1 :=
  (regularPoint_cusp_hasDerivAt D a hz).deriv

end RegularPoint

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
