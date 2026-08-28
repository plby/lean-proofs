import Wikipedia.NoExoticSixSphere.SuperlevelAtlas
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# The boundary of the constructed superlevel atlas

The native manifold boundary consists exactly of the zeroes of the actual
defining function, not of a separately specified or transported boundary.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SuperlevelAtlas

variable {B H M K : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup K] [NormedSpace ℝ K]
  {f : M → ℝ} (A : SuperlevelAtlas (K := K) I f)

theorem isInteriorPoint_iff (x : {x : M // 0 ≤ f x}) : letI := A.chartedSpace;
    (ProductHalfSpace.model K).IsInteriorPoint x ↔ 0 < f x.val := by
  let := A.chartedSpace
  change extChartAt (ProductHalfSpace.model K) x x ∈
    interior (range (ProductHalfSpace.model K)) ↔ 0 < f x.val
  rw [ProductHalfSpace.model_interior]
  change 0 < (A.chart x x).val.1 ↔ 0 < f x.val
  rw [A.chart_apply_val x x (A.mem_source x)]
  have hnonneg := (A.sign_iff x x.val (A.mem_source x)).mpr x.property
  have hzero := A.zero_iff x x.val (A.mem_source x)
  constructor
  · intro h
    exact lt_of_le_of_ne x.property (fun hz ↦ (ne_of_gt h) (hzero.mpr hz.symm))
  · intro h
    exact lt_of_le_of_ne hnonneg (fun hz ↦ (ne_of_gt h) (hzero.mp hz.symm))

theorem isBoundaryPoint_iff (x : {x : M // 0 ≤ f x}) : letI := A.chartedSpace;
    (ProductHalfSpace.model K).IsBoundaryPoint x ↔ f x.val = 0 := by
  let := A.chartedSpace
  rw [ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint, A.isInteriorPoint_iff]
  exact not_lt.trans (le_antisymm_iff.trans (and_iff_left x.property)).symm

end NoExoticSixSphere.SuperlevelAtlas
