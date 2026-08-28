import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Interior points in an arbitrary actual extended chart

The chart target is relatively open in the model range. Thus its interior
criterion at a chart point agrees with the interior of the whole model range.
-/

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem isInteriorPoint_iff_extChartAt_mem_interior_range (x y : M)
    (hy : y ∈ (extChartAt I x).source) :
    I.IsInteriorPoint y ↔ extChartAt I x y ∈ interior (range I) := by
  have hy' : y ∈ (chartAt H x).source := by simpa only [extChartAt_source] using hy
  rw [I.isInteriorPoint_iff_of_mem_atlas (n := ∞) (by simp) (chart_mem_atlas H x) hy']
  constructor
  · intro h
    exact (chartAt H x).interior_extend_target_subset_interior_range (I := I) h
  · intro h
    exact (chartAt H x).mem_interior_extend_target ((chartAt H x).map_source hy') h

end NoExoticSixSphere
