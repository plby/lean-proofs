import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
import Mathlib.Analysis.Complex.Basic

/-!
# Centered coordinates in actual complex-surface charts

An actual extended manifold chart, translated by its value at the base
point and identified with `ℂ × ℂ` by a continuous complex-linear
equivalence, gives centered surface coordinates.  The inverse identities
below retain the source and target conditions of the original chart.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (e : (ℂ × ℂ) ≃L[ℂ] E) (x : M)

/-- The given manifold chart expressed in centered complex surface coordinates. -/
def centeredChart (y : M) : ℂ × ℂ :=
  e.symm (extChartAt I x y - extChartAt I x x)

/-- The actual chart inverse after undoing the affine coordinate change. -/
def centeredChartInverse (z : ℂ × ℂ) : M :=
  (extChartAt I x).symm (extChartAt I x x + e z)

@[simp] theorem centeredChart_self : centeredChart I e x x = 0 := by
  simp [centeredChart]

@[simp] theorem centeredChartInverse_zero : centeredChartInverse I e x 0 = x := by
  simp only [centeredChartInverse, map_zero, add_zero, extChartAt_to_inv]

/-- The true source of the original chart is a neighborhood of its center. -/
theorem centeredChart_source_mem_nhds : (extChartAt I x).source ∈ 𝓝 x :=
  extChartAt_source_mem_nhds x

theorem centeredChart_continuousAt {y : M} (hy : y ∈ (extChartAt I x).source) :
    ContinuousAt (centeredChart I e x) y :=
  e.symm.continuous.continuousAt.comp
    ((continuousAt_extChartAt' hy).sub continuousAt_const)

/-- Centered coordinates tend to zero at the original manifold point. -/
theorem centeredChart_tendsto :
    Tendsto (centeredChart I e x) (𝓝 x) (𝓝 (0 : ℂ × ℂ)) := by
  simpa only [centeredChart_self] using
    (centeredChart_continuousAt I e x (mem_extChartAt_source x)).tendsto

/-- The affine inverse really recovers points in the original chart source. -/
theorem centeredChartInverse_left {y : M} (hy : y ∈ (extChartAt I x).source) :
    centeredChartInverse I e x (centeredChart I e x y) = y := by
  unfold centeredChartInverse centeredChart
  rw [e.apply_symm_apply, add_comm, sub_add_cancel]
  exact (extChartAt I x).left_inv hy

/-- Within the true chart source, only its center has zero centered coordinates. -/
theorem centeredChart_eq_zero_iff {y : M} (hy : y ∈ (extChartAt I x).source) :
    centeredChart I e x y = 0 ↔ y = x := by
  constructor
  · intro h
    calc
      y = centeredChartInverse I e x (centeredChart I e x y) :=
        (centeredChartInverse_left I e x hy).symm
      _ = x := by rw [h, centeredChartInverse_zero]
  · intro h
    rw [h, centeredChart_self]

/-- The other inverse identity retains the translated original target condition. -/
theorem centeredChartInverse_right {z : ℂ × ℂ}
    (hz : extChartAt I x x + e z ∈ (extChartAt I x).target) :
    centeredChart I e x (centeredChartInverse I e x z) = z := by
  unfold centeredChart centeredChartInverse
  rw [(extChartAt I x).right_inv hz, add_sub_cancel_left]
  exact e.symm_apply_apply z

/-- Undoing the affine change tends to the original chart coordinate. -/
theorem centeredChartAffineInverse_tendsto :
    Tendsto (fun z : ℂ × ℂ => extChartAt I x x + e z)
      (𝓝 0) (𝓝 (extChartAt I x x)) := by
  have h : ContinuousAt (fun z : ℂ × ℂ => extChartAt I x x + e z) 0 :=
    continuousAt_const.add e.continuous.continuousAt
  simpa only [map_zero, add_zero] using
    h.tendsto

/-- The actual centered chart inverse tends to the original manifold point. -/
theorem centeredChartInverse_tendsto :
    Tendsto (centeredChartInverse I e x) (𝓝 (0 : ℂ × ℂ)) (𝓝 x) := by
  have h : Tendsto (extChartAt I x).symm (𝓝 (extChartAt I x x)) (𝓝 x) := by
    simpa only [extChartAt_to_inv] using (continuousAt_extChartAt_symm (I := I) x).tendsto
  exact h.comp (centeredChartAffineInverse_tendsto I e x)

/-- In a boundaryless model, the translated original target contains a full
neighborhood of zero in the complex plane squared. -/
theorem centeredChart_target_mem_nhds [I.Boundaryless] :
    {z : ℂ × ℂ | extChartAt I x x + e z ∈ (extChartAt I x).target} ∈ 𝓝 0 :=
  (centeredChartAffineInverse_tendsto I e x) (extChartAt_target_mem_nhds (I := I) x)

end Wikipedia.HopfProblem.HolomorphicMeromorphic.PolarSurfaceReduced
