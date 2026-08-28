import Wikipedia.HopfProblem.DegreeCollapseCappedMiddleIntersections
import Wikipedia.SmoothSixDPoincare.MorseCoreCellAttachment

/-! # Both actual coordinate core disks of a native middle handle

The negative disk and positive disk use the same inverse Morse chart and
the original radius. Their boundaries are exactly the original attaching
and belt spheres. Their entire images lie in the appropriate basins of
the same native flow, and only the origin maps to the critical point.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.CoreDisks

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

theorem scaled_norm_le {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]
    (u : closedBall (0 : N) 1) : ‖d.radius • (u : N)‖ ≤ d.radius := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos]
  have hu := mem_closedBall_zero_iff.mp u.property
  nlinarith [d.radius_pos]

def negativeFun (u : d.chart.NegativeCoordinates) : M :=
  d.chart.splitChart.symm (d.radius • u, 0)

def positiveFun (u : d.chart.PositiveCoordinates) : M :=
  d.chart.splitChart.symm (0, d.radius • u)

theorem negative_target (u : closedBall (0 : d.chart.NegativeCoordinates) 1) :
    (d.radius • (u : d.chart.NegativeCoordinates), (0 : d.chart.PositiveCoordinates)) ∈
      d.chart.splitChart.target := by
  apply d.block
  constructor
  · exact mem_closedBall_zero_iff.mpr ((scaled_norm_le d u).trans (by linarith [d.radius_pos]))
  · exact mem_closedBall_self (by linarith [d.radius_pos])

theorem positive_target (u : closedBall (0 : d.chart.PositiveCoordinates) 1) :
    ((0 : d.chart.NegativeCoordinates), d.radius • (u : d.chart.PositiveCoordinates)) ∈
      d.chart.splitChart.target := by
  apply d.block
  constructor
  · exact mem_closedBall_self (by linarith [d.radius_pos])
  · exact mem_closedBall_zero_iff.mpr ((scaled_norm_le d u).trans (by linarith [d.radius_pos]))

def negativeDisk : C(closedBall (0 : d.chart.NegativeCoordinates) 1, M) := by
  refine ⟨fun u => negativeFun d u.val, ?_⟩
  have hc : Continuous (fun u : closedBall (0 : d.chart.NegativeCoordinates) 1 =>
      (d.radius • u.val, (0 : d.chart.PositiveCoordinates))) :=
    by fun_prop
  exact d.chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hc
    (negative_target d)

def positiveDisk : C(closedBall (0 : d.chart.PositiveCoordinates) 1, M) := by
  refine ⟨fun u => positiveFun d u.val, ?_⟩
  have hc : Continuous (fun u : closedBall (0 : d.chart.PositiveCoordinates) 1 =>
      ((0 : d.chart.NegativeCoordinates), d.radius • u.val)) :=
    by fun_prop
  exact d.chart.splitChart.contMDiffOn_invFun.continuousOn.comp_continuous hc
    (positive_target d)

theorem negative_coords (u : closedBall (0 : d.chart.NegativeCoordinates) 1) :
    d.chart.splitChart (negativeDisk d u) = (d.radius • u.val, 0) :=
  d.chart.splitChart.right_inv' (negative_target d u)

theorem positive_coords (u : closedBall (0 : d.chart.PositiveCoordinates) 1) :
    d.chart.splitChart (positiveDisk d u) = (0, d.radius • u.val) :=
  d.chart.splitChart.right_inv' (positive_target d u)

theorem negative_zero : negativeFun d 0 = p := by
  change d.chart.splitChart.symm (d.radius • 0, 0) = p
  rw [smul_zero]
  change d.chart.splitChart.symm 0 = p
  rw [← d.chart.splitChart_center]
  exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source

theorem positive_zero : positiveFun d 0 = p := by
  change d.chart.splitChart.symm (0, d.radius • 0) = p
  rw [smul_zero]
  change d.chart.splitChart.symm 0 = p
  rw [← d.chart.splitChart_center]
  exact d.chart.splitChart.left_inv' d.chart.splitChart_mem_source

theorem negative_injective : Injective (negativeDisk d) := by
  intro u v huv
  have h := congrArg (fun x => (d.chart.splitChart x).1) huv
  rw [negative_coords, negative_coords] at h
  exact Subtype.ext ((smul_right_injective _ d.radius_pos.ne') h)

theorem positive_injective : Injective (positiveDisk d) := by
  intro u v huv
  have h := congrArg (fun x => (d.chart.splitChart x).2) huv
  rw [positive_coords, positive_coords] at h
  exact Subtype.ext ((smul_right_injective _ d.radius_pos.ne') h)

theorem negative_boundary (u : sphere (0 : d.chart.NegativeCoordinates) 1) :
    negativeDisk d ⟨u.val, sphere_subset_closedBall u.property⟩ =
      (d.surgery.attachingSphere u).val := by
  rw [d.attaching_eq, d.chart.attachingCoreMap_coe]
  rfl

theorem positive_boundary (u : sphere (0 : d.chart.PositiveCoordinates) 1) :
    positiveDisk d ⟨u.val, sphere_subset_closedBall u.property⟩ =
      (d.surgery.beltSphere u).val := by
  rw [d.belt_eq, d.chart.beltCoreMap_coe]
  rfl

theorem negativeDisk_eq_coreMap : negativeDisk d = d.coreMap := by
  apply ContinuousMap.ext
  intro u
  change d.chart.splitChart.symm (d.radius • u.val, 0) =
    d.chart.splitChart.symm
      ((d.radius * Real.sqrt (1 + ‖(0 : d.chart.PositiveCoordinates)‖ ^ 2)) • u.val,
        d.radius • (0 : d.chart.PositiveCoordinates))
  simp

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.CoreDisks

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

theorem negativeDisk_descending (p : criticalPoints E D.function)
    (u : closedBall (0 : (D.windows.data p).chart.NegativeCoordinates) 1) :
    Tendsto (fun t => D.windows.flow t (CoreDisks.negativeDisk (D.windows.data p) u))
      atBot (𝓝 p.val) := by
  let d := D.windows.data p
  have hcoords := d.chart.splitChart.right_inv' (CoreDisks.negative_target d u)
  apply native_morse_negative_plane_limit d.chart (D.windows.smooth.of_le (by simp))
    D.windows.flow D.windows.integral (show 0 < 2 * d.radius by linarith [d.radius_pos])
      d.block (D.windows.model_germ p)
        (d.chart.splitChart.map_target' (CoreDisks.negative_target d u))
  · rw [hcoords]
    exact (CoreDisks.scaled_norm_le d u).trans_lt (by linarith [d.radius_pos])
  · rw [hcoords]

theorem positiveDisk_ascending (p : criticalPoints E D.function)
    (u : closedBall (0 : (D.windows.data p).chart.PositiveCoordinates) 1) :
    Tendsto (fun t => D.windows.flow t (CoreDisks.positiveDisk (D.windows.data p) u))
      atTop (𝓝 p.val) := by
  let d := D.windows.data p
  have hcoords := d.chart.splitChart.right_inv' (CoreDisks.positive_target d u)
  apply native_morse_positive_plane_limit d.chart (D.windows.smooth.of_le (by simp))
    D.windows.flow D.windows.integral (show 0 < 2 * d.radius by linarith [d.radius_pos])
      d.block (D.windows.model_germ p)
        (d.chart.splitChart.map_target' (CoreDisks.positive_target d u))
  · rw [hcoords]
    exact (CoreDisks.scaled_norm_le d u).trans_lt (by linarith [d.radius_pos])
  · rw [hcoords]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
