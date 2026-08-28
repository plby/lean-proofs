import Wikipedia.SmoothSixDPoincare.MorseSurgeryBeltCoordinates
import Wikipedia.SmoothSixDPoincare.BeltTubeCoordinates

/-!
# The intrinsic small belt tube is the native closed normal disk

The exact whole-new-piece calculation identifies every normal radius below
one with the existing surgery tube, retaining all original coordinates.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem beltClosedDiskPoint_mem_surgerySource
    (u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) (hu : ‖u.val‖ < 1) :
    (v, u.val) ∈ d.beltSurgerySource := by
  apply (d.mem_beltSurgerySource_iff _).mpr
  refine ⟨(d.beltClosedDiskPoint (u, v)).property, ?_⟩
  exact (d.beltClosedDiskMap_mem_newInterior_iff (u, v)).mpr hu

open Classical in
/-- Every closed normal disk of radius below one fits in the original new-piece interior. -/
theorem small_closed_belt_subset_surgerySource {a : ℝ} (ha : a < 1) :
    (univ : Set (PuncturedHandle.UnitSphere d.chart.PositiveCoordinates)) ×ˢ
      closedBall (0 : d.chart.NegativeCoordinates) a ⊆ d.beltSurgerySource := by
  rintro ⟨v, u⟩ ⟨_, hu⟩
  have hn : ‖u‖ < 1 := (mem_closedBall_zero_iff.mp hu).trans_lt ha
  exact d.beltClosedDiskPoint_mem_surgerySource ⟨u, hn.le⟩ v hn

open Classical in
/-- Equality with the intrinsic tube, not just inclusion in a chart neighborhood. -/
theorem closedBeltTube_eq_beltClosedDiskMap_image {a : ℝ} (ha : a < 1) :
    d.closedBeltTube a = d.beltClosedDiskMap ''
      {z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
        PuncturedHandle.UnitSphere d.chart.PositiveCoordinates | ‖z.1.val‖ ≤ a} := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hzy⟩ := (d.mem_closedBeltTube_iff_exists a y).mp hy
    let u : PuncturedHandle.UnitBall d.chart.NegativeCoordinates :=
      ⟨z.val.2, hz.trans ha.le⟩
    refine ⟨(u, z.val.1), hz, ?_⟩
    exact hzy
  · rintro ⟨⟨u, v⟩, hu, rfl⟩
    let z : d.beltSurgerySource :=
      ⟨(v, u.val), d.beltClosedDiskPoint_mem_surgerySource u v (hu.trans_lt ha)⟩
    have hpoint : (d.beltSurgeryHomeomorph z).val = d.beltClosedDiskMap (u, v) := rfl
    rw [← hpoint]
    exact (d.beltSurgeryHomeomorph_mem_closedBeltTube_iff a z).mpr hu

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
