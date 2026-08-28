import Wikipedia.SmoothSixDPoincare.MorseOnePointCollapse
import Wikipedia.SmoothSixDPoincare.MorseSurgeryBeltCoordinates
import Wikipedia.SmoothSixDPoincare.MorseBeltNormalCoordinates
import Wikipedia.SmoothSixDPoincare.BeltCollapseCoordinates

/-!
# The actual whole-attachment collapse in the original normal coordinates

The finite coordinate on the entire new interior is the explicit radial
coordinate of the negative Morse projection. In particular this is the
local representative of the global collapse at every actual belt point.
-/

noncomputable section

open Set Metric Function Topology
open scoped OnePoint

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem beltNormal_beltClosedDiskMap
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltNormal (d.beltClosedDiskMap z) = d.radius • z.1.val :=
  d.chart.beltNeighborhoodHomeomorph_normal d.radius d.radius_pos (d.beltClosedDiskPoint z)

open Classical in
theorem beltClosedDiskMap_mem_normalDomain
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.beltClosedDiskMap z ∈ d.beltNormalDomain :=
  (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos (d.beltClosedDiskPoint z)).property

open Classical in
theorem newInterior_subset_normalDomain : d.surgery.NewInterior ⊆ d.beltNormalDomain := by
  intro x hx
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  exact d.beltClosedDiskMap_mem_normalDomain z

open Classical in
theorem norm_scaled_beltNormal_lt_one {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    ‖d.radius⁻¹ • d.beltNormal x‖ < 1 := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  rw [d.beltNormal_beltClosedDiskMap, smul_smul,
    inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  exact (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx

open Classical in
/-- The finite representative in the original, unscaled negative Morse coordinate. -/
def collapseNormal (x : d.UpperLevel) : d.chart.NegativeCoordinates :=
  MorseHandle.beltCollapseCoordinate (d.radius⁻¹ • d.beltNormal x)

open Classical in
theorem collapseNormal_belt (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.collapseNormal (d.surgery.beltSphere v) = 0 := by
  rw [collapseNormal, d.beltNormal_belt, smul_zero, MorseHandle.beltCollapseCoordinate_zero]

variable [T2Space M]

open Classical in
theorem levelCollapse_beltClosedDiskMap (hf : Continuous f)
    (z : PuncturedHandle.UnitBall d.chart.NegativeCoordinates ×
      PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    d.levelCollapseMap hf (d.beltClosedDiskMap z) =
      DiskOnePointCollapse.collapse (MorseHandle.beltFaceDiskMap
        (MorseHandle.unitBallHomeomorph d.chart.NegativeCoordinates z.1)) := by
  rw [← d.newPiece_beltFaceCoordinates z.1 z.2, d.levelCollapse_newPiece]
  rfl

open Classical in
/-- Equality on the whole new interior, not just on the belt zero section. -/
theorem levelCollapse_eq_coe_collapseNormal (hf : Continuous f)
    {x : d.UpperLevel} (hx : x ∈ d.surgery.NewInterior) :
    d.levelCollapseMap hf x = (d.collapseNormal x : OnePoint d.chart.NegativeCoordinates) := by
  have hr := d.surgery.newInterior_subset_range hx
  rw [d.range_newPiece_eq_range_beltClosedDiskMap] at hr
  obtain ⟨z, rfl⟩ := hr
  have hz := (d.beltClosedDiskMap_mem_newInterior_iff z).mp hx
  rw [d.levelCollapse_beltClosedDiskMap, DiskOnePointCollapse.collapse_interior _
    ((MorseHandle.norm_beltFaceMap_lt_one_iff z.1.val).mpr hz)]
  unfold collapseNormal
  rw [d.beltNormal_beltClosedDiskMap, smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul]
  rfl

open Classical in
/-- This finite representative is a germ of the original global collapse at each belt point. -/
theorem levelCollapse_eventuallyEq_belt (hf : Continuous f)
    (v : PuncturedHandle.UnitSphere d.chart.PositiveCoordinates) :
    (d.levelCollapseMap hf : d.UpperLevel → OnePoint d.chart.NegativeCoordinates) =ᶠ[
      𝓝 (d.surgery.beltSphere v)] (fun x => (d.collapseNormal x : OnePoint _)) := by
  filter_upwards [d.surgery.isOpen_newInterior.mem_nhds
    (d.surgery.beltSphere_mem_newInterior v)] with x hx
  exact d.levelCollapse_eq_coe_collapseNormal hf hx

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
