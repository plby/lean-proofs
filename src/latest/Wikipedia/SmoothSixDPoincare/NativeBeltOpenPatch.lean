import Wikipedia.SmoothSixDPoincare.NativeBeltFramedRealization
import Wikipedia.SmoothSixDPoincare.SmoothBeltNeighborhood
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphIntoOpen

/-!
# The full native open belt patch with its original point coordinates

Open-disk inclusion, product exchange, and the original native belt
neighborhood compose to a full-source partial diffeomorphism. Its point
map is the same belt-coordinate map used by the corrected realization.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open PuncturedHandle FramedSurgery

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (n : ℕ) [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
private def beltPatchBasePoint : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates :=
  (⟨0, by simp [openUnitDisk]⟩,
    SphereCoordinates.standardParametrization d.chart.PositiveCoordinates n
      (Hemisphere.point true ⟨0, by simp⟩))

open Classical in
def beltRawPatchPartial :
    PartialDiffeomorph (𝓘(ℝ, d.chart.NegativeCoordinates).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
      (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (UnitSphere d.chart.PositiveCoordinates × d.chart.NegativeCoordinates) ∞ := by
  let _ : Nonempty (openUnitDisk d.chart.NegativeCoordinates) := ⟨⟨0, by simp [openUnitDisk]⟩⟩
  exact (PartialChart.prod (PartialChart.openInclusion (openUnitDisk d.chart.NegativeCoordinates))
    (Diffeomorph.refl (𝓡 n) (UnitSphere d.chart.PositiveCoordinates) ∞).toPartialDiffeomorph).trans
    (Diffeomorph.prodComm 𝓘(ℝ, d.chart.NegativeCoordinates) (𝓡 n)
      d.chart.NegativeCoordinates (UnitSphere d.chart.PositiveCoordinates) ∞).toPartialDiffeomorph

open Classical in
theorem beltRawPatchPartial_source : (d.beltRawPatchPartial n).source = univ := by
  apply eq_univ_of_forall
  intro y
  exact ⟨⟨mem_univ y.1, mem_univ y.2⟩, mem_univ _⟩

open Classical in
theorem beltRawPatchPartial_point
    (y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.beltRawPatchPartial n y = (y.2, y.1.val) := rfl

open Classical in
theorem beltRawPatchPartial_mem
    (y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    d.beltRawPatchPartial n y ∈ d.chart.beltSource d.radius d.radius_pos := by
  rw [d.beltRawPatchPartial_point]
  exact d.chart.enlarged_closed_belt_subset_source d.radius d.radius_pos d.block
    ⟨mem_univ _, mem_closedBall_zero_iff.mpr
      ((mem_ball_zero_iff.mp y.1.property).le.trans (by norm_num))⟩

open Classical in
def beltSourcePartial :
    PartialDiffeomorph (𝓘(ℝ, d.chart.NegativeCoordinates).prod (𝓡 n))
      ((𝓡 n).prod 𝓘(ℝ, d.chart.NegativeCoordinates))
      (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
      (d.chart.beltSource d.radius d.radius_pos) ∞ := by
  let _ : Nonempty (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :=
    ⟨beltPatchBasePoint d n⟩
  exact PartialChart.intoOpen (d.beltRawPatchPartial n)
    (d.chart.beltSource d.radius d.radius_pos) (d.beltRawPatchPartial_mem n)

open Classical in
theorem beltSourcePartial_source : (d.beltSourcePartial n).source = univ := by
  let _ : Nonempty (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :=
    ⟨beltPatchBasePoint d n⟩
  exact PartialChart.intoOpen_source (d.beltRawPatchPartial n)
    (d.chart.beltSource d.radius d.radius_pos) (d.beltRawPatchPartial_mem n)
      (d.beltRawPatchPartial_source n)

open Classical in
theorem beltSourcePartial_point
    (y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    (d.beltSourcePartial n y).val = (y.2, y.1.val) := by
  let _ : Nonempty (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :=
    ⟨beltPatchBasePoint d n⟩
  exact (PartialChart.intoOpen_apply (d.beltRawPatchPartial n)
    (d.chart.beltSource d.radius d.radius_pos) (d.beltRawPatchPartial_mem n) y).trans
      (d.beltRawPatchPartial_point n y)

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

open Classical in
def beltOpenPartial :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    PartialDiffeomorph (𝓘(ℝ, d.chart.NegativeCoordinates).prod (𝓡 n))
      𝓘(ℝ, RegularLevel.Model E)
      (NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) d.UpperLevel ∞ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : Nonempty (d.chart.beltTarget d.radius) :=
    ⟨d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
      (d.beltSourcePartial n (beltPatchBasePoint d n))⟩
  exact ((d.beltSourcePartial n).trans
    (d.chart.beltNeighborhoodDiffeomorph hf n d.radius d.radius_pos
      d.upper_regular).toPartialDiffeomorph).trans
    (PartialChart.openInclusion (d.chart.beltTarget d.radius))

open Classical in
theorem beltOpenPartial_source :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (d.beltOpenPartial n hf).source = univ := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  apply eq_univ_of_forall
  intro y
  refine ⟨⟨?_, mem_univ _⟩, mem_univ _⟩
  change y ∈ (d.beltSourcePartial n).source
  rw [d.beltSourcePartial_source]
  trivial

open Classical in
theorem beltOpenPartial_point
    (y : NewPatch d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    d.beltOpenPartial n hf y =
      d.beltClosedDiskMap (⟨y.1.val, (mem_ball_zero_iff.mp y.1.property).le⟩, y.2) := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  change (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos
    (d.beltSourcePartial n y)).val = _
  apply congrArg (fun z : d.chart.beltSource d.radius d.radius_pos =>
    (d.chart.beltNeighborhoodHomeomorph d.radius d.radius_pos z).val)
  exact Subtype.ext (d.beltSourcePartial_point n y)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
