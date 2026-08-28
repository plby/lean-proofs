import Wikipedia.SmoothSixDPoincare.NativeMorseAnnularCoordinates
import Wikipedia.SmoothSixDPoincare.NativeFramedExteriorOrbits

/-!
# The native annular formula for the corrected realization outside the open face

The full recorded model-orbit condition applies to each outer annular
point, including radius one. Its endpoint is exactly the original upper
belt-coordinate point, with the same original manifold coordinates.
-/

noncomputable section

open Set Function Topology Metric
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

open FramedSurgery MorseHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)

open Classical in
theorem annularLowerPoint_descentFlow
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates) :
    descentFlow (annularCrossingTime ‖z.2.val‖) (d.chart.splitChart (d.annularLowerPoint z).val) =
      annularUpperModel d.radius z.1.val z.2.val := by
  rw [d.annularLowerPoint_coordinates]
  exact descentFlow_annularCrossingTime d.radius (mem_sphere_zero_iff_norm.mp z.1.property)
    (surgeryAnnulus_ne_zero z.2)

open Classical in
theorem annularLowerPoint_flow_mem_block
    (z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates)
    {t : ℝ} (ht : t ∈ uIcc 0 (annularCrossingTime ‖z.2.val‖)) :
    descentFlow t (d.chart.splitChart (d.annularLowerPoint z).val) ∈
      closedBall (0 : d.chart.NegativeCoordinates) (2 * d.radius) ×ˢ
        closedBall (0 : d.chart.PositiveCoordinates) (2 * d.radius) := by
  rw [d.annularLowerPoint_coordinates]
  exact descentFlow_annular_mem_block d.radius_pos (mem_sphere_zero_iff_norm.mp z.1.property)
    (surgeryAnnulus_ne_zero z.2) z.2.property.2.le ht

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]

open Classical in
theorem beltFramedBoundaryRealization_annularOutside :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    ∀ z : AnnularParameters d.chart.NegativeCoordinates d.chart.PositiveCoordinates,
      1 ≤ ‖z.2.val‖ →
      d.beltFramedBoundaryRealization hf m n
        (oldMap (d.attachingSmoothFace hf m) n (d.annularOldPoint hf m z)) =
        d.annularUpperPoint z := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  intro z hz
  let r : Exterior (d.attachingSmoothFace hf m) :=
    ⟨d.annularLowerPoint z, fun h => (not_lt.mpr hz)
      ((d.annularLowerPoint_mem_faceInterior_iff hf m z).mp h)⟩
  have hsource : r.val.val ∈ d.chart.splitChart.source :=
    (d.chart.attachingNeighborhoodHomeomorph d.radius d.radius_pos
      (d.annularAttachingPoint z)).property
  have hend : d.chart.splitChart.symm
      (descentFlow (annularCrossingTime ‖z.2.val‖) (d.chart.splitChart r.val.val)) =
      (d.annularUpperPoint z).val :=
    (congrArg d.chart.splitChart.symm (d.annularLowerPoint_descentFlow z)).trans
      (d.annularUpperPoint_model z).symm
  have hlevel : f (d.chart.splitChart.symm
      (descentFlow (annularCrossingTime ‖z.2.val‖) (d.chart.splitChart r.val.val))) =
      f p + d.radius ^ 2 :=
    (congrArg f hend).trans (d.annularUpperPoint z).property
  have horbit := d.beltFramedBoundaryRealization_exterior_model hf m n r hsource
    (annularCrossingTime ‖z.2.val‖) (annularCrossingTime_nonpos (surgeryAnnulus_norm_pos z.2))
    (fun _ ht => d.annularLowerPoint_flow_mem_block z ht) hlevel
  exact Subtype.ext (horbit.trans hend)

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
