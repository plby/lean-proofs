import Wikipedia.SmoothSixDPoincare.SmoothFaceDescent
import Wikipedia.SmoothSixDPoincare.SmoothAttachingNeighborhood
import Wikipedia.SmoothSixDPoincare.OpenDiffeomorphPartial
import Wikipedia.SmoothSixDPoincare.NativeHandleFaceCoordinates
import Wikipedia.SmoothSixDPoincare.FramedSurgeryBodyAttachment

/-!
# The original native attaching face as a framed whole-body face

Its full smooth chart comes from the original Morse coordinates. The
attaching map into the old body is exactly the already recorded native
face map, with no change of whole-handle coordinates.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] {f : M → ℝ} {p : M}
  (d : MorseSurgeryData E f p)
  (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (m : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]

open Classical in
def attachingSmoothFace : d.LowerSmoothFace hf (𝓡 m)
    (PuncturedHandle.UnitSphere d.chart.NegativeCoordinates) d.chart.PositiveCoordinates := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let u₀ := SphereCoordinates.standardParametrization d.chart.NegativeCoordinates m
    (Hemisphere.point true ⟨0, by simp⟩)
  let x₀ := d.chart.closedAttachingPoint d.radius d.radius_pos d.block u₀ ⟨0, by simp⟩
  let N := d.chart.attachingNeighborhoodDiffeomorph hf m d.radius d.radius_pos d.lower_regular
  let P := OpenDiffeomorph.partialDiffeomorph N x₀
  exact {
    map := d.attachingFace
    closedEmbedding := d.attachingFace.continuous.isClosedEmbedding d.attachingFace_injective
    chart := P
    source := fun z hz =>
      (d.chart.closedAttachingPoint d.radius d.radius_pos d.block z.1 ⟨z.2, hz.2⟩).property
    point := fun u v => by
      apply Subtype.ext
      exact (congrArg (fun y : d.LowerLevel => y.val)
        (OpenDiffeomorph.partialDiffeomorph_apply N x₀
          (d.chart.closedAttachingPoint d.radius d.radius_pos d.block u v))).trans
        (d.chart.attachingNeighborhoodDiffeomorph_face hf m d.radius d.radius_pos d.block
          d.lower_regular u v) }

open Classical in
theorem attachingSmoothFace_map :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    (d.attachingSmoothFace hf m).map = d.attachingFace := rfl

def lowerBodyInclusion : C(d.LowerLevel, {x : M // f x ≤ f p - d.radius ^ 2}) :=
  ⟨fun x => ⟨x.val, x.property.le⟩, continuous_subtype_val.subtype_mk _⟩

include hf in
omit [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] in
theorem lowerBodyInclusion_isClosedEmbedding : IsClosedEmbedding d.lowerBodyInclusion :=
  ClosedCover.isClosedEmbedding_codRestrict
    (isClosed_eq hf.continuous continuous_const).isClosedEmbedding_subtypeVal
      (fun x => x.property.le)

open Classical in
theorem attachingSmoothFace_bodyFace :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.bodyFaceMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion =
      d.handleFaceToSublevel := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  ext z
  rfl

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
