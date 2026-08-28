import Wikipedia.SmoothSixDPoincare.NativeSmoothFramedRealization
import Wikipedia.SmoothSixDPoincare.ShrunkExteriorSmoothness
import Wikipedia.SmoothSixDPoincare.ShrunkUpperBodyChange

/-!
# Carry the smooth native boundary realization through the retained shrinking

The original shrinking's whole-body change and its recorded ambient
boundary diffeomorphism commute on the actual upper level. Composing
this record with the corrected native realization retains the exact
whole-body map; smoothness is asserted only for its boundary restriction.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
namespace ShrunkSurgeryRealization.AmbientExtension

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} {R : d.ShrunkSurgeryRealization s}
  (H : R.AmbientExtension) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)

def upperBodySmoothChange :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      d.upperBodyInclusion d.upperBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  exact {
    body := R.upperBodyChange
    boundary := H.boundaryDiffeomorph hf
    boundary_point := fun y => Subtype.ext (R.upperBodyChange_on_level y) }

theorem upperBodySmoothChange_body :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (H.upperBodySmoothChange hf).body = R.upperBodyChange := rfl

theorem upperBodySmoothChange_boundary :
    letI := RegularLevel.chartedSpace hf d.upper_regular
    (H.upperBodySmoothChange hf).boundary.toHomeomorph = R.boundaryHomeomorph := rfl

variable [T2Space M] [CompactSpace M] (m n : ℕ)
  [Fact (Module.finrank ℝ d.chart.NegativeCoordinates = m + 1)]
  [Fact (Module.finrank ℝ d.chart.PositiveCoordinates = n + 1)]
  (P : letI := RegularLevel.chartedSpace hf d.lower_regular
    FramedSurgery.SmoothBoundaryData (d.attachingSmoothFace hf m) n)
  (hd : d.HasSmoothExterior hf)

open Classical in
def beltFramedSmoothRealization :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    SmoothBoundaryBodyEquiv (J := 𝓘(ℝ, RegularLevel.Model E))
      (FramedSurgery.boundaryBodyMap (d.attachingSmoothFace hf m) d.lowerBodyInclusion n
        (d.lowerBodyInclusion_isClosedEmbedding hf)) d.upperBodyInclusion := by
  let _ := RegularLevel.chartedSpace hf d.lower_regular
  let _ := RegularLevel.chartedSpace hf d.upper_regular
  let _ : CompactSpace d.LowerLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
    isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
  let _ := P.charted
  exact (d.beltFramedSmoothRealization hf m n P hd).trans (H.upperBodySmoothChange hf)

open Classical in
theorem beltFramedSmoothRealization_body :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (H.beltFramedSmoothRealization hf m n P hd).body =
      (d.beltFramedBodyRealization hf m).trans R.upperBodyChange := rfl

open Classical in
theorem beltFramedSmoothRealization_boundary :
    letI := RegularLevel.chartedSpace hf d.lower_regular
    letI := RegularLevel.chartedSpace hf d.upper_regular
    letI : CompactSpace d.LowerLevel :=
      isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
    letI : CompactSpace {x : M // f x ≤ f p - d.radius ^ 2} :=
      isCompact_iff_compactSpace.mp (isClosed_le hf.continuous continuous_const).isCompact
    letI := P.charted
    (H.beltFramedSmoothRealization hf m n P hd).boundary.toHomeomorph =
      (d.beltFramedBoundaryRealization hf m n).trans R.boundaryHomeomorph := rfl

end ShrunkSurgeryRealization.AmbientExtension
end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData
